#!/usr/bin/env python3
"""Exact diagnostics for the largest-coordinate volume dynamic program.

This script compares two distinct recurrences for interval-constrained orders:

1. Integer polynomial integration over the largest coordinate, O(b^3 2^b).
2. A Fraction-valued segment-assignment table, with an independently computed
   linear-extension count for each subset, O(poly(b) 3^b).

All comparisons are exact.  The checks are implementation diagnostics, not a
proof of the sorting adversary or its asymptotic claims.  No third-party package
is required.  Run `python3 check_local_volume.py`; the JSON report is written
beside this script unless --output specifies another path.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
import json
from math import comb, factorial, lcm
from pathlib import Path
import random


SEED = 817
CASES_PER_SIZE = 90


def predecessors(n: int, edges: list[tuple[int, int]]) -> list[int]:
    """Compute the strict transitive predecessor relation as bit masks."""
    pred = [0] * n
    for source, target in edges:
        if not (0 <= source < n and 0 <= target < n):
            raise ValueError("An edge endpoint is outside the vertex set.")
        pred[target] |= 1 << source
    for middle in range(n):
        for target in range(n):
            if pred[target] & (1 << middle):
                pred[target] |= pred[middle]
    return pred


def is_cyclic(pred: list[int]) -> bool:
    return any(mask & (1 << v) for v, mask in enumerate(pred))


def normalize_intervals(intervals):
    return [(Fraction(left), Fraction(right)) for left, right in intervals]


def largest_coordinate_volume(intervals, edges) -> Fraction:
    """Exact integer DP using F'_S = sum_{v maximal and active} F_(S-v)."""
    intervals = normalize_intervals(intervals)
    n = len(intervals)
    if n == 0:
        return Fraction(1)
    if any(left >= right for left, right in intervals):
        return Fraction(0)

    outgoing = [0] * n
    for source, target in edges:
        if not (0 <= source < n and 0 <= target < n):
            raise ValueError("An edge endpoint is outside the vertex set.")
        outgoing[source] |= 1 << target

    # A common rational scaling makes every segment length an integer.  For
    # the manuscript's dyadic inputs this common denominator is a power of 2.
    scale = lcm(*(endpoint.denominator for interval in intervals for endpoint in interval))
    integral_intervals = [
        (int(left * scale), int(right * scale)) for left, right in intervals
    ]
    endpoints = sorted({endpoint for interval in integral_intervals for endpoint in interval})

    # Every subset has its own induced-graph volume.  The recurrence needs
    # only direct outgoing edges and never computes transitive closure.
    subsets = sorted(range(1 << n), key=int.bit_count)
    maximal = {
        subset: [
            v
            for v in range(n)
            if subset & (1 << v)
            and not outgoing[v] & subset
        ]
        for subset in subsets
    }

    # Q[S] = |S|! times the partial volume at the segment's left endpoint.
    values = {subset: 0 for subset in subsets}
    values[0] = 1
    for left, right in zip(endpoints, endpoints[1:]):
        active = {
            v
            for v, (lower, upper) in enumerate(integral_intervals)
            if lower <= left and right <= upper
        }
        coefficients = {}
        for subset in subsets:
            size = subset.bit_count()
            coefficients[subset] = [values[subset]]
            for power in range(1, size + 1):
                coefficients[subset].append(
                    sum(
                        coefficients[subset ^ (1 << v)][power - 1]
                        for v in maximal[subset]
                        if v in active
                    )
                )
        length = right - left
        values = {
            subset: sum(
                comb(subset.bit_count(), power) * coefficient * length**power
                for power, coefficient in enumerate(coefficients[subset])
            )
            for subset in subsets
        }

    return Fraction(values[(1 << n) - 1], factorial(n) * scale**n)


def segment_assignment_volume(intervals, edges) -> Fraction:
    """Independent exact reference recurrence, using subsets per segment."""
    intervals = normalize_intervals(intervals)
    n = len(intervals)
    if n == 0:
        return Fraction(1)
    if any(left >= right for left, right in intervals):
        return Fraction(0)

    pred = predecessors(n, edges)
    if is_cyclic(pred):
        return Fraction(0)
    ideals = [
        subset
        for subset in range(1 << n)
        if all(
            not subset & (1 << v) or pred[v] & subset == pred[v]
            for v in range(n)
        )
    ]

    @lru_cache(maxsize=None)
    def extension_count(subset: int) -> int:
        if subset == 0:
            return 1
        return sum(
            extension_count(subset ^ (1 << v))
            for v in range(n)
            if subset & (1 << v) and not pred[v] & subset
        )

    endpoints = sorted({endpoint for interval in intervals for endpoint in interval})
    values = {subset: Fraction(0) for subset in ideals}
    values[0] = Fraction(1)
    for left, right in zip(endpoints, endpoints[1:]):
        updated = {subset: Fraction(0) for subset in ideals}
        length = right - left
        for previous in ideals:
            if not values[previous]:
                continue
            for following in ideals:
                if previous & following != previous:
                    continue
                newly_assigned = following ^ previous
                if any(
                    newly_assigned & (1 << v)
                    and not (lower <= left and right <= upper)
                    for v, (lower, upper) in enumerate(intervals)
                ):
                    continue
                count = newly_assigned.bit_count()
                updated[following] += (
                    values[previous]
                    * extension_count(newly_assigned)
                    * length**count
                    / factorial(count)
                )
        values = updated
    return values[(1 << n) - 1]


def rational_string(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def check_equal(name, actual, expected, report):
    actual, expected = Fraction(actual), Fraction(expected)
    if actual != expected:
        raise AssertionError(f"{name}: {actual} != {expected}")
    report.append({"case": name, "actual": rational_string(actual), "expected": rational_string(expected), "passed": True})


def run_checks():
    analytic = []
    for size in range(1, 8):
        intervals = [(0, 3)] * size
        check_equal(
            f"independent_{size}_coordinates_in_0_3",
            largest_coordinate_volume(intervals, []),
            3**size,
            analytic,
        )
        check_equal(
            f"chain_{size}_coordinates_in_0_3",
            largest_coordinate_volume(intervals, [(v, v + 1) for v in range(size - 1)]),
            Fraction(3**size, factorial(size)),
            analytic,
        )

    check_equal("empty_coordinate_set", largest_coordinate_volume([], []), 1, analytic)
    check_equal("directed_cycle", largest_coordinate_volume([(0, 1), (0, 1)], [(0, 1), (1, 0)]), 0, analytic)
    check_equal("infeasible_intervals", largest_coordinate_volume([(2, 3), (0, 1)], [(0, 1)]), 0, analytic)
    check_equal("unequal_independent_box", largest_coordinate_volume([(0, 2), (0, 3)], []), 6, analytic)
    check_equal("triangle_area", largest_coordinate_volume([(0, 2), (0, 2)], [(0, 1)]), 2, analytic)

    box = largest_coordinate_volume([(0, 1), (0, 2)], [])
    ordered = largest_coordinate_volume([(0, 1), (0, 2)], [(0, 1)])
    check_equal("Pr_A_less_B_uniform_0_1_and_0_2", ordered / box, Fraction(3, 4), analytic)

    # Parent: 0 < X_A < X_B < 2, area 2.  Its A-section at c has
    # length 2-c, hence f_A(c)=(2-c)/2.  The child already has two
    # coordinates from admissions 1 and 2; an isolated third arrival
    # has interval (0,3), so its child volume multiplies by exactly 3.
    parent_volume = largest_coordinate_volume([(0, 2), (0, 2)], [(0, 1)])
    old_child = largest_coordinate_volume([(0, 1), (0, 2)], [(0, 1)])
    new_child = largest_coordinate_volume([(0, 1), (0, 2), (0, 3)], [(0, 1)])
    check_equal("third_child_admission_gain", new_child / old_child, 3, analytic)
    for position in [Fraction(1, 2), Fraction(1), Fraction(3, 2)]:
        section = largest_coordinate_volume([(position, 2)], [])
        density = section / parent_volume
        check_equal(
            f"triangle_density_at_{rational_string(position)}",
            density,
            (2 - position) / 2,
            analytic,
        )
        check_equal(
            f"promotion_ratio_at_{rational_string(position)}",
            section * new_child / (parent_volume * old_child),
            3 * density,
            analytic,
        )

    rng = random.Random(SEED)
    by_size = []
    for size in range(1, 8):
        positive = zero = 0
        for case in range(CASES_PER_SIZE):
            order = list(range(size))
            rng.shuffle(order)
            edges = [
                (order[first], order[second])
                for first in range(size)
                for second in range(first + 1, size)
                if rng.random() < 0.3
            ]
            common_scale = 2 ** rng.randrange(4)
            intervals = []
            for _ in range(size):
                left, right = sorted(rng.sample(range(9), 2))
                scale = 1 if case % 3 == 0 else common_scale if case % 3 == 1 else 2 ** rng.randrange(4)
                intervals.append((Fraction(left, scale), Fraction(right, scale)))
            actual = largest_coordinate_volume(intervals, edges)
            expected = segment_assignment_volume(intervals, edges)
            if actual != expected:
                raise AssertionError(
                    f"Random mismatch: size={size}, case={case}, intervals={intervals}, "
                    f"edges={edges}, actual={actual}, expected={expected}"
                )
            if actual:
                positive += 1
            else:
                zero += 1
        by_size.append({"vertices": size, "cases": CASES_PER_SIZE, "positive_volume": positive, "zero_volume": zero, "all_exactly_equal": True})

    return {
        "status": "passed",
        "scope": "Exact diagnostics of the local volume recurrence and elementary identities only; not a verification of all adversary trajectories or the asymptotic theorem.",
        "arithmetic": "Python integers and fractions.Fraction; no floating-point comparisons",
        "seed": SEED,
        "random_case_total": 7 * CASES_PER_SIZE,
        "random_case_design": "Random acyclic orientations of a random vertex ordering, edge probability 0.3; integer, common-dyadic, and mixed-dyadic intervals, including infeasible systems.",
        "random_cases_by_size": by_size,
        "analytic_case_total": len(analytic),
        "analytic_cases": analytic,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()
    report = run_checks()
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "random_cases": report["random_case_total"], "analytic_cases": report["analytic_case_total"], "report": str(args.output.resolve())}))


if __name__ == "__main__":
    main()
