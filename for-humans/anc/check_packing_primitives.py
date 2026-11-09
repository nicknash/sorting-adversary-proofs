#!/usr/bin/env python3
"""Exact diagnostics for endpoint-interleaving volume and midpoint refinement.

Two independent reference volume calculations are compared: permutation/gap
enumeration and an integer subset-polynomial recurrence. These provide exact
reference probabilities for checking the geometric anchor rules.  Midpoint
search is then checked using exact reference CDFs with pointwise perturbations
of at most 1/32, including alternating signs.  All arithmetic uses integers and
fractions.Fraction.  This is a small diagnostic, not a proof or a simulation of
all sorting-adversary trajectories.  No nonstandard dependency is required.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement, permutations
import json
from math import comb, factorial, lcm, prod
from pathlib import Path
import random


SEED = 1108
CASES_PER_SIZE = 8
ERROR = Fraction(1, 32)


def interval_fractions(intervals):
    return [(Fraction(a), Fraction(b)) for a, b in intervals]


def subset_volume(intervals, edges):
    """Previously checked exact integer DP, used as the independent reference."""
    intervals = interval_fractions(intervals)
    n = len(intervals)
    if not n:
        return Fraction(1)
    if any(a >= b for a, b in intervals):
        return Fraction(0)
    outgoing = [0] * n
    for u, v in edges:
        outgoing[u] |= 1 << v
    scale = lcm(*(x.denominator for ab in intervals for x in ab))
    scaled = [(int(a * scale), int(b * scale)) for a, b in intervals]
    endpoints = sorted({x for ab in scaled for x in ab})
    subsets = sorted(range(1 << n), key=int.bit_count)
    sinks = {
        s: [v for v in range(n) if s & (1 << v) and not outgoing[v] & s]
        for s in subsets
    }
    values = {s: 0 for s in subsets}
    values[0] = 1
    for left, right in zip(endpoints, endpoints[1:]):
        active = {v for v, (a, b) in enumerate(scaled) if a <= left and right <= b}
        coefficients = {}
        for s in subsets:
            r = s.bit_count()
            coefficients[s] = [values[s]]
            for k in range(1, r + 1):
                coefficients[s].append(sum(
                    coefficients[s ^ (1 << v)][k - 1]
                    for v in sinks[s] if v in active
                ))
        delta = right - left
        values = {
            s: sum(comb(s.bit_count(), k) * c * delta**k
                   for k, c in enumerate(coefficients[s]))
            for s in subsets
        }
    return Fraction(values[(1 << n) - 1], factorial(n) * scale**n)


def interleaving_volume(intervals, edges):
    """New enumeration: compatible coordinate orders and ordered gap choices."""
    intervals = interval_fractions(intervals)
    n = len(intervals)
    if not n:
        return Fraction(1)
    if any(a >= b for a, b in intervals):
        return Fraction(0)
    scale = lcm(*(x.denominator for ab in intervals for x in ab))
    scaled = [(int(a * scale), int(b * scale)) for a, b in intervals]
    endpoints = sorted({x for ab in scaled for x in ab})
    gaps = list(zip(endpoints, endpoints[1:]))
    lengths = [right - left for left, right in gaps]
    allowed = [[a <= left and right <= b for left, right in gaps] for a, b in scaled]
    factorials = [factorial(r) for r in range(n + 1)]

    # These are the possible gaps of the first, second, ..., last coordinate.
    # Coordinates sharing a gap have the order prescribed by the permutation.
    assignments = []
    for chosen in combinations_with_replacement(range(len(gaps)), n):
        counts = Counter(chosen)
        factor = factorials[n] // prod(factorials[r] for r in counts.values())
        integer_term = factor * prod(lengths[j] ** r for j, r in counts.items())
        assignments.append((chosen, integer_term))

    numerator = 0
    for order in permutations(range(n)):
        rank = {x: i for i, x in enumerate(order)}
        if any(rank[u] >= rank[v] for u, v in edges):
            continue
        for chosen, term in assignments:
            if all(allowed[x][j] for x, j in zip(order, chosen)):
                numerator += term
    return Fraction(numerator, factorials[n] * scale**n)


def relations(n, edges):
    pred = [set() for _ in range(n)]
    for u, v in edges:
        pred[v].add(u)
    for middle in range(n):
        for target in range(n):
            if middle in pred[target]:
                pred[target].update(pred[middle])
    assert all(x not in pred[x] for x in range(n))
    succ = [{v for v in range(n) if u in pred[v]} for u in range(n)]
    return pred, succ


def effective_data(intervals, edges):
    pred, succ = relations(len(intervals), edges)
    supports = [
        (max(intervals[y][0] for y in pred[x] | {x}),
         min(intervals[y][1] for y in succ[x] | {x}))
        for x in range(len(intervals))
    ]
    return supports, [len(pred[x] | succ[x]) for x in range(len(intervals))]


def section_volume(intervals, edges, x, position):
    intervals = interval_fractions(intervals)
    position = Fraction(position)
    if not intervals[x][0] < position < intervals[x][1]:
        return Fraction(0)
    bounds = [list(ab) for ab in intervals]
    kept = [y for y in range(len(intervals)) if y != x]
    new_id = {y: i for i, y in enumerate(kept)}
    remaining_edges = []
    for u, v in edges:
        if u == x:
            bounds[v][0] = max(bounds[v][0], position)
        elif v == x:
            bounds[u][1] = min(bounds[u][1], position)
        else:
            remaining_edges.append((new_id[u], new_id[v]))
    return subset_volume([tuple(bounds[y]) for y in kept], remaining_edges)


def exact_cdf(intervals, edges, x, threshold, full_volume):
    a, b = intervals[x]
    if threshold <= a:
        return Fraction(0)
    if threshold >= b:
        return Fraction(1)
    truncated = list(intervals)
    truncated[x] = (a, threshold)
    return subset_volume(truncated, edges) / full_volume


def ceil_log2_positive(value):
    value = Fraction(value)
    assert value >= 1
    exponent = max(0, value.numerator.bit_length() - value.denominator.bit_length())
    while Fraction(1 << exponent) < value:
        exponent += 1
    while exponent > 0 and Fraction(1 << (exponent - 1)) >= value:
        exponent -= 1
    return exponent


def check_midpoint_search(intervals, edges, x, full_volume, support, comparable, noise_pattern):
    left, right = Fraction(0), Fraction(1)
    left_cdf, right_cdf = Fraction(0), Fraction(1)
    ell, upper = support
    width = upper - ell
    cap = ceil_log2_positive(Fraction(4 * (comparable + 1)) / width) + 1
    accepted = None
    for m in range(cap):
        assert right - left == Fraction(1, 2**m)
        assert left_cdf < Fraction(9, 32)
        assert right_cdf > Fraction(23, 32)
        assert right_cdf - left_cdf >= Fraction(7, 16)
        midpoint = (left + right) / 2
        value = exact_cdf(intervals, edges, x, midpoint, full_volume)
        if noise_pattern == "exact":
            perturbation = Fraction(0)
        else:
            first_sign = 1 if noise_pattern == "alternating_plus" else -1
            perturbation = first_sign * (1 if m % 2 == 0 else -1) * ERROR
        reported = min(Fraction(1), max(Fraction(0), value + perturbation))
        assert abs(reported - value) <= ERROR
        if reported < Fraction(1, 4):
            left, left_cdf = midpoint, value
        elif reported > Fraction(3, 4):
            right, right_cdf = midpoint, value
        else:
            density = section_volume(intervals, edges, x, midpoint) / full_volume
            cell_width = right - left
            certificate = min(value, 1 - value) * (right_cdf - left_cdf)
            assert cell_width * density >= certificate
            assert 16 * cell_width * density >= 1
            assert ell < midpoint < upper
            assert Fraction(7, 32) <= value <= Fraction(25, 32)
            assert midpoint.denominator == 2 ** (m + 1)
            accepted = {
                "tests": m + 1,
                "address_length": m,
                "density_tariff_ratio": 16 * cell_width * density,
            }
            break
    if accepted is None:
        raise AssertionError(f"Midpoint search failed to terminate within {cap} tests")
    return accepted


def check_narrow_selection(intervals, edges, x, full_volume, support, comparable):
    ell, upper = support
    width = upper - ell
    m, cell_width = 0, Fraction(1)
    while cell_width > width / 4:
        m += 1
        cell_width /= 2
    assert width / 8 < cell_width <= width / 4
    center = (ell + upper) / 2
    cell_index = center // cell_width
    position = (Fraction(cell_index) + Fraction(1, 2)) * cell_width
    assert abs(position - center) <= cell_width / 2
    assert ell + width / 4 <= position <= upper - width / 4
    density = section_volume(intervals, edges, x, position) / full_volume
    assert 16 * cell_width * 2 ** (2 * comparable) * density >= 1
    assert position.denominator == 2 ** (m + 1)


def run_checks():
    explicit = [
        ("empty_region_coordinates", [], [], Fraction(1)),
        ("unit_interval", [(0, 1)], [], Fraction(1)),
        ("unit_square", [(0, 1), (0, 1)], [], Fraction(1)),
        ("root_triangle", [(0, 1), (0, 1)], [(0, 1)], Fraction(1, 2)),
        ("five_element_chain", [(0, 1)] * 5, [(0, 1), (1, 2), (2, 3), (3, 4)], Fraction(1, 120)),
        ("clipped_fork", [(Fraction(1, 4), Fraction(3, 4)), (0, 1),
                           (Fraction(3, 8), 1), (Fraction(1, 8), Fraction(7, 8))],
                          [(0, 1), (0, 2), (0, 3)], Fraction(2849, 49152)),
        ("incomparable_attachments", [(Fraction(1, 4), Fraction(3, 4)),
                                      (0, Fraction(5, 8)), (Fraction(3, 8), 1),
                                      (Fraction(1, 8), Fraction(7, 8)),
                                      (Fraction(1, 8), Fraction(7, 8))],
                                     [(1, 0), (0, 2), (3, 2), (1, 4)], Fraction(10127, 245760)),
        ("isolated_narrow", [(Fraction(1, 2), Fraction(1, 2) + Fraction(1, 2**20))], [], Fraction(1, 2**20)),
        ("disconnected_narrow", [(0, 1), (0, 1),
                                  (Fraction(1, 2), Fraction(257, 512)),
                                  (Fraction(1, 8), Fraction(7, 8))], [(0, 1)], Fraction(3, 4096)),
        ("directed_cycle", [(0, 1), (0, 1)], [(0, 1), (1, 0)], Fraction(0)),
        ("infeasible_intervals", [(Fraction(3, 4), 1), (0, Fraction(1, 4))], [(0, 1)], Fraction(0)),
    ]
    rng = random.Random(SEED)
    systems = [(name, intervals, edges, expected, "explicit")
               for name, intervals, edges, expected in explicit]
    for n in range(1, 6):
        for case in range(CASES_PER_SIZE):
            order = list(range(n))
            rng.shuffle(order)
            edges = [(order[i], order[j]) for i in range(n) for j in range(i + 1, n)
                     if rng.random() < 0.3]
            if case < CASES_PER_SIZE // 2:
                intervals = [(Fraction(rng.randrange(4), 8), Fraction(rng.randrange(5, 9), 8))
                             for _ in range(n)]
            else:
                intervals = [tuple(Fraction(x, 8) for x in sorted(rng.sample(range(9), 2)))
                             for _ in range(n)]
            systems.append((f"seeded_n{n}_case{case}", intervals, edges, None, "seeded"))

    reports = []
    search_count = zero_address_count = narrow_count = 0
    max_tests = 0
    min_tariff_ratio = None
    positive_by_size = Counter()
    zero_by_size = Counter()
    for name, intervals, edges, expected, kind in systems:
        intervals = interval_fractions(intervals)
        calculated = interleaving_volume(intervals, edges)
        reference = subset_volume(intervals, edges)
        if calculated != reference:
            raise AssertionError(f"Volume mismatch in {name}: {calculated} != {reference}")
        if expected is not None and calculated != expected:
            raise AssertionError(f"Analytic mismatch in {name}: {calculated} != {expected}")
        n = len(intervals)
        (positive_by_size if calculated else zero_by_size)[n] += 1
        if calculated and n:
            supports, comparables = effective_data(intervals, edges)
            for x in range(n):
                for pattern in ["exact", "alternating_plus", "alternating_minus"]:
                    result = check_midpoint_search(intervals, edges, x, reference,
                                                   supports[x], comparables[x], pattern)
                    search_count += 1
                    zero_address_count += result["address_length"] == 0
                    max_tests = max(max_tests, result["tests"])
                    ratio = result["density_tariff_ratio"]
                    min_tariff_ratio = ratio if min_tariff_ratio is None else min(min_tariff_ratio, ratio)
                check_narrow_selection(intervals, edges, x, reference, supports[x], comparables[x])
                narrow_count += 1
        reports.append({"name": name, "kind": kind, "vertices": n, "edges": len(edges),
                        "volume": str(calculated), "passed": True})

    return {
        "status": "passed",
        "scope": "Small exact diagnostics of endpoint-interleaving volume, midpoint search with pointwise CDF error, and narrow-position rounding. Not a formal verification of locality or the asymptotic adversary, and not a simulation of all adversary trajectories.",
        "arithmetic": "Python integers and fractions.Fraction only",
        "seed": SEED,
        "volume_systems": len(systems),
        "seeded_systems": 5 * CASES_PER_SIZE,
        "explicit_systems": len(explicit),
        "volume_methods": ["coordinate permutations and ordered endpoint-gap assignments",
                           "independent previous integer subset-polynomial recurrence"],
        "positive_systems_by_size": dict(sorted(positive_by_size.items())),
        "zero_volume_systems_by_size": dict(sorted(zero_by_size.items())),
        "midpoint_searches": search_count,
        "midpoint_noise_patterns": ["exact", "+1/32,-1/32 alternating", "-1/32,+1/32 alternating"],
        "midpoint_noise_note": "Perturbed reports are clipped to [0,1]; each has error <=1/32. No monotonicity or shared-distribution property is assumed.",
        "empty_address_acceptances": zero_address_count,
        "maximum_midpoint_tests": max_tests,
        "minimum_observed_16_times_cell_width_times_density": str(min_tariff_ratio),
        "narrow_position_checks": narrow_count,
        "all_passed": True,
        "systems": reports,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()
    report = run_checks()
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "volume_systems": report["volume_systems"],
                      "midpoint_searches": report["midpoint_searches"],
                      "narrow_position_checks": report["narrow_position_checks"],
                      "report": str(args.output.resolve())}))


if __name__ == "__main__":
    main()
