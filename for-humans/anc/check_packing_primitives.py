#!/usr/bin/env python3
"""Exact diagnostics for local certainty, refinement sections, and volumes.

Permutation/gap enumeration and an independent integer subset-polynomial
recurrence supply exact reference volumes. These diagnose local certainty and
refinement without persistent tightening on small systems. They are reference
calculations, not the current adversary's finite digit estimator. These finite
checks do not prove the general statements or simulate all trajectories.
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


def substitute_incident_constraints(intervals, edges, x, position):
    """Return the remaining system after fixing x, using only incident arcs."""
    bounds = [list(ab) for ab in interval_fractions(intervals)]
    kept = [y for y in range(len(bounds)) if y != x]
    new_id = {y: i for i, y in enumerate(kept)}
    remaining_edges = []
    for u, v in edges:
        if u == x:
            bounds[v][0] = max(bounds[v][0], position)
        elif v == x:
            bounds[u][1] = min(bounds[u][1], position)
        else:
            remaining_edges.append((new_id[u], new_id[v]))
    return [tuple(bounds[y]) for y in kept], remaining_edges, kept


def check_local_certainty_and_sections(name, intervals, edges, full_volume):
    """Test the new criteria against exact volumes on one positive region."""
    n = len(intervals)
    supports, _ = effective_data(intervals, edges)
    pred, succ = relations(n, edges)
    counts = Counter()
    assert subset_volume(supports, edges) == full_volume, (name, "effective_volume")
    counts["effective_region_volume_checks"] += 1

    orientation_volumes = {}
    for x in range(n):
        for y in range(n):
            if x == y:
                continue
            volume = subset_volume(intervals, [*edges, (x, y)])
            orientation_volumes[x, y] = volume
            if y in succ[x]:
                assert volume == full_volume, (name, "forward_path", x, y)
                counts["directed_path_orientation_checks"] += 1
            elif y in pred[x]:
                assert volume == 0, (name, "reverse_path", x, y)
                counts["directed_path_orientation_checks"] += 1
            else:
                feasible = supports[x][0] < supports[y][1]
                assert (volume > 0) == feasible, (name, "local_certainty", x, y)
                counts["incomparable_orientation_checks"] += 1
                counts["incomparable_infeasible_orientations"] += not feasible
                counts["touching_effective_endpoint_checks"] += supports[x][0] == supports[y][1]
            counts["ordered_pair_checks"] += 1
        for y in range(x):
            assert orientation_volumes[x, y] + orientation_volumes[y, x] == full_volume, (
                name, "opposite_orientation_partition", x, y
            )
            counts["opposite_orientation_partition_checks"] += 1

    for x in range(n):
        ell, upper = supports[x]
        for fraction in (Fraction(1, 4), Fraction(1, 2), Fraction(3, 4)):
            anchor = ell + fraction * (upper - ell)
            assert ell < anchor < upper
            raw_bounds, remaining_edges, kept = substitute_incident_constraints(intervals, edges, x, anchor)
            effective_bounds, effective_edges, _ = substitute_incident_constraints(supports, edges, x, anchor)
            raw_volume = subset_volume(raw_bounds, remaining_edges)
            effective_volume = subset_volume(effective_bounds, effective_edges)
            assert raw_volume == effective_volume > 0, (name, "section_volume", x, anchor)
            assert raw_volume == section_volume(intervals, edges, x, anchor)
            counts["raw_effective_section_volume_checks"] += 1
            assert interleaving_volume(raw_bounds, remaining_edges) == raw_volume, (
                name, "independent_section_volume", x, anchor
            )
            counts["independent_section_volume_checks"] += 1

            actual_supports, _ = effective_data(raw_bounds, remaining_edges)
            for index, y in enumerate(kept):
                lo, hi = supports[y]
                if y in pred[x]:
                    hi = min(hi, anchor)
                elif y in succ[x]:
                    lo = max(lo, anchor)
                assert actual_supports[index] == (lo, hi), (
                    name, "remaining_effective_endpoints", x, anchor, y,
                    actual_supports[index], (lo, hi)
                )
                counts["remaining_effective_interval_checks"] += 1
    return counts


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
        ("touching_incomparable_intervals", [(0, Fraction(1, 2)), (Fraction(1, 2), 1)],
                                           [], Fraction(1, 4)),
        ("remote_lower_endpoint", [(Fraction(3, 4), 1), (0, 1), (0, 1),
                                   (0, Fraction(1, 2))], [(0, 1), (1, 2)], Fraction(1, 768)),
        ("remote_upper_endpoint", [(0, 1), (0, 1), (0, Fraction(1, 4)),
                                   (Fraction(1, 2), 1)], [(0, 1), (1, 2)], Fraction(1, 768)),
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
    positive_by_size = Counter()
    zero_by_size = Counter()
    certainty_and_section_counts = Counter()
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
            certainty_and_section_counts.update(
                check_local_certainty_and_sections(name, intervals, edges, reference)
            )
        reports.append({"name": name, "kind": kind, "vertices": n, "edges": len(edges),
                        "volume": str(calculated), "passed": True})

    return {
        "status": "passed",
        "scope": "Small exact diagnostics of endpoint-interleaving volume, complete local certainty, raw-bound refinement sections and their effective endpoints. Not a proof of these properties for all states, a formal verification of locality or the asymptotic adversary, or a simulation of all adversary trajectories.",
        "arithmetic": "Python integers and fractions.Fraction only",
        "seed": SEED,
        "volume_systems": len(systems),
        "seeded_systems": 5 * CASES_PER_SIZE,
        "explicit_systems": len(explicit),
        "volume_methods": ["coordinate permutations and ordered endpoint-gap assignments",
                           "independent previous integer subset-polynomial recurrence"],
        "positive_systems_by_size": dict(sorted(positive_by_size.items())),
        "zero_volume_systems_by_size": dict(sorted(zero_by_size.items())),
        "local_certainty_and_sections": dict(sorted(certainty_and_section_counts.items())),
        "section_anchor_fractions_of_effective_width": ["1/4", "1/2", "3/4"],
        "additional_explicit_cases": ["touching_incomparable_intervals", "remote_lower_endpoint", "remote_upper_endpoint"],
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
                      "local_certainty_and_sections": report["local_certainty_and_sections"],
                      "report": str(args.output.resolve())}))


if __name__ == "__main__":
    main()
