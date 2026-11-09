#!/usr/bin/env python3
"""Exact finite diagnostics for the finite-averaging audit (9 Nov 2026).

These checks use small parameters and exact Fraction arithmetic. They do NOT
execute the astronomically large certified adversary and do NOT establish the
universal estimator theorem. They check ties, dependency-cone indexing, and
the update/rounding inequalities on explicitly enumerated finite examples.

Usage: python3 check_finite_averaging.py [--output PATH]
"""

from argparse import ArgumentParser
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path


def graph_data(n, edges):
    pred, succ, adjacent = [[] for _ in range(n)], [[] for _ in range(n)], [[] for _ in range(n)]
    for u, v in edges:
        pred[v].append(u)
        succ[u].append(v)
        adjacent[u].append(v)
        adjacent[v].append(u)
    return pred, succ, adjacent


def tighten(lower, upper, order, pred, succ):
    lo, hi = list(lower), list(upper)
    for v in order:
        lo[v] = max([lo[v]] + [lo[u] for u in pred[v]])
    for v in reversed(order):
        hi[v] = min([hi[v]] + [hi[w] for w in succ[v]])
    assert all(a < b for a, b in zip(lo, hi))
    return lo, hi


def ball(target, radius, adjacent):
    result, frontier = {target}, {target}
    for _ in range(radius):
        frontier = {w for v in frontier for w in adjacent[v]} - result
        result |= frontier
    return result


def simulate(vertices, sweeps, order, pred, succ, lower, upper, quantiles):
    retained = set(vertices)
    values = {v: lower[v] for v in retained}
    for sweep in range(sweeps):
        for v in order:
            if v not in retained:
                continue
            a = max([lower[v]] + [values[u] for u in pred[v] if u in retained])
            b = min([upper[v]] + [values[w] for w in succ[v] if w in retained])
            assert a <= values[v] <= b, (v, a, values[v], b)
            u = quantiles[sweep][v]
            assert 0 <= u <= 1
            values[v] = (1-u)*a + u*b
    return values


def tie_example():
    mesh = [F(2*j+1, 8) for j in range(4)]
    strict_less = sum(x < y for x, y in product(mesh, repeat=2))
    strict_greater = sum(x > y for x, y in product(mesh, repeat=2))
    equal = sum(x == y for x, y in product(mesh, repeat=2))
    assert (strict_less, strict_greater, equal) == (6, 6, 4)
    p = F(strict_less, 16)
    assert p == F(3, 8) and 1-p == F(5, 8) and F(equal, 16) == F(1, 4)
    return {
        "vertices": 2, "edges": 0, "mesh_size": 4, "sweeps": 1,
        "trajectories": 16, "strict_less_count": strict_less,
        "strict_greater_count": strict_greater, "tie_count": equal,
        "strict_less_probability": str(p),
        "strict_greater_probability": str(F(strict_greater, 16)),
        "tie_probability": str(F(equal, 16)),
        "complement_of_strict_less": str(1-p),
        "continuous_target_probability": "1/2",
        "conclusion": "Use one strict-event estimate and its complement; two strict counts need not sum to one.",
    }


def dependency_cones():
    # An undirected path, directed from each even vertex to neighboring odds.
    # Directed paths have at most two vertices, while the undirected graph is long.
    n, height = 65, 2
    edges = [(i, i+1) if i % 2 == 0 else (i+1, i) for i in range(n-1)]
    pred, succ, adjacent = graph_data(n, edges)
    order = list(range(0, n, 2)) + list(range(1, n, 2))
    rank = {v: i for i, v in enumerate(order)}
    assert all(rank[u] < rank[v] for u, v in edges)
    assert max(map(len, adjacent)) == 2
    depth = [1]*n
    for v in order:
        depth[v] = 1 + max([0] + [depth[u] for u in pred[v]])
    assert max(depth) == height
    lower = [F(v % 7, 128) for v in range(n)]
    upper = [1-F((3*v+2) % 7, 128) for v in range(n)]
    lower, upper = tighten(lower, upper, order, pred, succ)
    assert all(lower[u] <= lower[v] and upper[u] <= upper[v] for u, v in edges)
    mesh = [F(2*j+1, 8) for j in range(4)]
    targets = [10, 21, 32, 43, 54]
    checks = 0
    retained_sizes = set()
    # Exhaust every pair of mesh values defining the alternating spatial/temporal
    # quantile pattern. All full/local comparisons share the same quantiles.
    for first, second in product(mesh, repeat=2):
        pair = [first, second]
        quantiles = [[pair[(v+sweep) % 2] for v in range(n)] for sweep in range(4)]
        for sweeps in range(1, 5):
            full = simulate(range(n), sweeps, order, pred, succ, lower, upper, quantiles)
            for target in targets:
                retained = ball(target, height*sweeps, adjacent)
                assert len(retained) < n
                local = simulate(retained, sweeps, order, pred, succ, lower, upper, quantiles)
                assert local[target] == full[target], (first, second, sweeps, target)
                retained_sizes.add(len(retained))
                checks += 1
    assert checks == 320
    return {
        "graph": "65-vertex zigzag DAG; even vertices point to adjacent odd vertices",
        "directed_height_vertices": height, "maximum_undirected_degree": 2,
        "global_endpoint_denominator": 128, "quantile_pattern_assignments": 16,
        "sweeps_tested": [1, 2, 3, 4], "query_vertices": targets,
        "radius": "height * sweeps", "all_truncations_proper": True,
        "retained_sizes": sorted(retained_sizes), "exact_agreements": checks,
    }


def update_rounding_checks():
    # These finite exhaustive tests include weak states with ties and degenerate
    # conditional intervals. No floating-point comparisons are used.
    examples = {
        "chain": (3, [(0, 1), (1, 2)]),
        "fork": (3, [(0, 1), (0, 2)]),
        "inverted_fork": (3, [(0, 2), (1, 2)]),
    }
    grid = [F(0), F(1, 2), F(1)]
    # Interior rational U values, rounded to S=4 midpoint cells.
    quantiles = [F(i, 32) for i in range(1, 32)]
    total, degenerate = 0, 0
    by_graph = {}
    for name, (n, edges) in examples.items():
        pred, succ, _ = graph_data(n, edges)
        states = [s for s in product(grid, repeat=n) if all(s[u] <= s[v] for u, v in edges)]
        checks = 0
        for x, y in product(states, repeat=2):
            old_error = max(abs(a-b) for a, b in zip(x, y))
            for v in range(n):
                a = max([F(0)] + [x[u] for u in pred[v]])
                b = min([F(1)] + [x[w] for w in succ[v]])
                c = max([F(0)] + [y[u] for u in pred[v]])
                d = min([F(1)] + [y[w] for w in succ[v]])
                assert a <= x[v] <= b and c <= y[v] <= d
                assert abs(a-c) <= old_error and abs(b-d) <= old_error
                for u in quantiles:
                    cell = (4*u.numerator)//u.denominator
                    rounded = F(2*cell+1, 8)
                    quantile_error = abs(u-rounded)
                    assert quantile_error <= F(1, 8)
                    first = (1-u)*a + u*b
                    same_quantile = (1-u)*c + u*d
                    second = (1-rounded)*c + rounded*d
                    assert abs(first-same_quantile) <= (1-u)*abs(a-c) + u*abs(b-d)
                    assert abs(same_quantile-second) == quantile_error*(d-c)
                    assert abs(first-second) <= old_error + quantile_error
                    checks += 1
                    degenerate += int(a == b or c == d)
        by_graph[name] = {"weak_states": len(states), "checks": checks}
        total += checks
    assert degenerate > 0
    return {
        "coordinate_grid": [str(x) for x in grid], "mesh_size": 4,
        "continuous_quantile_cases": len(quantiles), "graphs": by_graph,
        "exact_checks": total, "checks_including_degenerate_interval": degenerate,
        "checked_bound": "one updated-coordinate error <= previous sup error + quantile rounding error",
    }


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("finite_averaging_diagnostics.json"))
    args = parser.parse_args()
    results = {
        "scope": "Finite exact diagnostics only; not a simulation of certified huge parameters or a proof of the infinite theorem.",
        "arithmetic": "Python fractions.Fraction; exact rational arithmetic throughout",
        "tie_example": tie_example(),
        "dependency_cones": dependency_cones(),
        "update_rounding": update_rounding_checks(),
        "status": "passed",
    }
    args.output.write_text(json.dumps(results, indent=2)+"\n")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
