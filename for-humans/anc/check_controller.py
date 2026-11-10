#!/usr/bin/env python3
"""Exhaustive small-graph checks of repair after one inserted arc.

The old DAGs have vertices 0,...,n-1 in topological order. Each possible
new arc is tried, including backward arcs when the result is acyclic.
Every eligible path or degree choice is checked. These tests concern the
graph invariant, not the probability certificates or complete executions.
"""
from collections import Counter
from itertools import combinations, permutations
from pathlib import Path
import json


def order(n, arcs):
    remaining = set(range(n))
    result = []
    while remaining:
        eligible = [v for v in remaining
                    if not any(b == v and a in remaining for a, b in arcs)]
        if not eligible:
            return None
        v = min(eligible)
        remaining.remove(v)
        result.append(v)
    return result


def stats(n, arcs):
    topo = order(n, arcs)
    if topo is None:
        return None
    degree = [0] * n
    height = [1] * n
    for a, b in arcs:
        degree[a] += 1
        degree[b] += 1
    for v in reversed(topo):
        height[v] = 1 + max((height[b] for a, b in arcs if a == v), default=0)
    return degree, max(height, default=0)


def paths(n, arcs, length):
    found = []

    def visit(path):
        if len(path) == length:
            found.append(tuple(path))
        else:
            for a, b in sorted(arcs):
                if a == path[-1]:
                    visit(path + [b])

    for v in range(n):
        visit([v])
    return found


def check():
    counts = Counter()
    for n in range(1, 6):
        possible = list(combinations(range(n), 2))
        for mask in range(1 << len(possible)):
            old = {arc for bit, arc in enumerate(possible) if mask & (1 << bit)}
            old_degree, old_height = stats(n, old)
            for k in range(2, n + 2):
                if max(old_degree, default=0) >= k:
                    continue
                for threshold in range(2, n + 2):
                    if old_height >= threshold:
                        continue
                    counts['valid_old_states'] += 1
                    for arc in permutations(range(n), 2):
                        if arc in old:
                            continue
                        new = old | {arc}
                        new_stats = stats(n, new)
                        if new_stats is None:
                            counts['cyclic_insertions_excluded'] += 1
                            continue
                        degree, height = new_stats
                        counts['acyclic_insertions'] += 1
                        assert max(degree, default=0) <= k
                        assert height < 2 * threshold
                        high = [x for x in range(n) if degree[x] == k]
                        assert set(high) <= set(arc)
                        selected_paths = paths(n, new, threshold)
                        choices = selected_paths or [(x,) for x in high]
                        if not choices:
                            assert max(degree, default=0) < k and height < threshold
                            counts['no_repair_needed'] += 1
                        for selected in choices:
                            if selected_paths:
                                assert arc in set(zip(selected, selected[1:]))
                                assert set(arc) <= set(selected)
                                counts['complete_path_repairs'] += 1
                            else:
                                assert len(selected) == 1 and selected[0] in arc
                                counts['degree_repairs'] += 1
                            removed = set(selected)
                            after = {edge for edge in new if not (set(edge) & removed)}
                            assert after <= old
                            after_degree, after_height = stats(n, after)
                            assert max(after_degree, default=0) < k
                            assert after_height < threshold
                            counts['repair_choices_verified'] += 1
    assert counts['complete_path_repairs'] and counts['degree_repairs']
    return {'status': 'passed', 'scope': __doc__.strip(),
            'maximum_vertices': 5, **dict(counts)}


if __name__ == '__main__':
    result = check()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))
