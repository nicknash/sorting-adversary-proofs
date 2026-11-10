#!/usr/bin/env python3
"""Exact finite diagnostics for local enclosing intervals and their certificates.

These check small instances with rational arithmetic, including genuinely
truncated graphs. Independent polytope-volume enumeration checks the certified
probabilities. The small parameters used here do not replace the general
contraction proof or its much larger uniform choices.
"""
from collections import Counter, deque
from fractions import Fraction as F
from itertools import combinations_with_replacement, permutations, product
from math import factorial
from pathlib import Path
import json
from check_finite_digits import round_anchor


def topological(n, arcs):
    remaining = set(range(n))
    order = []
    while remaining:
        available = [v for v in remaining
                     if not any(b == v and a in remaining for a, b in arcs)]
        if not available:
            raise ValueError('Directed cycle')
        v = min(available)
        order.append(v)
        remaining.remove(v)
    return order


def normalize(bounds, arcs):
    n = len(bounds)
    order = topological(n, arcs)
    low, high = [a for a, _ in bounds], [b for _, b in bounds]
    for v in order:
        low[v] = max([low[v]] + [low[u] for u, w in arcs if w == v])
    for v in reversed(order):
        high[v] = min([high[v]] + [high[u] for w, u in arcs if w == v])
    assert all(a < b for a, b in zip(low, high))
    return low, high, order


def neighborhood(n, arcs, targets, radius):
    adjacent = [set() for _ in range(n)]
    for a, b in arcs:
        adjacent[a].add(b)
        adjacent[b].add(a)
    distance = {v: 0 for v in targets}
    pending = deque(targets)
    while pending:
        v = pending.popleft()
        for u in adjacent[v]:
            if u not in distance:
                distance[u] = distance[v] + 1
                pending.append(u)
    retained = sorted(v for v in distance if distance[v] <= radius)
    interior = set(v for v in retained if distance[v] < radius)
    return retained, interior


def step(values, vertex, low, high, predecessors, successors, digit, radix):
    lower = max([low[vertex]] + [values[u] for u in predecessors[vertex]])
    upper = min([high[vertex]] + [values[u] for u in successors[vertex]])
    assert lower <= values[vertex] <= upper
    return (values[vertex] + (radix-1-digit)*lower + digit*upper) / radix


def bits(x):
    denominator = x.denominator
    assert denominator & (denominator-1) == 0
    return denominator.bit_length()-1


def enclose(bounds, arcs, targets, radius, radix, sweeps):
    low, high, order = normalize(bounds, arcs)
    retained, interior = neighborhood(len(bounds), arcs, targets, radius)
    index = {v: i for i, v in enumerate(retained)}
    b = len(retained)
    lo, hi = [low[v] for v in retained], [high[v] for v in retained]
    pred = [[index[a] for a, z in arcs if z == v and a in index] for v in retained]
    succ = [[index[z] for a, z in arcs if a == v and z in index] for v in retained]
    visits = [index[v] for v in order if v in interior]
    states = Counter({tuple(lo+hi): 1})
    initial_bits = max(map(bits, lo+hi))
    updates = 0
    for _ in range(sweeps):
        for v in visits:
            next_states = Counter()
            for state, multiplicity in states.items():
                lower, upper = list(state[:b]), list(state[b:])
                for digit in range(radix):
                    a, z = lower.copy(), upper.copy()
                    a[v] = step(a, v, lo, hi, pred, succ, digit, radix)
                    z[v] = step(z, v, lo, hi, pred, succ, digit, radix)
                    assert all(x <= y for x, y in zip(a, z))
                    next_states[tuple(a+z)] += multiplicity
            states = next_states
            updates += 1
    boxes = Counter()
    precision = initial_bits + updates*(radix.bit_length()-1)
    for state, count in states.items():
        assert max(map(bits, state)) <= precision
        boxes[tuple((state[index[x]], state[b+index[x]]) for x in targets)] += count
        for v in set(retained)-interior:
            assert state[index[v]] == low[v] and state[b+index[v]] == high[v]
    assert sum(boxes.values()) == radix**(len(visits)*sweeps)
    return boxes, {'retained': retained, 'interior': sorted(interior),
                   'outside': sorted(set(range(len(bounds)))-set(retained)),
                   'digit_sequences': sum(boxes.values()),
                   'distinct_entries': len(boxes), 'precision_bound': precision}


def volume(bounds, arcs):
    """Independent exact integration by coordinate orders and endpoint segments.

    For each compatible total order, distribute its ordered coordinates among
    the segments cut by all interval endpoints. A segment of length w holding
    r ordered coordinates contributes w**r/r!.
    """
    if any(a >= b for a, b in bounds):
        return F(0)
    endpoints = sorted(set(x for interval in bounds for x in interval))
    segments = list(zip(endpoints, endpoints[1:]))
    assignments = list(combinations_with_replacement(range(len(segments)), len(bounds)))
    answer = F(0)
    for order in permutations(range(len(bounds))):
        rank = {v: i for i, v in enumerate(order)}
        if any(rank[a] >= rank[b] for a, b in arcs):
            continue
        for choices in assignments:
            if not all(bounds[v][0] <= segments[j][0] and segments[j][1] <= bounds[v][1]
                       for v, j in zip(order, choices)):
                continue
            term = F(1)
            for j, count in Counter(choices).items():
                term *= (segments[j][1]-segments[j][0])**count / factorial(count)
            answer += term
    return answer


def mass(bounds, arcs, vertex, left, right):
    modified = list(bounds)
    a, b = modified[vertex]
    modified[vertex] = max(a, left), min(b, right)
    return volume(modified, arcs)/volume(bounds, arcs)


def certify(boxes, threshold=None):
    n = sum(boxes.values())
    left = right = 0
    for entry, count in boxes.items():
        (a, b), (c, d) = entry if threshold is None else (entry[0], (threshold, threshold))
        if b < c:
            left += count
        elif d < a:
            right += count
    return F(left, n), F(right, n), F(n-left-right, n)


def accepted_comparison(boxes, eta, threshold=None):
    left, right, _ = certify(boxes, threshold)
    if max(left, right) < F(1,2)-eta:
        return None
    return 'left' if left >= right else 'right'


def ranked(counter, rank):
    count = 0
    for value, multiplicity in sorted(counter.items()):
        count += multiplicity
        if count >= rank:
            return value
    raise AssertionError('Rank exceeds list length')


def central(boxes):
    n = sum(boxes.values())
    assert n % 4 == 0
    lowers, uppers = Counter(), Counter()
    for ((a, b),), count in boxes.items():
        lowers[a] += count
        uppers[b] += count
    u = ranked(uppers, n//4)
    v = ranked(lowers, 3*n//4)
    left = sum(c for ((a, b),), c in boxes.items() if b <= u)
    middle = sum(c for ((a, b),), c in boxes.items() if u <= a <= b <= v)
    right = sum(c for ((a, b),), c in boxes.items() if a >= v)
    assert left >= n//4 and right >= n//4
    return u, v, [F(left, n), F(middle, n), F(right, n)], lowers, uppers


def certified_central(boxes):
    u, v, counts, _, _ = central(boxes)
    if u >= v or counts[1] < F(1,4):
        return None
    return u, v


def anchor_for_refinement(boxes, low, high, reason):
    assert reason in ('failure', 'repair')
    interval = certified_central(boxes) if reason == 'repair' else None
    branch = 'central' if interval is not None else 'middle_half'
    if interval is None:
        width = high-low
        interval = low+width/4, high-width/4
    return round_anchor(*interval)[0], branch


def check_moment_lemma():
    # Each site's multiplier depends on the same fresh digit; the two sites
    # need not be independent. Exact enumeration checks the resulting moments.
    moment_checks = 0
    for same_exception in (False, True):
        states = Counter({(F(1),F(3,4)):1})
        for sweep in range(1,5):
            next_states = Counter()
            for state, count in states.items():
                for digit in range(8):
                    multipliers = (F(1) if digit == 0 else F(1,2),
                                   F(1) if digit == (0 if same_exception else 1) else F(1,2))
                    next_states[tuple(a*max(state) for a in multipliers)] += count
            states = next_states
            for vertex in range(2):
                moment = sum(count*state[vertex]**3 for state,count in states.items())/8**sweep
                assert moment <= F(1,2**sweep)
                moment_checks += 1
    calibrations = []
    for m, height in ((1,1),(2,1),(4,1),(1,2)):
        radix = 1
        while radix < 4*m*m:
            radix *= 2
        beta = 1-F(1,radix**height)
        exponent, power = 1, beta
        while power > F(1,4*m):
            exponent += 1
            power *= beta
        assert power <= F(1,4*m) < power/beta
        exceptional = F(m,radix)
        assert exceptional+(1-exceptional)*power <= F(1,2*m)
        alpha, delta, queries = F(1,16), F(1,8), 2
        sweeps = 1
        target = alpha*delta**exponent/queries
        while F(1,2**sweeps) > target:
            sweeps += 1
        assert F(1,2**sweeps) <= target < F(1,2**(sweeps-1))
        calibrations.append({'M':m,'height':height,'radix':radix,
                             'moment_power':exponent,'sweeps':sweeps})
    return moment_checks, calibrations


def shared_full_run(bounds, arcs, targets, radius, radix, sweeps, digits, initial,
                    freeze=True, require_enclosure=True):
    low, high, order = normalize(bounds, arcs)
    retained, interior = neighborhood(len(bounds), arcs, targets, radius)
    update_set = interior if freeze else set(retained)
    full = list(initial)
    lower, upper = low.copy(), high.copy()
    pred = [[a for a, b in arcs if b == v] for v in range(len(bounds))]
    succ = [[b for a, b in arcs if a == v] for v in range(len(bounds))]
    local_pred = [[a for a in pred[v] if a in retained] for v in range(len(bounds))]
    local_succ = [[a for a in succ[v] if a in retained] for v in range(len(bounds))]
    moved_boundary = moved_outside = False
    checks = 0
    for sweep in range(sweeps):
        for v in order:
            digit = digits[sweep*len(bounds)+v]
            if v in update_set:
                lower[v] = step(lower, v, low, high, local_pred, local_succ, digit, radix)
                upper[v] = step(upper, v, low, high, local_pred, local_succ, digit, radix)
            previous = full[v]
            full[v] = step(full, v, low, high, pred, succ, digit, radix)
            moved_boundary |= v in set(retained)-interior and full[v] != previous
            moved_outside |= v not in retained and full[v] != previous
            enclosed = all(lower[x] <= full[x] <= upper[x] for x in retained)
            if require_enclosure:
                assert enclosed
            elif not enclosed:
                return False, checks, moved_boundary, moved_outside
            checks += len(retained)
    return True, checks, moved_boundary, moved_outside


def run():
    zero_one = (F(0), F(1))
    for n in range(1, 6):
        assert volume([zero_one]*n, [(i,i+1) for i in range(n-1)]) == F(1,factorial(n))
    assert volume([zero_one]*3, [(0,1),(0,2)]) == F(1,3)
    assert volume([(F(0),F(3,4)),(F(1,4),F(1))], []) == F(9,16)
    assert mass([zero_one]*2, [(0,1)], 0, F(0), F(1,2)) == F(3,4)
    cases = [
        ('independent_pair', [zero_one]*2, [], [0,1], 2, 2, 4),
        ('ordered_pair', [zero_one]*2, [(0,1)], [0,1], 2, 2, 4),
        ('reverse_ordered_pair', [zero_one]*2, [(0,1)], [1,0], 2, 2, 4),
        ('fork_pair', [zero_one]*3, [(0,1),(0,2)], [1,2], 2, 2, 3),
        ('unequal_bounds', [(F(0),F(3,4)),(F(1,4),F(1))], [], [0,1], 2, 4, 2),
        ('truncated_height_two', [(F(0),F(3,4)),zero_one,zero_one,zero_one,(F(1,4),F(1))],
         [(0,1),(2,1),(2,3),(4,3)], [0,4], 1, 2, 3),
    ]
    reports = []
    probability_checks = 0
    acceptance_checks = 0
    for name, bounds, arcs, targets, radius, radix, sweeps in cases:
        boxes, report = enclose(bounds, arcs, targets, radius, radix, sweeps)
        total_volume = volume(bounds, arcs)
        assert total_volume > 0
        true_left = volume(bounds, arcs+[(targets[0],targets[1])])/total_volume
        p, q, unresolved = certify(boxes)
        assert p <= true_left and q <= 1-true_left and p+q+unresolved == 1
        probability_checks += 2
        accepted = accepted_comparison(boxes, F(1,64))
        if accepted is not None:
            assert (true_left if accepted == 'left' else 1-true_left) >= F(1,2)-F(1,64)
        acceptance_checks += 1
        if 'ordered_pair' in name:
            assert (q == 0 and true_left == 1) or (p == 0 and true_left == 0)
        for coordinate, vertex in enumerate(targets):
            marginal = Counter()
            for entry, count in boxes.items():
                marginal[(entry[coordinate],)] += count
            for threshold in (F(0),F(1,4),F(1,2),F(3,4),F(1)):
                a, b, _ = certify(marginal, threshold)
                actual = mass(bounds, arcs, vertex, F(0), threshold)
                assert a <= actual and b <= 1-actual
                probability_checks += 2
        if name.startswith('truncated'):
            assert report['outside'] and set(report['retained'])-set(report['interior'])
            assert p > 0
        report.update(name=name, true_left=str(true_left),
                      certified_left=str(p), certified_right=str(q), unresolved=str(unresolved),
                      accepted_orientation=accepted)
        reports.append(report)

    # Actual full-graph boundary coordinates move, including under influence
    # from omitted vertices. Check enclosure after every individual update.
    moving_bounds = [(F(0),F(1,4)),zero_one,(F(3,4),F(1)),zero_one]
    chain_arcs = [(0,1),(1,2),(2,3)]
    initial_states = [(F(1,8),F(1,2),F(13,16),F(15,16)),
                      (F(1,16),F(1,4),F(7,8),F(31,32))]
    enclosure_checks = moving_boundary_runs = moving_outside_runs = 0
    for initial in initial_states:
        for digits in product(range(2), repeat=8):
            good, count, boundary_moved, outside_moved = shared_full_run(
                moving_bounds, chain_arcs, [1], 1, 2, 2, digits, initial)
            assert good
            enclosure_checks += count
            moving_boundary_runs += boundary_moved
            moving_outside_runs += outside_moved
    assert moving_boundary_runs and moving_outside_runs

    # Negative control: updating the truncated boundary can exclude a feasible
    # full assignment. Freezing it prevents this concrete failure.
    digits = (0,1,0, 1,0,0)
    initial = (F(1,16),F(1,8),F(3,16))
    unsafe = shared_full_run([zero_one]*3, [(0,1),(1,2)], [0], 1, 2, 2,
                             digits, initial, freeze=False, require_enclosure=False)
    assert unsafe[0] is False
    safe = shared_full_run([zero_one]*3, [(0,1),(1,2)], [0], 1, 2, 2,
                           digits, initial, freeze=True)
    assert safe[0]

    central_reports = []
    repeated_endpoint_cases = 0
    for name, bounds, arcs, vertex, sweeps in [
        ('minimum_of_two', [zero_one]*2, [(0,1)], 0, 8),
        ('maximum_of_two', [zero_one]*2, [(0,1)], 1, 8),
        ('short_interval', [(F(13,32),F(15,32))], [], 0, 4),
    ]:
        boxes, report = enclose(bounds, arcs, [vertex], 3, 2, sweeps)
        u, v, counts, lowers, uppers = central(boxes)
        assert counts[1] >= F(1,4), (name, counts)
        assert certified_central(boxes) == (u,v)
        assert u < v
        actual = [mass(bounds, arcs, vertex, F(0),u),
                  mass(bounds, arcs, vertex, u,v),
                  mass(bounds, arcs, vertex, v,F(1))]
        assert all(F(1,4) <= certified <= true for certified,true in zip(counts,actual))
        probability_checks += 3
        repeated = any(count > 1 for count in lowers.values()) or any(count > 1 for count in uppers.values())
        repeated_endpoint_cases += repeated
        report.update(name=name, interval=[str(u),str(v)],
                      certified_masses=list(map(str,counts)), true_masses=list(map(str,actual)),
                      repeated_endpoints=repeated)
        central_reports.append(report)
    assert repeated_endpoint_cases >= 2

    boxes, _ = enclose([zero_one]*2, [(0,1)], [0], 2, 2, 1)
    _, _, early_counts, _, _ = central(boxes)
    assert early_counts[1] < F(1,4)
    assert certified_central(boxes) is None
    fallback, branch = anchor_for_refinement(boxes, F(0), F(1), 'repair')
    assert branch == 'middle_half' and fallback == F(1,2)

    # Comparison failure goes directly to the middle half. Supplying no
    # marginal list makes an accidental central-certificate call fail here.
    # The chosen coordinate is uniform, so its density is independently 1/W.
    low, high = F(1,2), F(1,2)+F(1,2**20)
    boxes, _ = enclose([(low,high)]*2, [], [0,1], 2, 2, 2)
    assert accepted_comparison(boxes, F(1,64)) is None
    direct_anchor, branch = anchor_for_refinement(None, low, high, 'failure')
    assert branch == 'middle_half' and low < direct_anchor < high
    assert low+(high-low)/4 <= direct_anchor <= high-(high-low)/4
    assert F(1,1)/(high-low) == 2**20
    assert bits(direct_anchor) <= max(bits(low), bits(high))+2

    # Check the all-pair small-gap conclusion on a comparable pair directly:
    # on 0<x<y<1, the gap has density 2(1-d), 0<d<1.
    gap_checks = 0
    grid = [F(i,8) for i in range(-8,9)]
    for i,a in enumerate(grid):
        for b in grid[i+1:]:
            for sign in (-1,1):
                left,right = (a,b) if sign == 1 else (-b,-a)
                left,right = max(F(0),left),min(F(1),right)
                actual = F(0) if left >= right else 2*(right-left)-(right*right-left*left)
                assert actual <= 2*(b-a)
                gap_checks += 1
    moment_checks, calibrations = check_moment_lemma()
    return {'status':'passed', 'scope':__doc__.strip(),
            'independent_volume_identity_checks':8,
            'independent_probability_inequalities':probability_checks,
            'accepted_answer_checks':acceptance_checks,
            'comparable_gap_checks':gap_checks,
            'correlated_multiplier_moment_checks':moment_checks,
            'moment_parameter_calibrations':calibrations,
            'atomic_enclosure_checks':enclosure_checks,
            'moving_full_boundary_runs':moving_boundary_runs,
            'moving_omitted_vertex_runs':moving_outside_runs,
            'unsafe_unfrozen_boundary_detected':True,
            'insufficient_sweeps_rejected':True,
            'central_failure_middle_half_checked':True,
            'comparison_failure_direct_middle_checked':True,
            'repeated_endpoint_central_cases':repeated_endpoint_cases,
            'comparison_cases':reports, 'central_interval_cases':central_reports}


if __name__ == '__main__':
    result = run()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if not k.endswith('_cases')}))
