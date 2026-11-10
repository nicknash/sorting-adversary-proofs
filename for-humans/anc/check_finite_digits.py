#!/usr/bin/env python3
"""Small exact diagnostics for finite digit updates and rounded anchors.

These check finite examples and algebraic identities, not the general locality
proof or every adversary trajectory. No nonstandard dependencies are used.
"""
from collections import Counter
from fractions import Fraction as F
from math import comb
from pathlib import Path
from random import Random
import json


def update(z, low, high, digit, radix):
    return (z + (radix - 1 - digit) * low + digit * high) / radix


def round_anchor(left, right):
    """Round up on the largest binary grid no wider than the interval."""
    assert F(0) < left < right < F(1)
    spacing, exponent = F(1), 0
    while spacing > right-left:
        spacing /= 2
        exponent += 1
    scaled = left / spacing
    c = spacing * (-(-scaled.numerator // scaled.denominator))
    return c, exponent


def bits(x):
    d = x.denominator
    assert d & (d - 1) == 0
    return d.bit_length() - 1


def locality_checks():
    """Compare both endpoints with frozen boundaries and different tie orders."""
    random = Random(731)
    cases = 0
    for height in (2, 3, 4):
        size = 4 * height * 3 + 5
        layers = [z % height for z in range(size)]
        pred = [set() for _ in range(size)]
        succ = [set() for _ in range(size)]
        for x in range(size - 1):
            u, v = sorted((x, x + 1), key=layers.__getitem__)
            succ[u].add(v)
            pred[v].add(u)
        full_order = sorted(range(size), key=lambda z: (layers[z], z))

        def sweep(values, order, digits, radix):
            for z in order:
                low = max([left[z], *(values[u] for u in pred[z])])
                high = min([right[z], *(values[u] for u in succ[z])])
                values[z] = update(values[z], low, high, digits[z], radix)

        for sweeps in (1, 2, 3):
            for queried in ((size // 2,), (size // 3, 2 * size // 3)):
                for radix in (2, 4):
                    for _ in range(32):
                        # Canonical endpoints increase along every arc.
                        left = [F(3 * layers[z] + random.randrange(3), 32)
                                for z in range(size)]
                        right = [left[z] + F(1, 2) for z in range(size)]
                        radius = height * sweeps + 1
                        distance = [min(abs(z - x) for x in queried) for z in range(size)]
                        retained = {z for z in range(size) if distance[z] <= radius}
                        assert any(d == radius for d in distance)
                        assert len(retained) < size
                        local_order = sorted((z for z in retained if distance[z] < radius),
                                             key=lambda z: (layers[z], -z))
                        full_low, full_high = left.copy(), right.copy()
                        local_low = {z: left[z] for z in retained}
                        local_high = {z: right[z] for z in retained}
                        for _ in range(sweeps):
                            digits = [random.randrange(radix) for _ in range(size)]
                            sweep(full_low, full_order, digits, radix)
                            sweep(full_high, full_order, digits, radix)
                            sweep(local_low, local_order, digits, radix)
                            sweep(local_high, local_order, digits, radix)
                        assert all((full_low[z], full_high[z]) == (local_low[z], local_high[z])
                                   for z in queried)
                        cases += 1
    return cases


def run():
    invariant_checks = 0
    for radix in (2, 4, 8, 16):
        for low, high in ((F(0), F(1)), (F(3, 8), F(7, 8))):
            for degree in range(9):
                # Integrate the polynomial update over the old uniform value,
                # then average the digit choices. This is continuous integration.
                integral = F(0)
                for digit in range(radix):
                    offset = update(low, low, high, digit, radix)
                    slope = (high - low) / radix
                    integral += sum(F(comb(degree, p), p + 1) * offset**(degree-p)
                                    * slope**p for p in range(degree + 1)) / radix
                target = (high**(degree+1) - low**(degree+1)) / ((degree+1)*(high-low))
                assert integral == target
                invariant_checks += 1

    anchor_checks = 0
    for a in range(1, 64):
        for b in range(a+1, 64):
            left, right = F(a, 64), F(b, 64)
            c, exponent = round_anchor(left, right)
            spacing = F(1, 2**exponent)
            assert spacing <= right-left < 2*spacing
            assert left <= c <= right
            assert bits(c) <= max(bits(left), bits(right))
            m = bits(c)-1
            assert right-left < F(1, 2**m)
            # Independently enumerate the selected grid and check upward rounding.
            choices = [F(j, 2**exponent) for j in range(2**exponent+1)
                       if left <= F(j, 2**exponent) <= right]
            assert c == min(choices)
            anchor_checks += 1

    # This distinguishes the algorithm from minimum-denominator selection.
    nonminimal = round_anchor(F(11,32), F(17,32))[0]
    assert nonminimal == F(3,8) and F(11,32) < F(1,2) < F(17,32)

    fallback_checks = 0
    for a in range(64):
        for b in range(a+1, 65):
            ell, upper = F(a, 64), F(b, 64)
            width = upper-ell
            c, exponent = round_anchor(ell+width/4, upper-width/4)
            assert ell+width/4 <= c <= upper-width/4
            assert ell < c < upper
            assert bits(c) <= max(bits(ell), bits(upper))+1
            assert width/2 < F(1, 2**(bits(c)-1))
            fallback_checks += 1
    for precision in range(3, 129):
        width = F(1, 2**precision)
        c, exponent = round_anchor(F(1, 2)-width/4, F(1, 2)+width/4)
        assert c == F(1, 2)
        assert bits(c) <= precision+2
        fallback_checks += 1

    # All finite computations for a two-item chain. Equal final states are
    # collected with their exact multiplicities, preserving all digit choices.
    states = Counter({(F(0),F(0)):1})
    chain_reports = []
    update_checks = 0
    for sweep in range(1,9):
        for vertex in range(2):
            next_states = Counter()
            for state,count in states.items():
                low,high = (F(0),state[1]) if vertex==0 else (state[0],F(1))
                for digit in range(2):
                    values=list(state);values[vertex]=update(values[vertex],low,high,digit,2)
                    assert F(0)<=values[0]<=values[1]<=F(1)
                    assert max(map(bits,values)) <= 2*(sweep-1)+vertex+1
                    next_states[tuple(values)] += count
                    update_checks += 1
            states=next_states
        assert sum(states.values()) == 2**(2*sweep)
        chain_reports.append({'sweeps':sweep,'computations':2**(2*sweep),
                              'distinct_final_states':len(states)})
    assert any(state[0]==state[1] for state in states)
    return {'status':'passed','scope':__doc__.strip(),
            'continuous_invariance_moment_checks':invariant_checks,
            'full_local_endpoint_cases':locality_checks(),
            'rounding_checks':anchor_checks,'fallback_anchor_checks':fallback_checks,
            'nonminimal_anchor_example_checked':True,
            'finite_chain_update_checks':update_checks,
            'finite_chain':chain_reports,
            'note':'Small chain parameters are diagnostic examples, not the much larger certified locality parameters.'}


if __name__ == '__main__':
    result=run()
    destination=Path(__file__).with_suffix('.json')
    destination.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='finite_chain'}))
