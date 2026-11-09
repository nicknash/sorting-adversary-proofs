#!/usr/bin/env python3
"""Small exact diagnostics for finite digit updates and shortest anchors.

These check finite examples and algebraic identities, not the general locality
proof or every adversary trajectory. No nonstandard dependencies are used.
"""
from collections import Counter
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json


def update(z, low, high, digit, radix):
    return (z + (radix - 1 - digit) * low + digit * high) / radix


def shortest(left, right):
    a, b, depth = F(0), F(1), 0
    while True:
        c = (a + b) / 2
        if c < left:
            a = c
        elif c > right:
            b = c
        else:
            return c, depth, (a, b)
        depth += 1


def bits(x):
    d = x.denominator
    assert d & (d - 1) == 0
    return d.bit_length() - 1


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
        for b in range(a, 64):
            left, right = F(a, 64), F(b, 64)
            c, depth, interval = shortest(left, right)
            # Independently enumerate reduced fractions by precision.
            for m in range(7):
                candidates = [F(2*i+1, 2**(m+1)) for i in range(2**m)
                              if left <= F(2*i+1, 2**(m+1)) <= right]
                if candidates:
                    assert candidates == [c] and m == depth
                    break
            else:
                raise AssertionError('No candidate')
            assert interval[0] <= left <= right <= interval[1]
            assert interval[1]-interval[0] == F(1, 2**depth)
            assert bits(c) <= max(bits(left), bits(right)) + 1
            anchor_checks += 1

    narrow_checks = 0
    for a in range(64):
        for b in range(a+1, 65):
            ell, upper = F(a, 64), F(b, 64)
            width = upper-ell
            c, depth, interval = shortest(ell+width/4, upper-width/4)
            assert ell < c < upper
            assert bits(c) <= max(bits(ell), bits(upper))+1
            assert width/2 <= interval[1]-interval[0]
            narrow_checks += 1
    for precision in range(3, 129):
        width = F(1, 2**precision)
        c, depth, _ = shortest(F(1, 2)-width/4, F(1, 2)+width/4)
        assert c == F(1, 2) and depth == 0
        narrow_checks += 1

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
            'shortest_fraction_checks':anchor_checks,'narrow_anchor_checks':narrow_checks,
            'finite_chain_update_checks':update_checks,
            'finite_chain':chain_reports,
            'note':'Small chain parameters are diagnostic examples, not the much larger certified locality parameters.'}


if __name__ == '__main__':
    result=run()
    destination=Path(__file__).with_suffix('.json')
    destination.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='finite_chain'}))
