#!/usr/bin/env python3
"""Exact sanity checks for a replacement accounting proof.

These check algebra and small synthetic transitions, NOT the locality theorem,
not all sorting trajectories, and not a machine-checked mathematical proof.
Uses only Python's standard library. Run with Python 3.10+.
"""
from fractions import Fraction as F
import json
from pathlib import Path


def coefficients(k: int) -> tuple[int, F, F]:
    if k < 16:
        raise ValueError("The fixed-stage proof assumes k >= 16")
    # An exact rational variant of L = log_2(4k). Rounding up is conservative.
    ell = (4 * k - 1).bit_length()
    beta = F(k + 1 + ell, k - 5)
    tau = (4 * beta + ell) / k
    return ell, beta, tau


def run() -> dict[str, object]:
    stages = transitions = path_tests = 0
    for k in range(16, 4097):
        ell, beta, tau = coefficients(k)
        assert beta > 1 and tau > 0
        assert beta * (1 - F(1, k)) - (1 + F(1, k)) == tau
        assert 4 * beta + ell == k * tau
        conservative_query_cost = beta * (1 + F(1, k)) + tau
        target = 1 + F(17 + 3 * ell, k)
        assert target - conservative_query_cost == F((ell + 6) * (k - 15), k * (k - 5))
        assert conservative_query_cost <= target
        # Worst permitted log-density; use the conservative rounded slot cost.
        for m, degree in [(0, k), (1, k), (k, 0), (2*k+1, 0),
                          (k//2, k-k//2), (0, 0), (k-1, 1)]:
            log_density_lower = (1 - F(1, k)) * m - 4
            log_change_lower = (beta * log_density_lower - ell
                                - (1 + F(1, k)) * m + tau * degree)
            assert log_change_lower == tau * (m + degree - k)
            if m + degree >= k:
                assert log_change_lower >= 0
            else:
                assert log_change_lower < 0
            transitions += 1
        stages += 1

    # H=2^(2k) distinct dyadic anchors: minimize total raw address length by
    # filling levels 0,...,2k-1, then taking one address on level 2k.
    # This supplies a second direct check of the path-address lower bound.
    for k in range(16, 257):
        H = 1 << (2*k)
        minimum_sum = (2*k - 2) * H + 2 + 2*k
        assert minimum_sum >= k * H
        path_tests += 1

    # Check the total-refinement lower bound on representative synthetic
    # batches. This checks the additive implication, not graph realizability.
    batches = 0
    for k in [16, 17, 32, 64, 128, 256, 1024]:
        ell, beta, tau = coefficients(k)
        for size in [1, 2, 3, 8, 31]:
            ms = [0] * (size - 1) + [k * size]
            degrees = [(i % k) for i in range(size)]
            lower = sum((tau * (m+r-k) for m,r in zip(ms,degrees)), F(0))
            assert lower >= 0
            batches += 1

    # A sharp warning against replacing E[max] by max(E): one random index
    # holds a unit discrepancy, all others zero.
    first_moment_examples = 0
    for M in [2, 3, 4, 8, 32, 128]:
        expected_max = F(1)
        maximum_expectation = F(1, M)
        assert expected_max > maximum_expectation
        first_moment_examples += 1

    return {
        "status": "PASS",
        "exact_parameter_stages": stages,
        "exact_transition_identity_checks": transitions,
        "exact_distinct_address_checks": path_tests,
        "synthetic_batch_checks": batches,
        "first_moment_obstruction_examples": first_moment_examples,
        "scope": "Finite exact algebraic diagnostics only; no verification of all trajectories or locality.",
    }

if __name__ == '__main__':
    report = run()
    print(json.dumps(report, indent=2))
    Path(__file__).with_name('check_results.json').write_text(json.dumps(report, indent=2)+'\n')
