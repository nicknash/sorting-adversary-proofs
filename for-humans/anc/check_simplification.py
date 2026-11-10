#!/usr/bin/env python3
"""Exact finite checks of refinement rarity and transcript counting."""
from fractions import Fraction
from itertools import permutations
import json
from math import factorial
from pathlib import Path


def check_accounting(k):
    # At least half the anchors in a path repair have m >= k - 1.
    mean_path_gain = (1 - Fraction(1, k)) * Fraction(k - 1, 2) - 4
    assert mean_path_gain >= Fraction(k, 4)
    # Use -log2(1-u) <= 2u/(1-u) for the comparison and stopping losses.
    answer_loss = 1 + Fraction(2, 50 * k - 1)
    stopping_loss = Fraction(2, k - 1)
    assert 4 * answer_loss + 1 + Fraction(16, k) <= 8
    assert Fraction(1, k * k) / (1 - (1 - Fraction(1, k))) == Fraction(1, k)
    # Upper bounds for a, b and delta, including the s <= 2q charge.
    a = (1 + stopping_loss) / (1 - Fraction(1, k))
    log_k_upper = (k - 1).bit_length()
    b = 4 * a + 2 * log_k_upper
    delta = a * answer_loss - 1 + 2 * stopping_loss + 8 * b / k
    assert 0 <= delta <= Fraction(24 * log_k_upper + 60, k)

    # Check the sign of the leftover volume term with a negative degree gain.
    comparisons = k
    degree_moves = 1
    other_moves = (answer_loss * comparisons + 4) / mean_path_gain
    moves = degree_moves + other_moves
    assert moves <= Fraction(8 * comparisons, k)
    for final_log_volume in (Fraction(0), -answer_loss):
        gain = final_log_volume + answer_loss * comparisons
        cost = a * gain + b * moves
        assert final_log_volume - cost - 2 * comparisons * stopping_loss >= -(1 + delta) * comparisons


def check_insertions():
    """A block can exclude orders allowed by the transcript."""
    cases = 0
    for n in range(3, 8):
        orders = list(permutations(range(n)))
        for s in range(2, n):
            # Queried labels 0..s-1 form an ordered block. The other
            # labels have never been compared and can be inserted freely.
            compatible = [order for order in orders
                          if tuple(x for x in order if x < s) == tuple(range(s))]
            represented = [order for order in compatible
                           if order.index(s - 1) - order.index(0) == s - 1]
            assert len(compatible) == factorial(n) // factorial(s)
            assert len(represented) < len(compatible)
            cases += 1
    return cases


def main():
    stages = [*range(64, 4097), *(2**j for j in range(13, 129))]
    for k in stages:
        check_accounting(k)
    for n in range(1, 257):
        assert n * (n - 1).bit_length() >= (factorial(n) - 1).bit_length()
    report = {
        "status": "passed",
        "accounting_parameter_cases": len(stages),
        "untouched_label_insertion_cases": check_insertions(),
        "horizon_cases": 256,
        "scope": "Finite checks of the revised inequalities and counts, without simulating full adversary trajectories.",
    }
    Path(__file__).with_name("check_results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report))


if __name__ == "__main__":
    main()
