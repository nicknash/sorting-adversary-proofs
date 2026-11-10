#!/usr/bin/env python3
"""Finite exact-rational diagnostics of refinement and comparison accounting.

These checks cover the affine cost contract, large gains following failed
comparison certification, AM-GM batch accounting, and signed degree gains.
A conservative logarithm bound also checks non-power-of-two parameters.
They do not prove the geometric or structural hypotheses, simulate full
adversary histories, or establish the inequalities for all parameters.
"""

import json
from fractions import Fraction
from pathlib import Path


def display(value):
    return {"exact": str(value), "decimal": float(value)}


def coefficients(log_bound, k):
    """Use log_bound >= log2(k); it is exact on the power-of-two stages."""
    alpha = 1 - Fraction(1, k)
    gamma_bound = 1 + Fraction(3, 2 * k)
    a = 1 + Fraction(3, k)
    b = 4 * a + log_bound + 1
    lam = a / (1 - b / (k + 1))
    sigma = b + 4 * (lam - a)
    loss_bound = 1 + Fraction(1, 2 * k)
    return alpha, gamma_bound, a, b, lam, sigma, loss_bound


def refinement_examples(j, k):
    """Exercise boundary inputs for the affine contract and its three uses.

Path examples use mean costs at or above the AM-GM bound and the smallest
mean gains allowed by the affine contract. These are algebraic inputs,
not claims that a geometric state realizes each input.
    """
    alpha, gamma_bound, a, b, lam, sigma, _ = coefficients(j, k)
    counts = {"degree": 0, "failed_certification": 0, "path_batch": 0}
    minimum_slack = {}
    negative_degree_gains = 0
    shallow_failure_anchors = 0
    for m in (0, 1, k - 2, k, 2 * k):
        cost = gamma_bound * m + j + 1
        degree_gain = alpha * m - 4
        degree_slack = lam * degree_gain + sigma - cost
        if cost > a * degree_gain + b or degree_slack < 0:
            raise AssertionError((j, k, "degree", m, degree_gain, degree_slack))
        counts["degree"] += 1
        negative_degree_gains += degree_gain < 0
        minimum_slack["degree"] = min(minimum_slack.get("degree", degree_slack), degree_slack)

        failure_gain = max(alpha * m - 4, k + Fraction(1, k))
        failure_slack = lam * failure_gain - cost
        if cost > a * failure_gain + b or failure_slack < 0:
            raise AssertionError((j, k, "failed_certification", m, failure_gain, failure_slack))
        counts["failed_certification"] += 1
        shallow_failure_anchors += m <= 1
        minimum_slack["failed_certification"] = min(minimum_slack.get("failed_certification", failure_slack), failure_slack)

    for mean_cost in (k + 1, k + 2, 2 * (k + 1)):
        mean_gain = (mean_cost - b) / a
        path_slack = lam * mean_gain - mean_cost
        if path_slack < 0:
            raise AssertionError((j, k, "path_batch", mean_cost, mean_gain, path_slack))
        counts["path_batch"] += 1
        minimum_slack["path_batch"] = min(minimum_slack.get("path_batch", path_slack), path_slack)
    return {
        "counts": counts,
        "negative_degree_gains": negative_degree_gains,
        "failure_anchor_depth_zero_or_one": shallow_failure_anchors,
        "minimum_rational_slack": {name: display(value) for name, value in minimum_slack.items()},
    }


def stage(j):
    k = 2**j
    alpha, gamma_bound, a, b, lam, sigma, loss_bound = coefficients(j, k)
    charge = lam * loss_bound + sigma / k
    growth_envelope = 1 + Fraction(5 * (j + 9), k)
    checks = {
        "certificate_tolerance_range": 0 < Fraction(1, 100 * k) < Fraction(1, 32),
        "affine_slope_identity": a - 1 == Fraction(3, k),
        "affine_slope_dominates_anchor_cost": a >= gamma_bound / alpha,
        "affine_intercept_identity": b - j == 5 + Fraction(12, k),
        "affine_intercept_growth_bound": 1 <= b <= j + 6,
        "batch_denominator_bounded_away_from_zero": b <= Fraction(k + 1, 2),
        "failure_gain_factor_covered": lam >= a + b / k,
        "negative_gain_allowance_boundary": a * (-4) + b == lam * (-4) + sigma,
        "am_gm_batch_boundary": lam * ((k + 1 - b) / a) == k + 1,
        "remaining_volume_term_has_correct_sign": lam >= 1,
        "batch_coefficient_growth_bound": lam - 1 <= Fraction(2 * (j + 9), k),
        "degree_allowance_growth_bound": sigma <= 2 * (j + 9),
        "comparison_coefficient_growth_bound": 1 <= charge <= growth_envelope,
        # Summing over the 2**m anchors at depth m cancels 2**(-m).
        "child_weight_probability_mass": Fraction(1, 2 * k) / (1 - alpha) == Fraction(1, 2),
        # ln 2 >= 56/81, from the first two positive terms of 2*atanh(1/3),
        # and -ln(1-x) <= x/(1-x) imply this sufficient logarithm bound.
        "anchor_depth_logarithm_majorant": Fraction(81, 56 * (k - 1)) <= gamma_bound - 1,
        # -log2(1-1/(50k)) <= 2/(50k-1), using ln 2 >= 1/2.
        "comparison_loss_rational_majorant": Fraction(2, 50 * k - 1) <= loss_bound - 1,
    }
    if not all(checks.values()):
        raise AssertionError({"j": j, "checks": checks})
    return {
        "j": j,
        "k": k,
        "anchor_depth_cost_majorant": display(gamma_bound),
        "affine_cost_slope": display(a),
        "affine_cost_intercept": display(b),
        "batch_gain_coefficient": display(lam),
        "degree_refinement_allowance": display(sigma),
        "failure_gain_coefficient_margin": display(lam - a - b / k),
        "rational_comparison_charge": display(charge),
        "comparison_growth_envelope": display(growth_envelope),
        "coefficient_from_rational_charge": display(1 / charge),
        "checks": checks,
        "refinement_examples": refinement_examples(j, k),
    }


def integer_parameter_grid():
    """Use ceil(log2(k)) to check conservative bounds at every integer k."""
    count = 0
    nonpowers = 0
    for k in range(64, 4097):
        log_bound = (k - 1).bit_length()
        alpha, gamma_bound, a, b, lam, sigma, loss_bound = coefficients(log_bound, k)
        charge = lam * loss_bound + sigma / k
        checks = (
            gamma_bound / alpha <= a,
            1 <= b <= Fraction(k + 1, 2),
            lam >= a + b / k,
            a * (-4) + b == lam * (-4) + sigma,
            charge <= 1 + Fraction(5 * (log_bound + 9), k),
        )
        if not all(checks):
            raise AssertionError({"k": k, "log_bound": log_bound, "checks": checks})
        count += 1
        nonpowers += k & (k - 1) != 0
    return {
        "first_k": 64,
        "last_k": 4096,
        "count": count,
        "non_power_of_two_cases": nonpowers,
        "scope": "Five exact coefficient conditions per integer-parameter case, using ceil(log2(k)) as a conservative rational bound; a finite check only.",
    }


def cutoff_grid():
    """Compare the proposed cutoff with exact factorial information counts."""
    factorial = 1
    for n in range(1, 257):
        factorial *= n
        cutoff = n * (n - 1).bit_length()
        # ceil(log2(n!)) is computed from the exact integer factorial.
        if cutoff < (factorial - 1).bit_length():
            raise AssertionError({"n": n, "cutoff": cutoff})
    return {
        "first_n": 1,
        "last_n": 256,
        "count": 256,
        "scope": "The cutoff is at least ceil(log2(n!)); this does not test the lifetime or correctness of an adversary trajectory.",
    }


def main():
    rows = [stage(j) for j in range(6, 129)]
    integers = integer_parameter_grid()
    cutoffs = cutoff_grid()
    stage_checks = sum(len(row["checks"]) for row in rows)
    example_counts = {
        name: sum(row["refinement_examples"]["counts"][name] for row in rows)
        for name in ("degree", "failed_certification", "path_batch")
    }
    examples = sum(example_counts.values())
    output = {
        "purpose": "Finite exact-rational diagnostics of affine refinement costs, large gains after unsuccessful certification, AM-GM accounting, asymptotic coefficient growth, and the comparison cutoff; not a proof of the adversary or its geometric and structural hypotheses.",
        "range": {"first_j": 6, "last_j": 128, "count": len(rows)},
        "all_checks_passed": True,
        "checks_per_stage": len(rows[0]["checks"]),
        "stage_checks": stage_checks,
        "refinement_examples": {
            "counts": example_counts,
            "total": examples,
            "negative_degree_gains": sum(row["refinement_examples"]["negative_degree_gains"] for row in rows),
            "failure_anchor_depth_zero_or_one": sum(row["refinement_examples"]["failure_anchor_depth_zero_or_one"] for row in rows),
            "scope": "Synthetic costs and gains satisfying the affine and AM-GM inequalities; not full adversary trajectories or claims of geometric realizability.",
        },
        "integer_parameter_grid": integers,
        "cutoff_grid": cutoffs,
        "total_diagnostic_cases": stage_checks + examples + integers["count"] + cutoffs["count"],
        "coefficient_table": [row for row in rows if row["j"] in (6, 8, 10, 12, 16, 20)],
    }
    destination = Path(__file__).with_name("check_results.json")
    destination.write_text(json.dumps(output, indent=2) + "\n")
    keys = ("range", "all_checks_passed", "checks_per_stage", "stage_checks", "refinement_examples", "integer_parameter_grid", "cutoff_grid", "total_diagnostic_cases")
    print(json.dumps({key: output[key] for key in keys}, indent=2))
    print("j | k | rational charge | implied leading coefficient")
    for row in output["coefficient_table"]:
        print(f"{row['j']} | {row['k']} | {row['rational_comparison_charge']['exact']} | "
              f"{row['coefficient_from_rational_charge']['decimal']:.12f}")


if __name__ == "__main__":
    main()
