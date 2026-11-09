#!/usr/bin/env python3
"""Finite exact-rational diagnostics of refinement and comparison accounting.

These checks exercise the affine refinement bound, its use with the AM-GM
path-batch bound, negative degree gains, and the explicit +17 coefficient.
They do not prove the geometric or structural hypotheses, simulate full
adversary histories, or establish the inequalities for all parameters.
"""

import json
from fractions import Fraction
from pathlib import Path


def display(value):
    return {"exact": str(value), "decimal": float(value)}


def coefficients(j, k):
    alpha = 1 - Fraction(1, k)
    gamma_bound = 1 + Fraction(3, 2 * k)
    a = gamma_bound / alpha
    b = 4 * a + j + 1
    lam = a / (1 - b / (k + 1))
    sigma = b + 4 * (lam - a)
    loss_bound = 1 + Fraction(1, 2 * k)
    return alpha, gamma_bound, a, b, lam, sigma, loss_bound


def comparison_charges(j, k):
    _, _, _, _, lam, sigma, loss_bound = coefficients(j, k)
    charge = lam * loss_bound + sigma / k
    displayed_charge = 1 + Fraction(2 * j + 17, k)
    denominator = k * k - (j + 5) * k + j - 6
    numerator = 16 * k * k - (4 * j * j + 80 * j + 395) * k + 4 * j * j + 40 * j - 411
    return charge, displayed_charge, Fraction(numerator, 4 * k * denominator)


def refinement_examples(j, k):
    """Test boundary inputs for the affine contract and its three uses.

Path examples give mean costs at or above the AM-GM bound and the smallest
mean gains allowed by the affine contract. These are algebraic inputs,
not claims that a geometric state realizes each input.
    """
    alpha, gamma_bound, a, b, lam, sigma, _ = coefficients(j, k)
    counts = {"degree": 0, "narrow": 0, "path_batch": 0}
    minimum_slack = {}
    negative_degree_gains = 0
    shallow_narrow_anchors = 0
    for m in (0, 1, k - 2, k, 2 * k):
        cost = gamma_bound * m + j + 1
        degree_gain = alpha * m - 4
        degree_slack = lam * degree_gain + sigma - cost
        if degree_slack < 0:
            raise AssertionError((j, k, "degree", m, degree_gain, degree_slack))
        counts["degree"] += 1
        negative_degree_gains += degree_gain < 0
        minimum_slack["degree"] = min(minimum_slack.get("degree", degree_slack), degree_slack)

        narrow_gain = max(alpha * m - 4, k + Fraction(1, k))
        narrow_slack = lam * narrow_gain - cost
        if narrow_slack < 0:
            raise AssertionError((j, k, "narrow", m, narrow_gain, narrow_slack))
        counts["narrow"] += 1
        shallow_narrow_anchors += m <= 1
        minimum_slack["narrow"] = min(minimum_slack.get("narrow", narrow_slack), narrow_slack)

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
        "narrow_anchor_depth_zero_or_one": shallow_narrow_anchors,
        "minimum_rational_slack": {name: display(value) for name, value in minimum_slack.items()},
    }


def stage(j):
    k = 2**j
    alpha, gamma_bound, a, b, lam, sigma, loss_bound = coefficients(j, k)
    denominator = k * k - (j + 5) * k + j - 6
    charge, displayed_charge, slack = comparison_charges(j, k)
    polynomial = 4 * j * j + 80 * j + 395
    constant_term = 4 * j * j + 40 * j - 411
    checks = {
        "estimation_error_range": 0 < Fraction(1, 100 * k) < Fraction(1, 32),
        "affine_coefficient_identity": a == 1 + Fraction(5, 2 * (k - 1)),
        "affine_coefficient_positive": a >= 1 and b >= 1,
        "affine_coefficient_growth_bound": a <= 1 + Fraction(3, k),
        "affine_intercept_growth_bound": b <= j + 6,
        "path_budget_denominator_identity": k + 1 - b == Fraction(denominator, k - 1),
        "path_budget_denominator_positive": denominator > 0,
        "batch_factor_identity": lam == Fraction((k + 1) * (2 * k + 3), 2 * denominator),
        "narrow_factor_covered": lam >= a + b / k,
        "negative_gain_allowance_identity": sigma == j + 1 + 4 * lam,
        "am_gm_batch_boundary": lam * ((k + 1 - b) / a) == k + 1,
        "comparison_slack_identity": displayed_charge - charge == slack,
        "comparison_charge_upper_bound": charge <= displayed_charge,
        "comparison_residue_majorant": (j == 6 and slack > 0) or (j >= 7 and polynomial <= 16 * k and constant_term > 0),
        "polynomial_majorant_doubling": 4 * (j + 1)**2 + 80 * (j + 1) + 395 < 2 * polynomial,
        # Summing over the 2**m anchors at each depth cancels 2**(-m).
        "child_weight_probability_mass": Fraction(1, 2 * k) / (1 - alpha) == Fraction(1, 2),
        # ln 2 >= 56/81 follows from the first two positive terms of
        # 2*atanh(1/3). With -ln(1-x) <= x/(1-x), it supplies this
        # sufficient condition for gamma <= 1+3/(2k).
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
        "narrow_gain_coefficient_margin": display(lam - a - b / k),
        "rational_comparison_charge": display(charge),
        "displayed_comparison_charge": display(displayed_charge),
        "comparison_charge_slack": display(slack),
        "coefficient_from_rational_charge": display(1 / charge),
        "coefficient_from_displayed_charge": display(1 / displayed_charge),
        "checks": checks,
        "refinement_examples": refinement_examples(j, k),
    }


def slack_identity_grid():
    """Check the coefficient identity independently of the relation k=2**j."""
    count = 0
    skipped = []
    for j in range(17):
        for k in range(8, 129):
            denominator = k * k - (j + 5) * k + j - 6
            if denominator == 0:
                skipped.append({"j": j, "k": k, "reason": "zero denominator"})
                continue
            charge, displayed_charge, slack = comparison_charges(j, k)
            if displayed_charge - charge != slack:
                raise AssertionError({"j": j, "k": k, "check": "slack_identity"})
            count += 1
    return {
        "first_j": 0,
        "last_j": 16,
        "first_k": 8,
        "last_k": 128,
        "count": count,
        "skipped": skipped,
        "scope": "Identity only where its denominator is nonzero; this grid does not assert the comparison inequality when k is unrelated to 2**j.",
    }


def main():
    rows = [stage(j) for j in range(6, 129)]
    identity_grid = slack_identity_grid()
    stage_checks = sum(len(row["checks"]) for row in rows)
    example_counts = {
        name: sum(row["refinement_examples"]["counts"][name] for row in rows)
        for name in ("degree", "narrow", "path_batch")
    }
    examples = sum(example_counts.values())
    output = {
        "purpose": "Finite exact-rational diagnostics of the affine refinement contract, AM-GM batch accounting, and the +17 comparison coefficient; not a proof of structural or geometric hypotheses, all parameter values, or the adversary.",
        "range": {"first_j": 6, "last_j": 128, "count": len(rows)},
        "all_checks_passed": True,
        "checks_per_stage": len(rows[0]["checks"]),
        "stage_checks": stage_checks,
        "refinement_examples": {
            "counts": example_counts,
            "total": examples,
            "negative_degree_gains": sum(row["refinement_examples"]["negative_degree_gains"] for row in rows),
            "narrow_anchor_depth_zero_or_one": sum(row["refinement_examples"]["narrow_anchor_depth_zero_or_one"] for row in rows),
            "scope": "Synthetic costs and gains satisfying the affine and AM-GM inequalities; not full adversary trajectories or claims of geometric realizability.",
        },
        "slack_identity_grid": identity_grid,
        "total_checks": stage_checks + examples + identity_grid["count"],
        "coefficient_table": [row for row in rows if row["j"] in (6, 8, 10, 12, 16, 20)],
    }
    destination = Path(__file__).with_name("check_results.json")
    destination.write_text(json.dumps(output, indent=2) + "\n")
    keys = ("range", "all_checks_passed", "checks_per_stage", "stage_checks", "refinement_examples", "slack_identity_grid", "total_checks")
    print(json.dumps({key: output[key] for key in keys}, indent=2))
    print("j | k | rational charge | implied leading coefficient | stated coefficient")
    for row in output["coefficient_table"]:
        print(f"{row['j']} | {row['k']} | {row['rational_comparison_charge']['exact']} | "
              f"{row['coefficient_from_rational_charge']['decimal']:.12f} | "
              f"{row['coefficient_from_displayed_charge']['decimal']:.12f}")


if __name__ == "__main__":
    main()
