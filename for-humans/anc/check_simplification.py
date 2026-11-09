#!/usr/bin/env python3
"""Finite exact-rational diagnostics of the direct volume-gain accounting.

Section 4 proves the inequalities for every power of two k >= 64. This
script checks its rational bounds on a finite parameter grid, checks the
final coefficient identity with j and k varied independently, and exercises
the three refinement bounds on synthetic gains satisfying their hypotheses.
It does not verify the geometric or structural hypotheses, simulate full
adversary histories, or prove the inequalities for all parameters.
"""

import json
from fractions import Fraction
from pathlib import Path


def display(value):
    return {"exact": str(value), "decimal": float(value)}


def coefficients(j, k):
    """Rational upper bounds for the comparison loss and child depth cost."""
    alpha = 1 - Fraction(1, k)
    lam = 1 + Fraction(j + 10, k)
    gamma_bound = 1 + Fraction(3, 2 * k)
    loss_bound = 1 + Fraction(1, 2 * k)
    return alpha, lam, gamma_bound, loss_bound


def comparison_charges(j, k):
    _, lam, _, loss_bound = coefficients(j, k)
    charge = lam * loss_bound + Fraction(j + 6, k)
    displayed_charge = 1 + Fraction(2 * j + 17, k)
    slack = Fraction(k - j - 10, 2 * k * k)
    return charge, displayed_charge, slack


def refinement_examples(j, k):
    """Test boundary gains, including negative degree gains and shallow anchors.

The path examples specify averages over an entire batch; their depth
averages obey the distinct-anchor bound. They are algebra inputs, not
assertions that a particular geometric state realizes each input.
    """
    alpha, lam, gamma_bound, _ = coefficients(j, k)
    counts = {"degree": 0, "narrow": 0, "path_batch": 0}
    minimum_slack = {}
    negative_degree_gains = 0
    shallow_narrow_anchors = 0
    for m in (0, 1, k - 2, k, 2 * k):
        cost = gamma_bound * m + j + 1
        degree_gain = alpha * m - 4
        degree_slack = lam * degree_gain + j + 6 - cost
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

    for mean_depth in (k - 2, k, 2 * k):
        mean_gain = alpha * mean_depth - 4
        mean_cost = gamma_bound * mean_depth + j + 1
        path_slack = lam * mean_gain - mean_cost
        if path_slack < 0:
            raise AssertionError((j, k, "path_batch", mean_depth, mean_gain, path_slack))
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
    alpha, lam, gamma_bound, loss_bound = coefficients(j, k)
    delta_bound = lam * alpha - gamma_bound
    degree_margin = 5 - 4 * lam
    narrow_margin = delta_bound * k - 4 * gamma_bound - alpha * (j + 1)
    path_margin = delta_bound * (k - 2) - 4 * lam - j - 1
    charge, displayed_charge, slack = comparison_charges(j, k)
    checks = {
        "estimation_error_range": 0 < Fraction(1, 100 * k) < Fraction(1, 32),
        "gain_coefficient_range": 1 < lam <= Fraction(5, 4),
        "depth_difference_identity": delta_bound == Fraction(2 * j + 15, 2 * k) - Fraction(j + 10, k * k),
        "depth_difference_positive": delta_bound > 0,
        "degree_allowance_margin_identity": degree_margin == 1 - Fraction(4 * (j + 10), k),
        "degree_allowance_margin_nonnegative": degree_margin >= 0,
        "narrow_margin_identity": narrow_margin == Fraction(5, 2) - Fraction(15, k),
        "narrow_margin_positive": narrow_margin > 0,
        "path_margin_identity": path_margin == Fraction(5, 2) - Fraction(7 * j + 65, k) + Fraction(2 * (j + 10), k * k),
        "path_margin_positive": path_margin > 0,
        "path_margin_sufficient_inequality": 7 * j + 65 <= 2 * k,
        "comparison_slack_identity": displayed_charge - charge == slack,
        "comparison_charge_upper_bound": charge <= displayed_charge,
        # Half the probability starts a walk; its stopping depth is geometric
        # with parameter 1/k. The 2**m anchor choices cancel 2**(-m).
        "anchor_walk_probability_mass": Fraction(1, 2 * k) / (1 - alpha) == Fraction(1, 2),
        # ln 2 >= 2*(1/3 + (1/3)**3/3) = 56/81, from the first
        # two positive terms of the logarithm series. Combined with
        # -ln(1-x) <= x/(1-x), this bounds gamma-1 by 3/(2k).
        "anchor_depth_logarithm_majorant": Fraction(81, 56 * (k - 1)) <= gamma_bound - 1,
        # The same log inequality and ln 2 >= 1/2 give
        # -log2(1-1/(50k)) <= 2/(50k-1) <= 1/(2k).
        "comparison_loss_rational_majorant": Fraction(2, 50 * k - 1) <= loss_bound - 1,
    }
    if not all(checks.values()):
        raise AssertionError({"j": j, "checks": checks})
    return {
        "j": j,
        "k": k,
        "volume_gain_coefficient": display(lam),
        "anchor_depth_cost_majorant": display(gamma_bound),
        "degree_allowance_margin": display(degree_margin),
        "narrow_refinement_margin": display(narrow_margin),
        "path_batch_margin_per_refinement": display(path_margin),
        "rational_comparison_charge": display(charge),
        "displayed_comparison_charge": display(displayed_charge),
        "comparison_charge_slack": display(slack),
        "coefficient_from_rational_charge": display(1 / charge),
        "coefficient_from_displayed_charge": display(1 / displayed_charge),
        "checks": checks,
        "refinement_examples": refinement_examples(j, k),
    }


def slack_identity_grid():
    """Check the final coefficient identity without requiring k=2**j."""
    count = 0
    for j in range(17):
        for k in range(8, 129):
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
        "scope": "Identity only; this grid does not assert the comparison inequality when k is unrelated to 2**j.",
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
        "purpose": "Finite exact-rational diagnostics of direct volume-gain charges and the +17 comparison coefficient; not a proof of the structural or geometric hypotheses, of all parameter values, or of the adversary.",
        "range": {"first_j": 6, "last_j": 128, "count": len(rows)},
        "all_checks_passed": True,
        "checks_per_stage": len(rows[0]["checks"]),
        "stage_checks": stage_checks,
        "refinement_examples": {
            "counts": example_counts,
            "total": examples,
            "negative_degree_gains": sum(row["refinement_examples"]["negative_degree_gains"] for row in rows),
            "narrow_anchor_depth_zero_or_one": sum(row["refinement_examples"]["narrow_anchor_depth_zero_or_one"] for row in rows),
            "scope": "Synthetic gains satisfying the anchor inequalities; not full adversary trajectories or claims of geometric realizability.",
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
