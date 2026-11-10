#!/usr/bin/env python3
"""Finite exact-rational diagnostics of refinement rarity and accounting.

These checks exercise the affine cost contract, AM-GM path batches,
signed degree gains, and the final comparison bound. Non-power-of-two
parameters use a conservative integer bound on log2(k). The checks do not
prove the geometric or structural hypotheses, simulate adversary histories,
or establish the inequalities for all parameters.
"""

import json
from fractions import Fraction
from pathlib import Path


def display(value):
    return {"exact": str(value), "decimal": float(value)}


def coefficients(log_bound, k):
    """Use log_bound >= log2(k); equality holds at power-of-two stages."""
    alpha = 1 - Fraction(1, k)
    gamma_bound = 1 + Fraction(3, 2 * k)
    a = 1 + Fraction(3, k)
    b = 4 * a + log_bound + 1
    loss_bound = 1 + Fraction(1, 2 * k)
    degree_gain_floor = -b / a
    path_mean_gain = (k + 1 - b) / a
    # Normalize q to one. Degree moves number at most 1/k; other moves
    # contribute at least k/2 each, while total gain is at most loss_bound.
    refinement_bound = (1 + 2 * loss_bound + 2 * b / (a * k)) / k
    charge = a * loss_bound + b * refinement_bound
    rescaled_charge = charge + (log_bound - 1) * refinement_bound
    return {
        "alpha": alpha,
        "gamma_bound": gamma_bound,
        "a": a,
        "b": b,
        "loss_bound": loss_bound,
        "degree_gain_floor": degree_gain_floor,
        "path_mean_gain": path_mean_gain,
        "refinement_bound": refinement_bound,
        "charge": charge,
        "rescaled_charge": rescaled_charge,
    }


def coefficient_checks(log_bound, k):
    c = coefficients(log_bound, k)
    alpha, gamma, a, b, loss = (c[name] for name in
                               ("alpha", "gamma_bound", "a", "b", "loss_bound"))
    checks = {
        "certificate_tolerance_range": 0 < Fraction(1, 100 * k) < Fraction(1, 32),
        "affine_slope_dominates_anchor_cost": a >= gamma / alpha,
        "affine_slope_growth": a - 1 == Fraction(3, k),
        "affine_intercept_growth": 1 <= b <= log_bound + 6,
        "negative_gain_floor_from_nonnegative_cost": a * c["degree_gain_floor"] + b == 0,
        "am_gm_path_mean_gain": a * c["path_mean_gain"] + b == k + 1,
        "path_mean_gain_at_least_half_k": c["path_mean_gain"] >= Fraction(k, 2),
        "rarity_bound_saturates_worst_signed_gain":
            Fraction(k, 2) * (c["refinement_bound"] - Fraction(1, k))
            - b / (a * k) == loss,
        "rarity_bound_at_most_four_over_k": c["refinement_bound"] <= Fraction(4, k),
        "remaining_volume_term_has_correct_sign": a >= 1,
        "comparison_loss_product_growth": a * loss <= 1 + Fraction(4, k),
        "comparison_coefficient_growth":
            1 <= c["charge"] <= 1 + Fraction(4 * log_bound + 28, k),
        # Summing over the 2**m anchors cancels the factor 2**(-m).
        "child_weights_sum_to_one_half": Fraction(1, 2 * k) / (1 - alpha) == Fraction(1, 2),
        "rescaled_child_weights_sum_to_one_over_k":
            Fraction(1, k * k) / (1 - alpha) == Fraction(1, k),
        "rescaled_comparison_coefficient_growth":
            1 <= c["rescaled_charge"] <= 1 + Fraction(8 * log_bound + 24, k),
        # ln 2 >= 56/81 follows from two terms of 2*atanh(1/3).
        # Combining this with -ln(1-x) <= x/(1-x) bounds gamma.
        "anchor_cost_logarithm_majorant": Fraction(81, 56 * (k - 1)) <= gamma - 1,
        # -log2(1-1/(50k)) <= 2/(50k-1), using ln 2 >= 1/2.
        "comparison_loss_logarithm_majorant": Fraction(2, 50 * k - 1) <= loss - 1,
    }
    if not all(checks.values()):
        raise AssertionError({"k": k, "log_bound": log_bound, "checks": checks})
    return c, checks


def signed_accounting_examples(log_bound, k):
    """Check normalized mixtures at the boundaries of the rarity argument.

Counts may be fractional: q is normalized to one. These examples test
only the accounting implications of the stated contracts. They do not
assert that a particular adversary execution realizes the inputs.
    """
    c = coefficients(log_bound, k)
    a, b, loss = (c[name] for name in ("a", "b", "loss_bound"))
    count = negative_degree_cases = negative_final_log_volume_cases = 0
    minimum_rarity_slack = minimum_comparison_slack = None
    for degree_count in (Fraction(0), Fraction(1, 2 * k), Fraction(1, k)):
        for degree_gain in (c["degree_gain_floor"], c["degree_gain_floor"] / 2,
                            Fraction(0), Fraction(2)):
            for other_mean_gain in (c["path_mean_gain"], k + Fraction(1, k), 2 * k):
                for final_log_volume in (Fraction(0), -loss / 2):
                    total_gain = final_log_volume + loss
                    other_count = (total_gain - degree_count * degree_gain) / other_mean_gain
                    if other_count < 0:
                        raise AssertionError("The test inputs require a negative count")
                    refinement_count = degree_count + other_count
                    degree_cost = a * degree_gain + b
                    other_mean_cost = a * other_mean_gain + b
                    total_cost = degree_count * degree_cost + other_count * other_mean_cost
                    rarity_slack = c["refinement_bound"] - refinement_count
                    # The volume contribution left after paying child costs
                    # must be at least minus the advertised comparison charge.
                    comparison_slack = final_log_volume - total_cost + c["charge"]
                    checks = (
                        degree_cost >= 0,
                        other_mean_gain >= Fraction(k, 2),
                        total_gain >= Fraction(k, 2) * other_count - b / a * degree_count,
                        total_cost == a * total_gain + b * refinement_count,
                        rarity_slack >= 0,
                        comparison_slack >= 0,
                        # Supplementary counting pays log2(k/2) per move.
                        # log_bound - 1 is exact at the power-of-two stages.
                        final_log_volume - total_cost
                        - (log_bound - 1) * refinement_count + c["rescaled_charge"] >= 0,
                    )
                    if not all(checks):
                        raise AssertionError({"k": k, "degree_count": str(degree_count),
                                              "degree_gain": str(degree_gain), "checks": checks})
                    count += 1
                    negative_degree_cases += degree_count > 0 and degree_gain < 0
                    negative_final_log_volume_cases += final_log_volume < 0
                    minimum_rarity_slack = (rarity_slack if minimum_rarity_slack is None
                                            else min(minimum_rarity_slack, rarity_slack))
                    minimum_comparison_slack = (comparison_slack if minimum_comparison_slack is None
                                                else min(minimum_comparison_slack, comparison_slack))
    return {
        "count": count,
        "checks_per_case": len(checks),
        "negative_degree_gain_cases": negative_degree_cases,
        "negative_final_log_volume_cases": negative_final_log_volume_cases,
        "minimum_rarity_slack": display(minimum_rarity_slack),
        "minimum_comparison_slack": display(minimum_comparison_slack),
    }


def stage(j):
    k = 2**j
    c, checks = coefficient_checks(j, k)
    return {
        "j": j,
        "k": k,
        "affine_cost_slope": display(c["a"]),
        "affine_cost_intercept": display(c["b"]),
        "minimum_path_mean_gain": display(c["path_mean_gain"]),
        "derived_degree_gain_floor": display(c["degree_gain_floor"]),
        "refinements_per_comparison_bound": display(c["refinement_bound"]),
        "rational_comparison_charge": display(c["charge"]),
        "rescaled_prefix_comparison_charge": display(c["rescaled_charge"]),
        "coefficient_from_rational_charge": display(1 / c["charge"]),
        "checks": checks,
        "signed_accounting_examples": signed_accounting_examples(j, k),
    }


def integer_parameter_grid():
    """Check all coefficients with ceil(log2(k)) at every integer k."""
    count = nonpowers = 0
    for k in range(64, 4097):
        _, checks = coefficient_checks((k - 1).bit_length(), k)
        count += 1
        nonpowers += k & (k - 1) != 0
    return {
        "first_k": 64,
        "last_k": 4096,
        "count": count,
        "checks_per_case": len(checks),
        "non_power_of_two_cases": nonpowers,
        "scope": "All coefficient inequalities checked exactly at each integer, using ceil(log2(k)) as a conservative rational bound; a finite check only.",
    }


def cutoff_grid():
    """Compare the cutoff with exact factorial information counts."""
    factorial = 1
    for n in range(1, 257):
        factorial *= n
        cutoff = n * (n - 1).bit_length()
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
    integers, cutoffs = integer_parameter_grid(), cutoff_grid()
    stage_checks = sum(len(row["checks"]) for row in rows)
    examples = {
        key: sum(row["signed_accounting_examples"][key] for row in rows)
        for key in ("count", "negative_degree_gain_cases", "negative_final_log_volume_cases")
    }
    examples["checks_per_case"] = rows[0]["signed_accounting_examples"]["checks_per_case"]
    examples["scope"] = "Synthetic normalized mixtures satisfying the affine and gain inequalities; not adversary trajectories or claims of geometric realizability."
    total_checks = (stage_checks + examples["count"] * examples["checks_per_case"]
                    + integers["count"] * integers["checks_per_case"] + cutoffs["count"])
    output = {
        "purpose": "Finite exact-rational diagnostics of refinement rarity, signed gains, affine costs, AM-GM path batches, original and rescaled prefix accounting, and the cutoff; not a proof of geometric or structural hypotheses.",
        "range": {"first_j": 6, "last_j": 128, "count": len(rows)},
        "all_checks_passed": True,
        "checks_per_stage": len(rows[0]["checks"]),
        "stage_checks": stage_checks,
        "signed_accounting_examples": examples,
        "integer_parameter_grid": integers,
        "cutoff_grid": cutoffs,
        "total_diagnostic_cases": len(rows) + examples["count"] + integers["count"] + cutoffs["count"],
        "total_exact_inequality_checks": total_checks,
        "coefficient_table": [row for row in rows if row["j"] in (6, 8, 10, 12, 16, 20)],
    }
    destination = Path(__file__).with_name("check_results.json")
    destination.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({key: value for key, value in output.items() if key != "coefficient_table"}, indent=2))
    print("j | k | rational charge | implied leading coefficient")
    for row in output["coefficient_table"]:
        print(f"{row['j']} | {row['k']} | {row['rational_comparison_charge']['exact']} | "
              f"{row['coefficient_from_rational_charge']['decimal']:.12f}")


if __name__ == "__main__":
    main()
