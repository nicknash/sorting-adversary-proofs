#!/usr/bin/env python3
"""Finite exact-rational checks of the refinement-count and depth accounting.

Section 4 proves the inequalities for every power of two k >= 64. This
script checks the resulting algebra on a finite grid, including the
coefficient residue as an identity in independently varied j and k.
It does not verify the structural, geometric, or locality hypotheses and
is not a proof of the adversary or of the inequalities for all parameters.
"""

import json
from fractions import Fraction
from pathlib import Path


def display(value):
    return {"exact": str(value), "decimal": float(value)}


def accounting_bounds(k):
    """Normalize q to one and eliminate P from the two inequalities."""
    denominator = k * k - 7 * k + 2
    depth_coefficient = 1 - Fraction(1, k) - Fraction(4, k - 2)
    depth_bound = Fraction((k + 5) * (k - 2), denominator)
    refinement_bound = Fraction(1, k) + depth_bound / (k - 2)
    return denominator, depth_coefficient, depth_bound, refinement_bound


def comparison_charges(j, k):
    denominator, _, depth_bound, refinement_bound = accounting_bounds(k)
    loss_bound = 1 + Fraction(1, k)
    charge = loss_bound + Fraction(2, k) * depth_bound + (j + 6) * refinement_bound
    displayed_charge = 1 + Fraction(2 * j + 18, k)
    residue = 3 * k * k - (12 * j + 113) * k + 2 * j + 42
    return charge, displayed_charge, Fraction(residue, k * denominator)


def stage(j):
    k = 2**j
    denominator, depth_coefficient, depth_bound, refinement_bound = accounting_bounds(k)
    loss_bound = 1 + Fraction(1, k)
    charge, displayed_charge, residue_fraction = comparison_charges(j, k)
    checks = {
        "estimation_error_range": 0 < Fraction(1, 100 * k) < Fraction(1, 32),
        "elimination_coefficient_identity": depth_coefficient == Fraction(denominator, k * (k - 2)),
        "elimination_coefficient_positive": depth_coefficient > 0,
        "depth_bound_from_elimination": depth_coefficient * depth_bound == 1 + Fraction(5, k),
        "depth_excess_identity": depth_bound - 1 == Fraction(10 * k - 12, denominator),
        "refinement_bound_identity": refinement_bound == Fraction(2 * (k * k - k + 1), k * denominator),
        "refinement_excess_identity": refinement_bound - Fraction(2, k) == Fraction(12 * k - 2, k * denominator),
        "extremal_volume_balance": (1 - Fraction(1, k)) * depth_bound == loss_bound + 4 * refinement_bound,
        "comparison_residue_identity": displayed_charge - charge == residue_fraction,
        "comparison_charge_upper_bound": charge <= displayed_charge,
        # This sufficient inequality makes the residue positive; Section 4
        # proves it at j=6 and observes its increase at every later integer j.
        "residue_positive_majorant": 3 * k >= 12 * j + 113,
        # -ln(1-x) <= x/(1-x), ln 2 >= 1/2, and x=1/(50k)
        # give a rational sufficient condition for a_eta <= 1+1/k.
        "comparison_loss_rational_majorant": Fraction(2, 50 * k - 1) <= Fraction(1, k),
    }
    if not all(checks.values()):
        raise AssertionError({"j": j, "checks": checks})
    return {
        "j": j,
        "k": k,
        "total_depth_per_comparison_bound": display(depth_bound),
        "refinements_per_comparison_bound": display(refinement_bound),
        "rational_comparison_charge": display(charge),
        "displayed_comparison_charge": display(displayed_charge),
        "comparison_charge_slack": display(displayed_charge - charge),
        "coefficient_from_rational_charge": display(1 / charge),
        "coefficient_from_displayed_charge": display(1 / displayed_charge),
        "checks": checks,
    }


def residue_identity_grid():
    """Check the residue formula independently of the relation k=2**j."""
    count = 0
    for j in range(17):
        for k in range(8, 129):
            charge, displayed_charge, residue_fraction = comparison_charges(j, k)
            if displayed_charge - charge != residue_fraction:
                raise AssertionError({"j": j, "k": k, "check": "residue_identity"})
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
    identity_grid = residue_identity_grid()
    stage_checks = sum(len(row["checks"]) for row in rows)
    output = {
        "purpose": "Finite exact-rational diagnostic of the two accounting inequalities and the +18 comparison coefficient; not a proof of the structural, geometric, or locality hypotheses or of the adversary.",
        "range": {"first_j": 6, "last_j": 128, "count": len(rows)},
        "all_checks_passed": True,
        "checks_per_stage": len(rows[0]["checks"]),
        "stage_checks": stage_checks,
        "residue_identity_grid": identity_grid,
        "total_checks": stage_checks + identity_grid["count"],
        "coefficient_table": [row for row in rows if row["j"] in (6, 8, 10, 12, 16, 20)],
    }
    destination = Path(__file__).with_name("check_results.json")
    destination.write_text(json.dumps(output, indent=2) + "\n")
    keys = ("range", "all_checks_passed", "checks_per_stage", "stage_checks", "residue_identity_grid", "total_checks")
    print(json.dumps({key: output[key] for key in keys}, indent=2))
    print("j | k | rational charge | implied leading coefficient | stated coefficient")
    for row in output["coefficient_table"]:
        print(f"{row['j']} | {row['k']} | {row['rational_comparison_charge']['exact']} | "
              f"{row['coefficient_from_rational_charge']['decimal']:.12f} | "
              f"{row['coefficient_from_displayed_charge']['decimal']:.12f}")


if __name__ == "__main__":
    main()
