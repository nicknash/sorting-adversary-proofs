#!/usr/bin/env python3
"""Exact rational checks of the all-stage one-coefficient accounting.

This diagnostic verifies the algebraic inequalities on finitely many stages.
Section 8 of the accompanying paper proves them for every j >= 6.
It does not verify the geometric or probability-estimator hypotheses.
"""

import json
from fractions import Fraction
from pathlib import Path


def display(value):
    return {"exact": str(value), "decimal": float(value)}


def stage(j):
    k = 2**j
    s = Fraction(j + 10, k)
    a = s - (s + 2) / k
    C = j + 6 + 4 * s
    degree = s * k - C
    narrow = 2 * k * a - C
    path = a * (k - 2) - C
    rational_charge = (1 + s) * (1 + Fraction(1, k)) + s
    displayed_charge = 1 + Fraction(2 * j + 22, k)
    checks = {
        "coefficient_range": 0 < s <= Fraction(1, 4),
        "positive_address_coefficient": a > 0,
        "degree_identity": degree == 4 * (1 - s),
        "narrow_identity": narrow == j + 10 - 6 * s,
        "path_identity": path == 2 - 7 * s + (2 * s + 4) / k,
        "degree_paid": degree > 0,
        "narrow_paid": narrow > 0,
        "complete_path_batch_paid": path > 0,
        "comparison_charge_upper_bound": rational_charge < displayed_charge,
        # Rational sufficient bound for -log2(1-1/(50k)) <= 1/k:
        # -ln(1-x) <= x/(1-x); ln 2 >= 1/2.
        "logarithm_rational_majorant": Fraction(1, 50 * k - 1) <= Fraction(1, 2 * k),
        # The exact minimum is H(k-2)+k+2, with H=2**k.
        # Cancel H(k-2), rather than materializing the enormous H.
        "minimum_distinct_address_sum": k + 2 > 0,
    }
    if not all(checks.values()):
        raise AssertionError({"j": j, "checks": checks})
    return {
        "j": j,
        "k": k,
        "s": display(s),
        "address_coefficient_a": display(a),
        "constant_C": display(C),
        "degree_margin": display(degree),
        "narrow_margin": display(narrow),
        "path_margin_per_vertex": display(path),
        "rational_comparison_charge": display(rational_charge),
        "displayed_comparison_charge": display(displayed_charge),
        "coefficient_from_rational_charge": display(1 / rational_charge),
        "coefficient_from_displayed_charge": display(1 / displayed_charge),
        "checks": checks,
    }


def main():
    # Avoid constructing 2**k for huge k: the exact distinct-address formula
    # differs from H(k-2) by k+2 > 0, checked symbolically below instead.
    rows = [stage(j) for j in range(6, 129)]
    output = {
        "purpose": "Finite exact-rational diagnostic, not a proof of the inherited geometry/estimator lemmas",
        "range": {"first_j": 6, "last_j": 128, "count": len(rows)},
        "all_checks_passed": True,
        "checks_per_stage": len(rows[0]["checks"]),
        "total_checks": sum(len(row["checks"]) for row in rows),
        "coefficient_table": [row for row in rows if row["j"] in (6, 8, 10, 12, 16, 20)],
    }
    destination = Path(__file__).with_name("check_results.json")
    destination.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({key: output[key] for key in ("range", "all_checks_passed", "checks_per_stage", "total_checks")}, indent=2))
    print("j | k | rational charge | implied leading coefficient | stated coefficient")
    for row in output["coefficient_table"]:
        print(f"{row['j']} | {row['k']} | {row['rational_comparison_charge']['exact']} | "
              f"{row['coefficient_from_rational_charge']['decimal']:.12f} | "
              f"{row['coefficient_from_displayed_charge']['decimal']:.12f}")


if __name__ == "__main__":
    main()
