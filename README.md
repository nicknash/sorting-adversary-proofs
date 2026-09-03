# Sorting adversaries in Lean

An audit-oriented Lean 4 formalization of the deterministic
curvature/volumetric adversary for comparison sorting.

The trusted theorem has determinant ratio

```text
K = 347 / 50
```

and leading coefficient

```text
2 / log₂(347/50) = 0.715579977964088...
```

This is the strengthened exact-rationally certified constant from the
curvature-volumetric notes; the full two-variable finite certificate is
replayed with Lean's native evaluator.  Lean proves the exact enclosure
`0.7155 < 2 / log₂(347/50) < 18/25`.

## What is proved

`SortingAdversary.lean` is the trusted, `sorry`-free library root.  It includes:

- finite deterministic comparison trees, rankings, adaptive transcripts, and
  the bridge from a consistent adversarial transcript to a genuine hard input;
- informative-history retention, including repeated and transitively implied
  comparisons;
- the history polytope, logarithmic barrier Hessian, volumetric center, and
  initial and terminal determinant estimates;
- whitening, electrical motion, exact first and second derivative identities,
  sign-sensitive rate savings, and twice-integrated branch inequalities;
- a proved exact-rational interval checker and a native replay of all 7,315
  leaves of its Boolean certificate for the two-variable `347/50` envelope;
- the explicit local rule: at large normalized offset retain the center side;
  otherwise evaluate the two electrical trial branches and retain the smaller;
- the resulting total history-dependent strategy and global telescoping proof;
  and
- a rational approximate-child selector proving that additive error `ε` costs
  at most `2ε` in the selected true child potential.

There is no compatible-ranking counting adversary in the theorem path.

The main declarations are:

```lean
SortingAdversary.StrengthenedCurvature.efficientInformativeRule
SortingAdversary.StrengthenedCurvature.efficientCertifiedRuleFamily
SortingAdversary.StrengthenedCurvature.efficient_curvature_adversary
SortingAdversary.StrengthenedCurvature.approximateChildAnswer_le_min_add
```

## Efficiency boundary

The mathematical rule is deterministic and uses only the retained DAG and two
child volumetric potentials.  The notes obtain polynomial time by evaluating
those potentials to additive accuracy `n⁻⁴` with deterministic convex
optimization; there are at most `O(n²)` informative comparisons, so the total
decision error is `O(n⁻²)`.

Lean's `Strategy` type is a semantic function and carries no bit-cost model.
Accordingly, the repository proves the exact geometric strategy and the
`2ε` robustness lemma, while treating the standard convex-optimization running
time as the implementation boundary rather than pretending that
`Classical.choose` is executable code.

## Build and audit

The Lean toolchain and mathlib revision are pinned.

```bash
lake update
lake exe cache get
./scripts/check-trusted-no-sorry.sh
lake build SortingAdversary
```

GitHub Actions repeats the source audit, full trusted build, `leanchecker`, and
axiom audit.  Besides the usual Lean foundations, the audit explicitly allows
the generated `native_decide` evaluator axiom for the finite rational replay;
the checker soundness proof itself remains kernel checked.  Review
`docs/semantic-boundary.md`, `docs/verification.md`, and
`SortingAdversary/Audit.lean` for the small trusted interface.
