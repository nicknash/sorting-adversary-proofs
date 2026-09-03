# Curvature-adversary formalization status

## Exported target

The completed theorem uses the efficient deterministic curvature/volumetric
adversary with exact determinant ratio

```text
K = 347 / 50
```

and coefficient `2 / log₂ K = 0.715579977964088...`.  The theorem records one
online history-dependent strategy for every input size, feasibility after
every answer, and a compatible concrete ranking at the generated leaf.

## Kernel-checked proof chain

1. Comparison trees, rankings, transcripts, strategies, and the hard-input
   semantic bridge.
2. Retention of precisely the informative history-DAG rows.
3. Strict feasibility of the history polytope and existence of its volumetric
   center.
4. Barrier-Hessian positivity, whitening, electrical normalization, and the
   leverage-balance stationarity equation.
5. Rank-one determinant identities and exact augmented-Gram differentiation.
6. Projection curvature, the sign-imbalance rate-saving inequalities, and the
   twice-integrated positive and negative branch inequalities.
7. Convex endpoint reduction to the two-variable scalar envelope.
8. Exact rational interval arithmetic, proved logarithm bounds, and the
   recursive `347/50` certificate (7,315 terminal boxes).
9. The small-offset electrical trial rule and large-offset center-side rule.
10. Completion to arbitrary repeated or implied queries, initial/terminal
    endpoints, and global telescoping.

The closing declaration is

```lean
SortingAdversary.StrengthenedCurvature.efficient_curvature_adversary
```

## Deterministic numerical implementation

`ApproximateRule.lean` formalizes the decision used in the notes: compare
rational approximations to the two child potentials and select the smaller.
The theorem `approximateChildAnswer_le_min_add` proves that accuracy `ε` loses
at most `2ε` in true potential.  Polynomial-time production of `n⁻⁴`-accurate
values is the notes' standard deterministic convex-optimization ingredient;
the repository's semantic decision-tree model does not define bit complexity.

## Strengthened sign-imbalance certificate

The exported theorem uses the later note's `K = 347/50` argument.
`RateSaving.lean`, `StrengthenedIntegration.lean`,
`StrengthenedBranchBounds.lean`, and `StrengthenedEnvelope.lean` prove the
symbolic saving reduction.  `StrengthenedInterval.lean` proves the directed
square-root, logarithm, crossover, and saving bounds; the generated tree in
`StrengthenedCertificateData.lean` is then replayed exactly for the full
`(delta,r,lambda)` cover.

## Acceptance conditions

- `lake build SortingAdversary` succeeds on the pinned toolchain;
- every trusted source is free of `sorry`, `admit`, and project-specific
  axioms;
- the finite scalar certificate is reproducible and its checker has a proved
  soundness theorem; and
- the axiom audit of the exported adversary theorem reports only the permitted
  Lean/mathlib foundations and the explicitly named `native_decide` evaluator
  for the finite rational check.
