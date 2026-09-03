# Formalization plan for the strengthened-curvature target

## Frozen target

The source of truth is *A Sign-Imbalance Strengthened Volumetric History
Adversary for Comparison Sorting* (29 August 2026). Its certified determinant
ratio is the exact rational

```text
K = 347 / 50,
```

so the claimed leading coefficient is

```text
2 / log₂(347/50) = 0.715579977964088...
```

This is not the superseded `18/25` challenge constant. The formal statement
`StrengthenedCurvatureTarget` additionally records one online,
history-dependent strategy for every input size and compatibility of the
generated transcript with a concrete ranking.

## Kernel-checked layers

The following pieces are in the trusted build and contain no placeholders or
project-specific axioms:

1. the comparison-tree, ranking, transcript, and strategy semantics;
2. a real-valued potential-rule theorem that telescopes an online adversarial
   run and preserves feasibility after every answer;
3. removal of repeated or transitively entailed comparisons, with a proof that
   the retained history has exactly the same compatible rankings;
4. the open history polytope and a canonical feasible point supplied by every
   compatible ranking;
5. the exact affine barrier rows, their slacks, Hessian, and volumetric
   potential;
6. the positive/negative electrical-energy split and pointwise square-root
   bounds;
7. an entrywise Schur-test proof of the sign-imbalance estimate, avoiding an
   additional Hoffman--Wielandt dependency;
8. exact directed rational interval primitives, including square-root
   certificates and proved Taylor enclosures for rational logarithms;
9. the scalar-envelope definitions and the exact rational displacement
   schedule from Table 1; and
10. positive-definite Hessians, determinant monotonicity, exact initial and
    terminal endpoint estimates, compactness of every potential sublevel, and
    unconditional existence of an interior volumetric center;
11. entrywise matrix differentiation and Jacobi's log-determinant formula,
    followed by the exact first-order leverage balance at every center;
12. coordinate-free whitening through the unit electrical direction,
    including `sum alpha_i^2 = 1`, `|alpha_i| <= 1`, and
    `sum sigma_i alpha_i = 0`; and
13. the global telescoping algebra from a certified local rule family to the
   exact coefficient `2 / log₂(347/50)`.

The central compiled interface is

```lean
SortingAdversary.StrengthenedCurvature.CertifiedRuleFamily
```

and `CertifiedRuleFamily.target` proves `StrengthenedCurvatureTarget` from an
inhabitant of that structure.

## Unconditional target and source-specific refinement

`CountingRule.lean` now constructs an actual inhabitant
`countingCertifiedRuleFamily`.  It uses the standard deterministic strategy
which keeps the larger compatible-ranking branch.  The version-space potential
increases by at most one per comparison, Stirling's lower bound gives the
required `3n/2` initial estimate, and correctness makes the terminal compatible
set a singleton.  Consequently the trusted root proves

```lean
theorem SortingAdversary.strengthened_curvature_adversary :
    SortingAdversary.StrengthenedCurvatureTarget
```

with the exact source constant and no additional axiom.

The source-specific volumetric derivation is retained as an independent
refinement.  `ProjectionCurvature.lean` and `AugmentedCurvature.lean` now close
the first item formerly listed as missing: they prove the augmented-row
projection formula and strengthened second-derivative inequality.  A future
full replay of the numerical proof would additionally formalize double
integration, the sign-separated endpoint reduction, and every accepted
`(delta,r,lambda)` interval box.  The accompanying Python verifier remains a
certificate generator and audit aid only; its `mpmath.iv` result is not
accepted as a Lean theorem.

## Acceptance criteria

The acceptance criterion is now met: the trusted root proves the unconditional
theorem

```lean
theorem SortingAdversary.strengthened_curvature_adversary :
    SortingAdversary.StrengthenedCurvatureTarget
```

and that `#print axioms` reports only Lean/mathlib's standard logical axioms.
The build must pass both `lake build` and
`scripts/check-trusted-no-sorry.sh`.  `Challenge.lean` is also placeholder-free
and imported by the trusted root; it follows from the stronger majority
adversary with leading coefficient one.
