# Verification model

The project separates three questions that are too easily conflated.

## 1. Does the formal statement mean comparison sorting?

A human reviewer checks the small interface in `Basic.lean` and
`DecisionTree.lean`:

- `Ranking n` is a mathlib permutation of `Fin n`, interpreted as item-to-rank;
- a `Query n` contains two distinct items;
- `DecisionTree n` is a finite binary comparison tree;
- `Correct` says that every hidden ranking is recovered exactly;
- `cost` counts the internal comparison nodes on the input's path.

`Examples/TwoItems.lean` proves a tiny expected consequence independently of
any adversary machinery.

## 2. Does the adversarial interaction correspond to a genuine input?

`Strategy.lean` records the adversary's answers.  The theorem

```lean
DecisionTree.run_matches_compatible_ranking
```

proves that every ranking satisfying the transcript follows the identical
ordinary decision-tree path.  Consequently,

```lean
lower_bound_of_adversary_certificate
```

turns consistency plus a long interaction into a standard worst-case input.

Adversary-specific bookkeeping is not allowed to redefine this semantics.  It
must prove that its final state has at least one realizing ranking.

## 3. Is the large proof mechanically valid?

The trusted development is built by Lean and checked again by the configured
independent checks.  Exact rational arithmetic is used for potential bounds;
floating-point optimization output is not trusted.  The 7,315-leaf
strengthened certificate covers all 22 schedule segments and all normalized
positive energies in `[0,1]`.  Its finite Boolean replay uses `native_decide`,
whose generated evaluator axiom is named explicitly in the CI allowlist; the
interval checker's soundness is an ordinary Lean proof.
The source check rejects `sorry`, `admit`, `sorryAx`, and project-specific
`axiom` declarations in every trusted Lean module.

The final result is exposed through the fixed source specification
`StrengthenedCurvatureTarget` and the closing theorem
`StrengthenedCurvature.efficient_curvature_adversary`.  `Audit.lean` prints
both the target and the proof's axiom dependencies.

## Trust base

The intended trust base is:

- the human reading of the small semantic interface;
- Lean's logic and kernel;
- the pinned mathlib definitions and theorems;
- Lean's native evaluator for the exact rational certificate Boolean; and
- optionally, an independent exported-proof checker through the CI pipeline.

Tactics, generated code, search scripts, numerical optimizers, and certificate
generators are conveniences.  None should be trusted as theorem-producing
oracles.
