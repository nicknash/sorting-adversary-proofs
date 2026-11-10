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

## 3. Which construction is being checked?

The current paper's continuous construction is exported by
`Continuous.UniformAdversary.asymptoticallyOptimal` and
`Continuous.UniformAdversary.worst_case`. Its actual controller discharges
the geometric, local-certificate, sampling and accounting hypotheses. The
[continuous theorem map](continuous-adversary-formalization.md) records the
correspondence to the manuscript and the explicit external input to the
supplied-information corollary.

`Continuous.UniformMachineWork` implements the stored program and proves
exact agreement with that strategy. `Continuous.UniformEfficient` combines
its counted execution, reachable operand certificates and fixed polynomial
charges in an explicit schoolbook arithmetic model. This resource theorem
does not certify native compiler or bigint timings.

The earlier recursive-colour theorem remains under `Optimal/`. Both
constructions have enforced all-declaration axiom audits allowing only
`propext`, `Classical.choice` and `Quot.sound`. They require no native
certificate axiom. The separate curvature construction below has the
historical native-evaluation trust requirement described explicitly here.

## 4. Is the large proof mechanically valid?

The trusted development is built by Lean, replayed with `leanchecker`, and
checked by source and axiom audits. Kernel replay reuses Lean's kernel;
an external exported-proof checker is a separate check.
Exact rational arithmetic is used for potential bounds;
floating-point optimization output is not trusted.  The 7,315-leaf
strengthened certificate covers all 22 schedule segments and all normalized
positive energies in `[0,1]`.  Its finite Boolean replay uses `native_decide`,
whose generated evaluator axiom is named explicitly in the CI allowlist; the
interval checker's soundness is an ordinary Lean proof.
The source check rejects `sorry`, `admit`, `sorryAx`, and project-specific
`axiom` declarations in every trusted Lean module.

The curvature result is exposed through the fixed source specification
`StrengthenedCurvatureTarget` and the closing theorem
`StrengthenedCurvature.efficient_curvature_adversary`.  `Audit.lean` prints
both the target and the proof's axiom dependencies.

## Trust base

The common trust base is:

- the human reading of the small semantic interface;
- Lean's logic and kernel;
- the pinned mathlib definitions and theorems.

An external exported-proof checker can provide an additional independent
check. The [CI workflow](../.github/workflows/lean.yml) records why its
optional `nanoda` step is currently disabled.

The curvature certificate additionally trusts Lean's native evaluator for
its exact rational Boolean replay. This additional dependency is excluded
by both the continuous and recursive-colour audits.

Tactics, generated code, search scripts, numerical optimizers, and certificate
generators are conveniences.  None should be trusted as theorem-producing
oracles.
