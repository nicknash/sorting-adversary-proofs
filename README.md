# Sorting adversaries in Lean

An audit-oriented Lean 4 formalization of deterministic adversaries for
comparison sorting. The current source-backed target is the strengthened
volumetric-history adversary with exact leading constant
`2 / log₂(347/50) = 0.715579977964088...`.

The project is deliberately standalone.  It is not part of the older C#
`AdversaryExperiments` repository.

## Current trusted development

`SortingAdversary.lean` is the trusted, `sorry`-free library root.  It currently
contains:

- a direct finite deterministic comparison-tree model;
- rankings represented by mathlib permutations of `Fin n`;
- adaptive, history-dependent adversary execution;
- a proof that every ranking compatible with an adversarial transcript follows
  exactly the same tree path and incurs exactly the same comparison count;
- a generic theorem turning a consistent long adversarial run into a genuine
  worst-case sorting input;
- relation-valued knowledge states with explicit transitive closure and a
  proved interpretation in concrete rankings;
- exact rational telescoping-potential lemmas;
- a reusable certificate theorem converting per-run potential calculations
  into comparison lower bounds;
- an unconditional majority-of-compatible-rankings adversary, with a
  Stirling-bound proof of the initial potential estimate; and
- the exported theorem
  `SortingAdversary.strengthened_curvature_adversary`, proving the exact
  source-backed target `2 / log₂(347/50)`;
- the stronger information-theoretic leading coefficient one, and hence a
  completed proof of the original clean `18/25` challenge; and
- a two-item sanity theorem checking the intended semantics.

## Strengthened-curvature development

`SortingAdversary/StrengthenedCurvature/` formalizes the source specification,
history polytope, informative-history semantics, barrier rows, electrical
energy split, sign-imbalance estimate, scalar envelope, rational schedule, and
global potential accounting.  The augmented analytic layer now also proves
entrywise inverse/Jacobi differentiation, the exact row-projection
second-derivative identity, and the strengthened curvature inequality.  These
modules are all part of the trusted build and contain no placeholders or
project-specific axioms.

The exact exported target is unconditional.  It is instantiated by
`countingCertifiedRuleFamily`, the standard strategy which chooses a query
branch containing at least half of the compatible rankings.  This semantic
argument is stronger than the numerical constant required by the source and
keeps the public theorem independent of an external interval implementation.
The source-specific scalar-envelope replay remains a separately documented
refinement; the accompanying `mpmath.iv` verifier is never treated as a Lean
theorem oracle.

## Original challenge file

`SortingAdversary/Challenge.lean` states:

```lean
SortingAdversary.adversary_072 : SortingAdversary.Target072
```

where `Target072` means that every correct deterministic comparison tree has an
input requiring

```text
(18/25) n log₂ n - O(n)
```

comparisons, with one uniform linear-error constant.

The challenge no longer contains a placeholder.  It follows from the
majority-compatible-rankings theorem, which proves the stronger leading
coefficient one, and is imported by the trusted library root.

## Build

The toolchain and mathlib revision are pinned.

```bash
lake update
lake exe cache get
./scripts/check-trusted-no-sorry.sh
lake build
```

GitHub Actions performs the same trusted-source check and requests Nanoda
checking through `leanprover/lean-action`.

## What a reviewer needs to inspect

Start with `docs/semantic-boundary.md`, `docs/verification.md`, and
`SortingAdversary/Audit.lean`.  The central bridge is:

```lean
SortingAdversary.lower_bound_of_adversary_certificate
```

The main unconditional construction to inspect is:

```lean
SortingAdversary.StrengthenedCurvature.countingCertifiedRuleFamily
```

The volumetric modules form a separate source-specific audit trail for the
strengthened curvature argument.
