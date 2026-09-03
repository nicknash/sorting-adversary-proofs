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
- a two-item sanity theorem checking the intended semantics.

## Strengthened-curvature development

`SortingAdversary/StrengthenedCurvature/` formalizes the source specification,
history polytope, informative-history semantics, barrier rows, electrical
energy split, sign-imbalance estimate, scalar envelope, rational schedule, and
global potential accounting. These modules are all part of the trusted build
and contain no placeholders or project-specific axioms.

The exact remaining bridge is represented by:

```lean
SortingAdversary.StrengthenedCurvature.CertifiedRuleFamily
```

The center/end-point layer is now complete: minimizers exist unconditionally,
Jacobi differentiation gives their exact leverage balance, and the electrical
direction has unit normalized row energy. Constructing the object still
requires the augmented projection-curvature reduction and kernel-verified
replay of the directed interval certificate. See `docs/formalization-plan.md`
for the current theorem map. The external `mpmath.iv` verifier is not treated
as a theorem oracle.

## Superseded challenge file

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

The challenge file contains one **intentional** `sorry` and is excluded from the
trusted library root. Its clean `18/25` target predates the frozen strengthened
source and is not imported or claimed by the trusted development.

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

The adversary-specific development must interpret every custom state back into
ordinary rankings and ultimately construct:

```lean
SortingAdversary.PotentialAdversaryCertificate n k
```

The final proof is intended to be checked against the separately maintained
challenge statement using Comparator.
