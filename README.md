# Sorting adversaries in Lean

An audit-oriented Lean 4 formalization of deterministic adversaries for
comparison sorting, with the strongest new adversary (clean target constant
`18/25 = 0.72`) as the main target.

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

## Open target

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
trusted library root.  The connected source repositories do not contain a
frozen, complete statement of the claimed `0.72...` construction.  Accordingly,
this repository does not pretend that the final theorem has already been
proved.  The exact missing proof obligations are listed in
`docs/formalization-plan.md`.

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
