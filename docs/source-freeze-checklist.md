# Source-freeze checklist for the 0.72 adversary

Before adversary-specific Lean code is treated as a formalization of the
mathematical result, one immutable source document or commit must provide all
of the following.

## Mathematical data

- Exact theorem statement, including the quantifiers over algorithms and `n`.
- Whether efficiency of the adversary is part of the theorem or a separate
  implementation claim.
- Exact state representation and initial state.
- A total deterministic response rule for every reachable comparison type.
- The realization invariant connecting every reachable state to at least one
  total ranking.
- The potential, including every history-dependent or tracked-point term.
- The one-comparison potential-increase lemma, with a complete case split.
- The terminal potential lower bound.
- Treatment of arbitrary `n`, rounding, incomplete blocks, and small values.
- Exact rational or algebraic parameters certifying a coefficient above
  `18/25`; decimal output from an optimizer is not a certificate.

## Formalization correspondence

For each definition and lemma in the source, record the Lean declaration that
implements it.  Conversely, every nontrivial adversary-specific Lean declaration
should identify the source definition, lemma, or finite certificate it realizes.

## Acceptance conditions

- `lake build` succeeds on the pinned toolchain.
- No trusted module uses `sorry` or a project-specific axiom.
- `#print axioms SortingAdversary.adversary_072` reports only the explicitly
  permitted foundational axioms.
- Comparator confirms that `Main.lean` proves exactly the theorem in
  `Challenge.lean`.
- Any generated finite certificate is reproducible and its checker is proved
  sound inside Lean.
