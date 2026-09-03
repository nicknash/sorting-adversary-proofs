# Adversary-specific 0.72 development

This directory is reserved for the formalization of the strongest adversary.
It must be populated from a frozen mathematical source giving the exact state,
response rule, invariant, potential, terminal bound, and exact parameter
certificate.

The intended module order is:

1. `State.lean`
2. `Interpretation.lean`
3. `Reachable.lean`
4. `Response.lean`
5. `Invariant.lean`
6. `LocalPotential.lean`
7. `Terminal.lean`
8. `ExactCertificate.lean`
9. `Main.lean`

`Main.lean` must construct a `PotentialAdversaryCertificate` and prove the
independently stated theorem `SortingAdversary.adversary_072` without `sorry`,
project-specific axioms, floating-point assumptions, or an unverified external
oracle.
