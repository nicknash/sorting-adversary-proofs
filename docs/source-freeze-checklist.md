# Source-freeze checklist

Before a stronger adversary is exported, one immutable source bundle must
provide the exact theorem, state, deterministic response rule, feasibility
invariant, potential, local transition bound, terminal estimate, and an exact
certificate for every numerical inequality.

For the current `347/50` result the repository additionally requires:

- a Lean theorem connecting each analytic reduction to the scalar envelope;
- a proof-producing exact-rational interval checker;
- a checked cover of the full normalized-offset interval;
- an overlap proof between the small- and large-offset regimes;
- a total rule for repeated and transitively implied queries; and
- a global theorem connecting the adversarial transcript to a genuine ranking.

Decimal output or an `mpmath.iv` pass is not by itself a Lean certificate.  The
complete `(delta,r,lambda)` box cover, including directed square-root,
logarithm, crossover, and saving bounds, is replayed by a proved sound checker
before `347/50` enters the exported theorem.

Acceptance requires `lake build SortingAdversary`, the trusted-source
placeholder scan, and an axiom audit allowing `propext`, `Classical.choice`,
`Quot.sound`, and only the explicitly named `native_decide` evaluator used by
the finite exact-rational certificate replay.
