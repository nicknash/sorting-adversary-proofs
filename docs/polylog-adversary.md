# The polylogarithmic sorting adversary

The source is *An optimal sorting adversary in polylogarithmic time per
comparison*, 18 November 2026. Its uniform adversary uses rounded finite
enclosures, a binary-prefix fallback anchor and an order computed locally
after the active horizon.

## What Lean proves

`PolylogAdversary.asymptoticallyOptimal` proves the leading-one lower bound for
these specific choices against every correct comparison sorter.
`PolylogAdversary.consistent` and `execute_eq_run` give transcript consistency
and agreement with the stateful execution. The proof instantiates the
continuous controller's comparison and repair invariants with new geometric
certificates. It permits the rounded answers to differ from those of the
original exact-enclosure controller.

`PolylogAdversary.active_work` bounds the work of a stored active query by
`(logCap n + 7) * (2*b + 3) + 5` given a bound `b` for the individual
component calls visited by that query. A closed word-RAM time and space
bound requires a stored implementation satisfying all of those obligations
on every reachable state. The semantic comparison theorem has no such
hypothesis.

All modules belong to the continuous all-declaration axiom audit.
