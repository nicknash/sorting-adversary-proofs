# The polylogarithmic sorting adversary

The source is *An optimal sorting adversary in polylogarithmic time per
comparison* (18 November 2026). The online machine receives two labels and
returns an answer and an updated memory. It reads short outward-rounded
enclosures, writes exact anchors into a shared dyadic block heap and
freezes its memory after the active horizon. The frozen machine can
answer arbitrarily many further queries.

## Main theorems

In [PolylogEfficient.lean](../SortingAdversary/Continuous/PolylogEfficient.lean),
`consistent` proves that the stored machine's answers admit a single
ranking on each run. `asymptoticallyOptimal` proves that every correct
comparison sorter needs at least $(1-o(1))n\log_2 n$ comparisons against
this deterministic strategy. `execute_eq_run` connects a run from the
initial memory to the repository's decision-tree specification.

| Part of the argument | Lean entry point |
| --- | --- |
| Probability guarantees after rounding the two sets of walls in opposite directions | [PolylogEnclosure](../SortingAdversary/Continuous/PolylogEnclosure.lean) |
| Exact dyadic prefix search and persistent allocation | [PolylogRawAnchor](../SortingAdversary/Continuous/PolylogRawAnchor.lean) and [PolylogMint](../SortingAdversary/Continuous/PolylogMint.lean) |
| Agreement of one stored comparison, including graph repair, with the rounded geometric controller | [PolylogCompare.compare_aligned](../SortingAdversary/Continuous/PolylogCompareProofs.lean) |
| Countdown, cached stage constants and transition to the frozen order | [PolylogExecution](../SortingAdversary/Continuous/PolylogExecution.lean) |
| Frozen queries, including balanced-dictionary lookups | [PolylogFrozenQuery.scheduled_work](../SortingAdversary/Continuous/PolylogFrozenQuery.lean) |
| Fixed table height and bounds on heap and hierarchy addresses | [PolylogResources](../SortingAdversary/Continuous/PolylogResources.lean) |

The frozen query takes at most `72000 * (logCap n + 1)^2` charged
operations under the proved representation and capacity invariants.
Here `logCap n` is the floor of the base-two logarithm of `n + 1`.
The end-to-end worst-case active work estimate is being assembled from
the component bounds. The sorting lower bound and state refinement are
unconditional.

All these modules belong to the continuous all-declaration axiom audit.
