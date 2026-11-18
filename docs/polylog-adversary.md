# The polylogarithmic sorting adversary

The source is *An optimal sorting adversary in polylogarithmic time per
comparison* (18 November 2026). The online machine receives two labels and
returns an answer and an updated memory. It reads short outward-rounded
enclosures, writes exact anchors into a shared dyadic block heap and
freezes its memory after the active horizon. The frozen machine can
answer arbitrarily many further queries.

## Main theorems

[PolylogRAM.asymptoticallyOptimal_and_polylogarithmic](../SortingAdversary/Continuous/PolylogRAM.lean)
proves both guarantees for the same deterministic online machine. For every
positive `ε` and all sufficiently large `n`, every correct comparison
sorter performs at least $(1-\varepsilon)n\log_2 n$ comparisons against
the machine. After **any** history, the next comparison costs at most
`(10²⁰ + 3) L¹⁰` in the word and bit cost model, where
`L = floor(log₂(n + 1)) + 1`. This is a worst-case bound per query,
including the query that triggers a path repair or enters the frozen phase.

| Guarantee | Theorem |
| --- | --- |
| A single ranking realizes all responses along each finite run | `PolylogRAM.asymptoticallyOptimal_and_polylogarithmic` (consistency is part of `Optimal.AsymptoticallyOptimal`) |
| Execution from measured startup agrees with the strategy used in the sorting theorem | `PolylogRAM.run_eq` |
| Linear startup, including rejected stages and construction of the exact initial memory | `PolylogStartup.build_work` |
| At most `8,210 (n + 1) L⁴` logical storage entries after any history | `PolylogRAM.stored_entries` |
| Cumulative allocation of persistent trie and adjacency-list cells, including superseded versions | `PolylogEfficient.allocated_storage_cells` |

## Proof map

| Part of the argument | Lean entry point |
| --- | --- |
| Probability guarantees after rounding the two sets of walls in opposite directions | [PolylogEnclosure](../SortingAdversary/Continuous/PolylogEnclosure.lean) |
| Exact dyadic prefix search and persistent allocation | [PolylogRawAnchor](../SortingAdversary/Continuous/PolylogRawAnchor.lean) and [PolylogMint](../SortingAdversary/Continuous/PolylogMint.lean) |
| Agreement of one stored comparison, including graph repair, with the rounded geometric controller | [PolylogCompare.compare_aligned](../SortingAdversary/Continuous/PolylogCompareProofs.lean) |
| Countdown, cached stage constants and transition to the frozen order | [PolylogExecution](../SortingAdversary/Continuous/PolylogExecution.lean) |
| Agreement and cost of the single-pass, fully priced active comparison | [PolylogWordProgram](../SortingAdversary/Continuous/PolylogWordProgram.lean) and [PolylogWordCompare.active_work](../SortingAdversary/Continuous/PolylogWordBudget.lean) |
| Frozen queries, including balanced-dictionary lookups | [PolylogFrozenQuery.scheduled_work](../SortingAdversary/Continuous/PolylogFrozenQuery.lean) |
| Fixed table height and bounds on heap and hierarchy addresses | [PolylogResources](../SortingAdversary/Continuous/PolylogResources.lean) |

The schedule admits a stage only when its local enumeration and repair
budgets fit the logarithmic cap. Before the first admitted stage, the
machine answers in label order. The polynomial bound is an asymptotic
certificate and its constants are conservative.

## Cost model and verification

The stored controller also has a bound of `20,000,003 L⁹` in the
repository's coarser arithmetic and block-operation model.
[PolylogEfficient](../SortingAdversary/Continuous/PolylogEfficient.lean)

The word-priced controller counts balanced-dictionary key comparisons and
local rebalances along the paths taken, including probes that discard their
temporary heaps. It prices rational comparisons, normalization, the seven
operations in an affine digit and the final certificate sort. Its cached
stage constants and persistent table indices fit logarithmically many bits.
The model counts operations on words with logarithmically many bits and
uses a conservative schoolbook bit charge for short rational arithmetic.
Native Lean execution time, allocator bytes and garbage-collection pauses
are outside the model.
[Dictionary paths](../SortingAdversary/Continuous/PolylogWordWork.lean) ·
[Key widths](../SortingAdversary/Continuous/PolylogHeapKeys.lean) ·
[Rational operands](../SortingAdversary/Continuous/PolylogOperands.lean) ·
[Priced enclosures](../SortingAdversary/Continuous/PolylogKernelProfile.lean)

The space theorems bound live entries and the cumulative number of
persistent trie and adjacency-list cells. The latter count includes
superseded versions. The frozen phase retains the same stored memory. In addition,
`PolylogRAM.preFreezeWork_bound` bounds all work before freezing by
`(10²⁰ + 3) n L¹¹`, independently of the length of the frozen suffix.
[Allocation proof](../SortingAdversary/Continuous/PolylogTrieCharges.lean)

The source checks, build, independent kernel replay and axiom audit can be
run with the same commands as CI.

```sh
./scripts/check-trusted-no-sorry.sh
./scripts/check-continuous-audit-imports.sh
lake build SortingAdversary
LEAN_NUM_THREADS=1 lake env leanchecker SortingAdversary
lake env lean SortingAdversary/Continuous/Audit.lean
```
