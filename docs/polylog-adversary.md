# The polylogarithmic sorting adversary

The source is *An optimal sorting adversary in polylogarithmic time per
comparison* (18 November 2026). The online machine receives two labels and
returns an answer and an updated memory. It reads short outward-rounded
enclosures, writes exact anchors into a shared dyadic block heap and
freezes its memory after the active horizon. The frozen machine can
answer arbitrarily many further queries.

## Main theorems

[PolylogEfficient.asymptoticallyOptimal_and_polylogarithmic](../SortingAdversary/Continuous/PolylogEfficient.lean)
proves both guarantees for the same deterministic online machine. For every
positive `ε` and all sufficiently large `n`, every correct comparison
sorter performs at least $(1-\varepsilon)n\log_2 n$ comparisons against
the machine. After **any** history, the next query costs at most
`20,000,003 L⁹` counted operations, where `L = floor(log₂(n + 1)) + 1`.
This is a worst-case bound per query, including a query that triggers a
path repair or enters the frozen phase.

| Guarantee | Theorem |
| --- | --- |
| A single ranking realizes all responses along each finite run | `PolylogEfficient.consistent` |
| Execution from measured startup agrees with the strategy used in the sorting theorem | `PolylogEfficient.run_eq` |
| Linear startup, including rejected stages and construction of the exact initial memory | `PolylogStartup.build_work` |
| At most `8,210 (n + 1) L⁴` logical storage entries after any history | `PolylogEfficient.stored_entries` |
| Cumulative allocation of persistent trie and adjacency-list cells, including superseded versions | `PolylogEfficient.allocated_storage_cells` |

## Proof map

| Part of the argument | Lean entry point |
| --- | --- |
| Probability guarantees after rounding the two sets of walls in opposite directions | [PolylogEnclosure](../SortingAdversary/Continuous/PolylogEnclosure.lean) |
| Exact dyadic prefix search and persistent allocation | [PolylogRawAnchor](../SortingAdversary/Continuous/PolylogRawAnchor.lean) and [PolylogMint](../SortingAdversary/Continuous/PolylogMint.lean) |
| Agreement of one stored comparison, including graph repair, with the rounded geometric controller | [PolylogCompare.compare_aligned](../SortingAdversary/Continuous/PolylogCompareProofs.lean) |
| Countdown, cached stage constants and transition to the frozen order | [PolylogExecution](../SortingAdversary/Continuous/PolylogExecution.lean) |
| Frozen queries, including balanced-dictionary lookups | [PolylogFrozenQuery.scheduled_work](../SortingAdversary/Continuous/PolylogFrozenQuery.lean) |
| Fixed table height and bounds on heap and hierarchy addresses | [PolylogResources](../SortingAdversary/Continuous/PolylogResources.lean) |

The schedule admits a stage only when its local enumeration and repair
budgets fit the logarithmic cap. Before the first admitted stage, the
machine answers in label order. The polynomial bound is an asymptotic
certificate and its constants are conservative.

## Cost model and verification

The query bound uses the repository's `PrimitiveWork.Result` model. Its
operations include local rational arithmetic, block accesses, row scans
and updates to persistent tables. [PolylogOperands](../SortingAdversary/Continuous/PolylogOperands.lean)
bounds the numerators, denominators and intermediate cross products used by
the rounded local enclosures. [PolylogDictionary](../SortingAdversary/Continuous/PolylogDictionary.lean)
bounds comparisons in the balanced interning dictionaries.
[PolylogTrieCharges](../SortingAdversary/Continuous/PolylogTrieCharges.lean)
counts persistent trie and adjacency-list cells allocated before freezing.
The theorem concerns this formal cost model. Exact byte counts, Lean's
allocator and native instruction timings lie outside it.

The source checks, build, independent kernel replay and axiom audit can be
run with the same commands as CI.

```sh
./scripts/check-trusted-no-sorry.sh
./scripts/check-continuous-audit-imports.sh
lake build SortingAdversary
LEAN_NUM_THREADS=1 lake env leanchecker SortingAdversary
lake env lean SortingAdversary/Continuous/Audit.lean
```
