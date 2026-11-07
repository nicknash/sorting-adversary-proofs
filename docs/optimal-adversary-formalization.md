# Recursive colour adversary: checked results and remaining obligations

## Status

This directory formalizes components of the 7 November 2026 manuscript,
*An asymptotically optimal deterministic adversary for comparison sorting*.
**It does not yet prove the manuscript's complete deterministic polynomial-time
adversary theorem.** The existing curvature theorem remains the repository's
proved complete online adversary result.

The new files contain proofs, executable finite reference definitions, and
explicit conditional reductions. There are no admitted proofs or declarations
of the missing mathematical results as axioms. In particular,
`comparison_guarantee_of_vanishing_accounting` has explicit legality,
accounting, and convergence hypotheses; it is not an existence theorem for
the proposed controller.

The source used for this development is the eleven-page manuscript dated
7 November 2026. Its PDF SHA-256 is
`353eeb213b15809abcd4c3de8ecce4137dce3f7c47734a80e2c8391049ceae70`.
The new construction is different from the curvature construction already in
the repository. None of its main lemmas is inferred from that older theorem.

## What has been checked

All paths below are under `SortingAdversary/Optimal/`.

| File | Proved content | Manuscript connection |
| --- | --- | --- |
| `WeakMaps.lean` | Exact finite colour-map semantics; raw row updates; overlapping weak branches; effective windows and attainable support; exact independent births; palette enlargement preserving old assignments | Sections 1–3 |
| `Routing.lean` | Explicit one-edge public closure; same-colour inner witnesses; all-retaining reverse signs; both obstructions force delegation; interior pins are incomparable to older same-colour pins | Sections 1–2 |
| `Refinement.lean` | Both endpoint colour splits; collapse is a left inverse; raw inequalities and artificial lists survive; immutable physical pin identities and strict cuts are preserved under their stated hypotheses | Section 2 |
| `FiniteRefinement.lean` | Both endpoint splits assembled into finite weak-map systems, with physical pins distinguished from artificial lists and cardinal injections from the selected old fibres | Section 2 |
| `Insertion.lean` | Concrete integer compression, central insertability, and finite counting consequences | Section 3 |
| `LocalChoice.lean` | Induced local systems and exact rational reference probabilities; choosing the larger estimate retains at least `1/2 - ε` when both errors are at most `ε`; unchanged old probabilities after palette enlargement | Section 3, conditional on approximation errors |
| `Terminal.lean` | Exactly `choose (K+r-1) r` weakly increasing assignments; actual finite assignment families with fixed pins satisfy this terminal bound | Section 5 |
| `Accounting.lean` | Factorial birth credits; bounded total cheap-pin cost; log-sum and code inequalities; node and population accounting; tree entropy; logarithmic binomial and terminal bounds; signed update telescoping | Section 5 |
| `GroupEntropy.lean` | Conditional destination entropy is at most unconditional destination entropy; groups of size `h` with multiplicity cap `r` cost at least `h log(h/r)` | Section 5, path and scale groups |
| `Endpoints.lean` | The actual root count is `n^n`; actual terminal weak systems satisfy the global logarithmic bound in terms of total free labels and total palette size | Sections 1 and 5 |
| `Parameters.lean` | Executable bounded consecutive-stage selection, first-rejection stopping, a bound on the number of tests, and divergence of selected stages under explicit affordability assumptions | Section 6 |
| `ComparisonBound.lean` | Precise online leading-one specification; finite relative-error clock inequality; reduction from vanishing accounting errors; conversion to a genuine worst-case input | Theorem 1, conditional reduction |
| `Examples.lean` | Kernel-reduced finite checks of ties, palette preservation, births, endpoint identities, and the distinction between weak feasibility and strict public legality | Semantic regression checks |
| `Audit.lean` | Declaration-level axiom audit of the new namespace | Verification boundary |

### Continuation after the initial foundation PR

The following modules close additional obligations of the initial checkpoint.
The full recursive controller and end-to-end polynomial-time theorem remain
under construction.

| File | Newly proved content |
| --- | --- |
| `Safety.lean` | Exact window changes under a new comparison; a newly singleton free coordinate forces an all-retaining reverse with a strict witness |
| `ControllerRouting.lean` | Executable certified routing using both safety tests and window feasibility; safe stopping branches preserve the local public-order and free-window invariant |
| `PinTransitions.lean` | Exact windows after a physical pin; strict interior pins preserve every other free coordinate and give independent child admissions |
| `RefinementTransitions.lean` | Both endpoint palette refinements preserve the full local invariant; the fresh colour is proved interior before pinning |
| `FreshAdmission.lean` | Fixed-carrier fresh-label admission is bijective to the old maps times the palette; exact birth credit and preservation of invariants through birth and top-colour enlargement |
| `SparseClosure.lean` | Stored-matrix Floyd--Warshall closure; exact map/count equivalence; propagating original walls while retaining sparse rows; explicit cubic matrix-cell-write count |
| `PublicOrder.lean` | Concrete ranking extension of any finite public partial order using predecessor counts and label tie-breaking |
| `PublicLegality.lean` | Executable public-order guard; every guarded policy satisfies the actual repository's online legality specification |
| `CompletedOrder.lean` | A correct sorter makes the actual public closure total; its compatible ranking supplies the exact free-label enumeration for the terminal count |
| `IdealCounting.lean` | Stored-table ideal-state dynamic programming equals the original finite count; endpoint expiry/future checks, polynomial table-work bounds under the logarithmic cap, and bounds on all intermediate integer sizes |
| `DyadicDictionary.lean` | Explicit finite dyadic hub-record code and summable cubic subprobability bound |
| `SignedPrice.lean` | Positive-debit truncation, factorial credits, code/Jensen aggregation, and the absolute-constant global signed-price envelope from dictionary records |

`IdealCounting.count_eq` is exact correctness of the executable local counter,
not an assumption about a counting oracle. The work theorem counts transition
tests and scanned table entries, including the implementation's linear table
lookup. It does not by itself certify the bit cost of arbitrary input functions
for rows and bounds. The stored-matrix representation and integer-size results
are ingredients for that separate end-to-end cost proof.

The public guard proves legality for any supplied policy; it does not prove
that every supplied policy has a long run. Likewise, the signed-price theorem
requires dictionary records representing the actual chosen colours. These
distinctions remain explicit during controller assembly.

`WeakSystem` uses Boolean raw rows and inclusive finite colour intervals.
Consequently exact counts and the reference choices are executable. The
reference definitions enumerate assignments. `IdealCounting` now proves a
separate stored-table implementation equal to those counts; it does not
enumerate assignments. Local approximation accuracy and its connection to the
full controller remain separate obligations.

### Weak colour inequalities and strict physical comparisons

These are intentionally separate. For two unconstrained labels and two
colours there are four maps. Each weak answer retains three maps, because the
two tied maps belong to both answers. Thus the two child counts sum to the
parent count plus the tie count, not to the parent count alone.

More seriously, a three-edge directed cycle has three weak maps on a
three-colour palette: all labels can have the same colour. Its three strict
physical answers have no realizing ranking. `Examples.lean` proves both
facts. The controller must therefore establish public-order consistency
using the routing invariants. Nonempty weak-map counts cannot substitute
for that argument.

### Logs, signed credits, and zero cases

`Accounting`, `GroupEntropy`, and `Endpoints` use natural logarithms.
`ComparisonBound` uses the existing `nLog2n` definition, which divides by
`Real.log 2`. The conversion must remain explicit when the controller is
assembled.

Daughter births increase the auxiliary count. Their logarithmic contribution
is negative loss, and the accounting theorems preserve that sign. For cheap
pins they prove `k log A - log(k!) ≤ A`, so repeated admissions at one child
have a bounded total debit. The bound is not charged separately at every
admission.

Zero rows, cells, and columns in the entropy arrays are handled explicitly.
Pools with no free labels are also included in the terminal product bound.
Probability lemmas which need a genuine normalized law require positive
parent counts in their statements.

## What remains before the full theorem is proved

1. **The local probability error.** Construct and verify the conditional
   refresh coupling, prove the discrepancy moment contraction, and combine
   it with the insertion/near-tie estimate to bound the difference between
   full and truncated laws. `local_choice_retains` currently takes those
   error inequalities as hypotheses. The truncated system must use the
   *original propagated windows* while retaining the sparse generating
   graph; taking arbitrary original lists is not a proved substitute.

2. **The efficient counting algorithm.** Verify the ideal-state dynamic
   program against the exact finite semantics. For a run of palette levels
   with the same transition matrix, admissible ideal states must exclude
   expired and not-yet-available unary intervals before the `I+V` argument
   is used. Then establish the operation and integer bit-length bounds.

3. **Calibrated pins and the changing palette dictionary.** Formalize the
   marginal log-concavity injection and noisy-CDF interval lemma; implement
   stable binary-counter batches and aligned dyadic hubs; prove the lifetime
   dictionary bound and the two-admissions-per-colour cap within a scale
   group. The current code inequalities do not establish the dictionary
   hypotheses for a particular implementation.

4. **The recursive controller.** Implement pools, delegation, pins, physical
   and numerical records, and repairs. Prove initialization, preservation,
   termination, legality, and the correspondence between actual promotions
   and the arrays/witnesses used in the accounting lemmas. This includes
   path reservations, retesting degree witnesses, retiring rows at strict
   walls, and preserving dormant child laws during births. Prove the
   complete singleton safety test and its compatibility with the inner-pin
   test. The local routing lemmas are not a proof that a complete run
   preserves all these invariants.

5. **Uniform asymptotics and machine cost.** Instantiate the stage-cost
   function with the manuscript's actual arithmetic and oracle parameters;
   prove the signed hub-price estimate and the resulting error functions
   vanish; apply `comparison_guarantee_of_vanishing_accounting`; and verify
   a fixed polynomial bit-cost bound for the constructed strategy. The
   existing bound on the number of affordability tests does not bound the
   cost of evaluating an arbitrary supplied stage-cost function.

For the uniformization step, preserve the manuscript's stronger cheap-cost
cap `(4^B W0)^2 ≤ log₂(n+1)`, equivalently
`4^B W0 ≤ sqrt(log₂(n+1))`. The square root is garbled in extracted PDF text;
the implementation paragraph explicitly describes capping the square.
Dropping this square would not make the corresponding linear remainder
negligible by the stated argument.

These are substantial remaining proof obligations. There is no theorem in
this contribution asserting that they have been discharged.

## Build and audit

Use the pinned `lean-toolchain` and `lake-manifest.json`:

```bash
lake exe cache get
lake build SortingAdversary.Optimal
lake env lean SortingAdversary/Optimal/Audit.lean
./scripts/check-trusted-no-sorry.sh
lake build SortingAdversary
```

The new namespace permits only Lean's standard `propext`, `Classical.choice`,
and `Quot.sound` axioms. It does not inherit the legacy curvature
certificate's native-evaluator exception. The full root continues to include
the older result and its separately documented trust boundary.

The finite examples use ordinary `decide`, whose resulting proof is checked
by the kernel. They are sanity checks of the model and do not replace
universal theorems or the missing complexity analysis.
