# Recursive colour adversary: comparison theorem and implementation costs

## Status

This directory formalizes the construction and components of the 7 November 2026 manuscript,
*An asymptotically optimal deterministic adversary for comparison sorting*.
**The unconditional leading-one online comparison theorem is proved.**
`UniformAdversary.asymptoticallyOptimal` applies to the actual executable
uniform family. The separate whole-program polynomial bit-cost theorem
remains under construction.

The files contain proofs, executable finite reference definitions, the actual
controller, and its complete comparison accounting. There are no admitted
proofs or custom axioms. General reductions such as
`comparison_guarantee_of_vanishing_accounting` retain their explicit hypotheses;
`UniformOptimal` discharges the corresponding obligations for the constructed
family and proves the unconditional result.

The source used for this development is the eleven-page manuscript dated
7 November 2026. Its PDF SHA-256 is
`353eeb213b15809abcd4c3de8ecce4137dce3f7c47734a80e2c8391049ceae70`.
The new construction is different from the curvature construction already in
the repository. None of its main lemmas is inferred from that older theorem.

## Measured implementation checkpoint

The measured primitive implementations now include exact local subset counting,
integer-size bounds, Euclidean normalization of rational probabilities, sparse
walk and longest-path tables, window and repair selectors, hub enumeration and
sorting, final-ranking construction, and finite stage-radius evaluation.
Their costs include the input callbacks they actually evaluate.

`RepresentationWork` through `RepresentationRealize` give cached, counted
representations of the actual local state. Both endpoint promotion branches,
interior promotion, cuts, fresh admissions, and cache rebuilds have exact
state-erasure proofs and explicit work bounds. `MeasuredPin` constructs the
actual pin update from measured window scans. The stored controller now also
materializes source/active rows and both palette-permutation directions.
`BoundedControllerMachine` proves that an equivalent executable controller
can discard its physical clock after freezing, keeping subsequent answers
from growing an unnecessary unbounded integer.

These are checked implementation components. The measured repair loops,
recursive routing, and complete polynomial bit-cost composition remain under
construction; the primitive bounds alone do not establish that final theorem.

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
The concrete recursive controller and its whole-run comparison bound are now
implemented and checked. Polynomial bit cost has a separate proof obligation.

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
enumerate assignments. The later local-accuracy and controller modules connect that implementation
to the full controller.

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

## Local laws, calibrated choices, and actual representative records

The next continuation proves the finite local comparison approximation rather
than taking its error bound as an oracle assumption. `FiniteProbability`,
`LocalCoupling`, `ClockContraction`, `SystematicCoupling`, `LocalMoments`,
`CouplingHistory`, and `ClockStationarity` build an actual rational common-clock
coupling and prove both uniform marginals and its moment contraction. The
factorial-sized clock grid is an auxiliary proof space; the algorithm does not
sample or enumerate it.

`GraphBalls`, `BallSchedule`, and `NumericalGeometry` instantiate the shrinking
neighbourhoods using the actual raw sparse rows. They prove the closure/reachability
correspondence, finite ball cardinal bounds, the bounded comparable set, and
propagated-window identities. `TruncatedLaw` identifies full-carrier truncation
with the genuinely smaller induced weak system. `LocalParameters` supplies
explicit rational/integer parameters. `LocalAccuracy.comparison_accuracy`
then proves the exact induced two-ball probability is within the requested
error, under the stated degree, height, component-width, and minimum-width
conditions. `CDFAccuracy` supplies the fixed-threshold cumulative endpoint.
`IsolatedAccuracy` removes the minimum-width condition on isolated marks,
including mixed isolated/nonisolated comparisons; fully isolated queries are exact.

`FiniteInsertion` transfers integer compression estimates to the actual finite
weak-map laws. It includes near-tie and fixed-threshold probability bounds,
arbitrary restricted-coordinate counts, and central-colour fibre lower bounds.
This transfer is proved through an explicit finite-palette embedding.

`ComponentSwap` constructs and inverts the marginal counting injection.
`MarginalCalibration` proves the resulting actual weak-map marginal is
log-concave, while `DiscreteCalibration` supplies the finite reverse-hazard
argument. The executable first-crossing rule is proved to return an interval
of length m in which **every colour, including both endpoints, has true mass
at least 1/(16m)**. No log-concavity premise is supplied by an oracle.

`StableBatches` implements the binary-counter batch partition. `HubSelector`
selects a largest admissible aligned block and verifies the typed hub veto.
`BatchWindows` derives batch windows from actual palette positions.
`HubPricing.history_signed_debit_le` computes destination multiplicities and
largest records from a finite selection history, decodes those actual records
into the lifetime dictionary, and derives the signed-price envelope. This
removes the earlier requirement to supply a code or maximum-block theorem as
an independent hypothesis. `ControllerPricing`, `ControllerEventCounts`, and `ControllerPriceBudget` now
produce that actual history and establish its population and group-separation
invariants.

`Promotion.promote` is a single executable parent operation covering interior,
lower-endpoint, and upper-endpoint choices. Its result includes the updated
system and pins, immutable-colour embedding, true fibre-count retention,
independence from old destination members, and the complete local invariant.
`ordinary_price` connects the calibrated fibre bound to this actual operation.

`CutNormalization` proves both strict width cuts, their exact rejected-width
count bounds, retention of at least `1-C/L`, preservation of the local invariant,
and equality after retiring a row already implied by the artificial walls.
`PinElimination` proves exact maps, counts, events, and expectations when pinned
coordinates are isolated and their consequences retained in propagated walls.

`PoolState` implements actual membership on the fixed label carrier, proves root
initialization and empty-child counts, and supplies executable birthday admissions
with their palette embeddings and exact count multiplier. `AsymptoticRates`
proves the explicit normalized terminal, squared-cap cheap, regular, and scale
remainders tend to zero, together with the physical/cut overhead. `UniformOptimal` instantiates these analytic results with the actual
controller's proved finite accounting inequality.

## Concrete tree, sparse history, and chronological accounting

The next checked layer contains the stored recursive tree and the actual
parent/child mutations. `PoolTree`, `TreePromotion`, `TreePromotionCount`,
`TreeOrder`, and `PoolPalette` prove exact child membership, immutable-key
transport, independent birthdays at the real destination, preservation of
public-order restrictions, and palette caps. `SeparatedPins` ensures that a
moved label keeps a comparable member outside its destination; this proves
strictly smaller child populations and the actual `2s-1` node bound.

`TreeRoutingBase`, `TreeReplacement`, and `TreeRouter` implement recursive
routing through the child containing both queried labels. The ancestor count
is unchanged, the shared child's new public order agrees with its parent,
and an exact product identity transfers the stopping subtree's retained
fraction to the root. `StoppingComparison` executes the safety tests, excludes
same-child delegation at a stopping node, and chooses the larger of the two
certified rational estimates. It proves the retained fraction `1/2-error`.
`StoredRouting` and `RecursiveController` now instantiate that router with
the complete stored repair-and-metadata program.

`NumericalRepresentation` retains proper primitive source rows separately from
active rows. Every retired source row is justified by a physical pin or
strict separation of primitive artificial walls. Its sparse numerical view
has exactly the original maps, counts, events, fibres, and effective windows.
Both endpoint splits, physical pins, strict cuts, fresh admissions, and new
comparison rows preserve this representation. In particular, no derived
propagated bound is silently stored as an artificial wall before a split.

`SparseRepairGraph` computes a longest path in a materialized table using
original label identities and a topological rank, proves actual reservation
properties, and supplies the decreasing free-label/active-row measure.
`ScaleGeometry`, `ScalePinPreservation`, `ScaleHubs`, and `ScaleMass` prove the
first-crossing scale labels, their separation and unchanged windows, the
actual typed-veto group length and two-per-child cap, and central-insertion
prices at the selected hubs. `PaletteBirthOrder` extends chronological colour
permutations through both endpoint splits and top appends. `Reindexing`
removes any ordering assumption on the original label indices from both
comparison and CDF accuracy.

`IncidenceLedger` and `GroupReservations` execute and validate finite action
sequences, deriving incidence budgets, disjoint completed reservations, and
entropy arrays from the recorded actions. `PoolTreeAccounting`,
`PoolTreeTraversal`, and `PoolTreeGroups` identify those arrays with actual
child populations and prove exact free-label conservation, population and
promotion identities, and the entropy telescope. `TreeChronology` proves
immutable-node allocation and that each actual promotion increases the tree's
promotion total by one. `LedgerStoredReplay` and `LedgerStructuralReplay` now prove that the actual
local normalizer emits an accepted incidence ledger through the concrete child
updates. The subsequent `LedgerRun`, `ReservationEntropyRun`, and
`ControllerFinalPrice` modules complete the whole-query delegation and
reservation/pricing aggregation.

`TreeTerminal` derives each actual pool's stars-and-bars bound from inherited
public totality, aggregates the real product count, and uses the preserved
palette caps for the terminal logarithmic remainder. Correct sorting supplies
the root totality through the repository's transcript semantics.

### Concrete controller and uniform construction

`LocalOracle` calls the verified materialized ideal-state DP on the actual
sparse balls; `LocalOracleWork` bounds its table visits and integer sizes.
`WidthRepair`, `WidthNormalize`, `WidthScaleSelect`, `WidthInterior`, and
`WidthScale` execute all three width priorities, including completed typed
scale reservations. `OrdinaryPromotion` records actual post-split destination
identities. `StructuralNormalize` executes degree repair and reserved paths,
including skipped labels and a final reserved label that becomes isolated.
The entire local repair uses at most `n+n²` primitive operations.

`StoredTree`, `StoredPromotion`, `StoredRepair`, and `StoredRouting` retain
public matrices, sparse source rows, and chronological palette permutations.
The replay updates the actual receiving child and divides the parent charge
by the exact birthday multiplier. `PassiveLocalState` and `StoredReady` prove
that isolated child admissions and equal-colour delegation preserve the
maintained local conditions. `NormalizedBounds` computes the actual ranks and
derives every local-oracle premise used by `RecursiveController`.

`OnlineMachine` proves equality between direct stateful execution and the
repository's transcript-dependent `Strategy` semantics. `ControllerMachine`
counts every physical query, handles implied answers, materializes stored
matrices between queries, and fixes a compatible ranking at its cutoff.
`UniformAdversary.strategy` uses the concrete bounded stage selector, with a
fixed-order fallback on small inputs. **`UniformAdversary.consistent` proves
unconditional legality for all input sizes and all finite comparison trees.**
`UniformAdversary.asymptoticallyOptimal` adds the leading-one comparison bound
for this same family.

`CappedArithmetic`, `CappedStageScan`, `StageScalars`, `StageRecipe`,
`StageParameters`, `UniformStage`, and `UniformController` implement and prove
the uniform constructor. Huge rejected exponents are checked by capped
arithmetic. Accepted packages discharge the controller's scalar hypotheses,
cap both actual oracle ball allowances by `log₂(n+1)`, and cap the square of
the cheap promotion price. The selected stage tends to infinity. The measured
arithmetic work and integer-size bounds include rejected candidates.

`LedgerBirthCredits` and `LedgerReplayPrices` emit actual child-admission
receipts and prove that their logarithmic credits telescope to the change in
the ledger's factorial potential. The signed count-loss theorem uses those
real receipts; it does not assume a factorial schedule.

`ControllerRun` and `ActiveTerminal` connect the stateful execution to the
actual active response sequence and the terminal totality/count estimate.
`LedgerQuery`, `LedgerRouter`, `LedgerController`, and `LedgerRun` derive an
accepted chronological ledger for that sequence, hence the actual final-tree
promotion bound `P ≤ 2q` and degree bound `D * degreeCount ≤ 2q`.
`LedgerControllerPrices` and `LedgerRunPrices` telescope the emitted birthday
receipts and the counting-potential drop over the full run.

The `Reservation*` modules through `ReservationFinalGroups` execute two
separate pending reservation books alongside that same actual ledger. Every
path group has `H` original labels, every scale group has `J`, groups of each
type are disjoint, and the actual final physical destinations have the required
path/scale multiplicities. Nested scale repairs inside a pending path are
covered. `RepairPricing`, `RepairPersistence`, `RepairEvolution`, and
`ControllerPricing` extract the actual immutable hub history and prove that
all its records still fit their real final stored node.

`StoredRowPotential`, `RepairCuts`, `CutAccounting`, and `CutRun` prove that
the cuts emitted by the real complete active execution number at most `q`.
Child admissions preserve the descendant active-row contribution, delegated
queries preserve ancestor active rows, and each stopping query adds at most
one row. `CutoffBounds` proves the implemented clock dominates `n log₂ n`
and is eventually at most `4 n log n`. `UniformRates` proves the rates for
the actual bounded selector, including the evaluated cheap charge and cut
error. `UniformComparisonReduction` is the scalar closing reduction; its
finite active-run inequality is now supplied by the actual global price
aggregation in `UniformOptimal`.

## Unconditional leading-one theorem

`TreeReservationEntropy` and `ReservationEntropyRun` turn the completed actual
path and scale groups into the global entropy budgets. `LedgerPromotionTrace`,
`ControllerLedgerAlignment`, and `TreeFactorialCredit` identify the birthday
receipts with the real final child factorials. `ControllerEventCounts` relates
the actual cheap, degree, path, and scale records to those tree populations.

`StoredStateIndex`, `TreePriceBudget`, and `TreePriceEntropy` build the finite
final dictionary over actual stored nodes and immutable child identities.
`IndexedHubHistory` and `SlotHubHistory` place every actual hub in that
dictionary. `CheapHubPrice` splits each child's single factorial credit between
cheap and expensive admissions. `ControllerFinalPrice.actual_price` proves the
resulting whole-run inequality with only an actual `ActiveRun` as a premise.
`ControllerPriceBudget.actual_budget_bounds` bounds its dictionary budget by
`256 n ln n` under the physical clock; all populations and counts are derived.

`UniformRunBudgets` proves the selected-stage hub-mass and scale-surcharge
bounds from the actual incidence and reservation histories. `UniformExecution`
recovers the exact selected controller run from the repository's sorting-tree
semantics. `UniformOptimal.selected_comparison_budget` combines these facts,
the actual terminal estimate, and the cut count into the finite comparison
inequality. Its closing theorem is:

```lean
theorem UniformAdversary.asymptoticallyOptimal :
    AsymptoticallyOptimal UniformAdversary.strategy
```

Unfolding the specification gives consistency for every input size and every
finite comparison tree, together with:

```text
for every δ > 0, there exists N such that for every n ≥ N
and every correct comparison tree t on n labels,
  (1 - δ) n log₂ n ≤ comparisons made against UniformAdversary.strategy n.
```

The theorem has no mathematical hypotheses. The actual selected stage tends
to infinity, all relative remainder terms tend to zero, and runs exceeding
the actual cutoff satisfy the comparison bound directly. The corollary
`UniformAdversary.worst_case` supplies a genuine ranking input of each correct
sorter with the same lower bound. This is an online adversary theorem for the
constructed family, not a conditional accounting reduction.

## Remaining whole-program cost obligation

The actual stage constructor, local DP, graph tables, repair length, palette
sizes, and tree sizes have checked bounds. Those bounds must still be composed
for the complete stateful program, including lookup and arithmetic costs. In
particular, function-valued sparse metadata must pay for its stored update
history, and every counted implementation must be connected to the actual
controller's result. A polynomial bound for a component is not a full
program-cost theorem.

For the uniformization step, preserve the manuscript's stronger cheap-cost
cap `(4^B W0)^2 ≤ log₂(n+1)`, equivalently
`4^B W0 ≤ sqrt(log₂(n+1))`. The square root is garbled in extracted PDF text;
the implementation paragraph explicitly describes capping the square.
Dropping this square would not make the corresponding linear remainder
negligible by the stated argument.

No whole-program polynomial bit-cost theorem is claimed at this checkpoint.

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
