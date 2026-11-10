# Continuous adversary: theorem map and verification boundary

The current manuscript is formalized in `SortingAdversary/Continuous/`.
The main theorem concerns the actual continuous adversary and the shared
comparison-tree semantics in `Basic.lean`, `DecisionTree.lean` and
`Strategy.lean`.

The manuscript baseline checked for this synchronization is commit
`42a7f75b8e03238dbc101501e21dc844138c07d3` (10 November 2026). Its PDF has
SHA-256 `3fbb0ce35f85b95659f6b5874b436400e46aed1a3489cd0d3f383bfbbdb364b6`.
The changes since the initial audit at `20040a98` preserve the construction,
constants and main theorem; they add exposition and conditional counting
consequences.

## Main exported statements

All names in this section are in `SortingAdversary.Continuous`.

| Statement | Lean entry point | Meaning |
| --- | --- | --- |
| Actual comparisons terminate and preserve the invariants | `Controller.compareGuarantee` in `ControllerCorrect.lean` | Every ready state at `k ≥ 64` answers the query, returns another ready state, and generates a valid accounting trace. |
| Every completed prefix retains sufficiently many orders | `Controller.prefix_count` | `log₂(n!) − (1 + prefixOverhead k)q ≤ log₂ T_q`, where `T_q` counts all transcript-compatible rankings. |
| One uniform legal adversary | `UniformAdversary.strategy`, `UniformAdversary.consistent` | A single deterministic parameter-selection program works for every input size and every finite comparison tree. |
| Leading-one online lower bound | `UniformAdversary.asymptoticallyOptimal` | For every real `δ > 0`, every correct sorter makes at least `(1−δ)n log₂ n` comparisons for all sufficiently large `n`. |
| Ordinary worst-case sorting input | `UniformAdversary.worst_case` | The same lower bound is realized by a genuine ranking input of every correct sorting tree. |
| Target-independent production | `UniformAdversary.production`, `error_tendsto` | The same initialized family forces `(1−ε_n)(log₂(n!)−log₂ e(R))` comparisons for every production target, with `ε_n → 0`. |
| Stateful execution | `UniformAdversary.Program.execute_eq_run` | Direct stateful execution agrees with the history-based strategy. Transcript replay is a semantic presentation. |
| Concrete measured implementation | `UniformMachineWork.strategy_eq`, `per_query_polynomial`, `initialization_work` | The constructed stored program has the same strategy, quadratic initialization work and a fixed degree-seventeen primitive-work bound for every reachable query. |
| Polynomial binary charge | `UniformEfficient.asymptoticallyOptimal_and_polynomial` | The same program combines asymptotic optimality, reachable operand certificates, and fixed polynomial initialization/query charges in the stated arithmetic model. |

The main correctness and asymptotic theorems have no assumed local oracle,
volume estimate, packing inequality, accounting budget or convergence rate.
The lower-level lemmas that expose such hypotheses are discharged by the
actual controller before those final theorems are stated.

## Correspondence with the paper

### Constants and local certificates

The stage parameter satisfies `k ≥ 64`. The paper's tree-path threshold is
`H = 2^k`; the transient local DAG calculation uses the vertex bound
`pathHeight k = 2^(k+1)`.

The executable definitions use exactly:

- `B = (k+1)^(2H+1)` and `w* = 2^(-2kB)`;
- `η = 1/(100k)`, `α = η/2`, and `δ = ηw*/(8(B+1))` for both selection and anchor choice;
- the least power of two `S ≥ 4M²`, with `M = (d+1)^(h+1)`;
- the least positive moment power satisfying the contraction test;
- the least positive sweep count satisfying the calibrated bad-width test;
- the retained radius `h t + 1`, with only the radius-`h t` interior updated.

`FiniteAveraging.lean` implements the affine digit update over rationals and
reals. `EnclosureParameters.lean` gives the exact searched parameters;
`ParameterBounds.lean` supplies explicit finite search envelopes.
`Stationarity.lean`, `EnclosureDistribution.lean`, `FiniteDependence.lean` and
`EnclosureGuarantee.lean` prove stationarity, contraction and locality.

`InducedEnclosure.lean` and `Neighborhood.lean` construct the retained graph
before computing its topological order. The one additional boundary layer is
frozen. `Neighborhood.enclose_full` identifies the local endpoint entries,
including their multiplicities, with the embedded schedule in the original
graph. Thus probability certificates are sound for the uniform distribution
on the original full feasible region. The argument does not replace that
measure by an unrelated marginal distribution on the retained graph.

`Certificates.lean`, `LocalSelection.lean`, `CertificateSuccess.lean`,
`NeighborhoodCertificates.lean` and `ArbitraryLabels.lean` implement and prove
the finite comparison and central-interval tests. They preserve the paper's
strict separation tests, answer tie rule, original-label refinement tie rule,
central order statistics, and exact upward dyadic rounding.

### Geometry and refinement

`OrderRegion.lean`, `RegionMeasure.lean`, `Density.lean`,
`ComparableDensity.lean`, `ProjectionDensity.lean`, `Conditioning.lean`,
`MarginalMeasure.lean` and `SmallDifference.lean` establish the geometric
lemmas for the actual continuous feasible region. `ComponentSwap.lean` and
`SectionConcavity.lean` supply the section-volume concavity argument.

`TreeState.lean`, `TreeRouting.lean`, `TreeVolume.lean`, `Admission.lean` and
`RationalSemantics.lean` connect rational stored data with real feasible
assignments and transcript-compatible rankings. The represented set of
orders may grow when an item enters an existing child. The invariant proved
is that every represented order still satisfies the transcript; equality
between represented orders and all compatible orders is unnecessary.

`ControllerSelection.lean` proves that selection needs at most two failed
attempts. Only the queried labels can move, and a moved label is isolated
with a unit interval and density one. It cannot meet the failed-selection
density requirement a second time before the answer.

`ControllerRepair.lean` proves correctness of the actual degree and path
batches. Path anchors are distinct, every move has the required density and
dyadic-level tariff, and one repair removes an endpoint of the inserted arc.
This restores both the strict degree and path bounds. These are properties
of the returned batches, not input certificates supplied to the controller.

### Counting all compatible orders

`Weights.lean` uses the single anchor distribution
`k^(-2)((1−1/k)/2)^m`, with total child mass `1/k` and stopping mass `1−1/k`.
`TreeSampling.lean`, `FiniteTreeLaw.lean`, `TreePacking.lean` and
`QueriedCompression.lean` prove the independent-label sampling and packing
argument. `Counting.lean` proves the free insertion of untouched labels.

The result is the paper's inequality

`T_q ≥ n! (1−1/k)^s Z W`, with `s ≤ 2q`.

`TraceAccounting.lean`, `TraceGuarantees.lean`, `ArcBudget.lean` and
`ControllerBounds.lean` derive the budgets from the actual comparison trace.
The refinement bound is at most `8q/k`. The explicit excess in the prefix
theorem is `prefixOverhead k`; `Rates.lean` proves that it tends to zero.
The volume product is not identified with the fraction of compatible total
orders: the sampling argument is the bridge between those quantities.

### Uniform parameter choice and the horizon

`UniformStages.lean` uses the generic capped-expression evaluator and stage
scan from the earlier development. Its recipe bounds the continuous
construction's scalar searches and enumeration, not the earlier colour
adversary's oracle.

The concrete selector is a conservative implementation of the paper's
slowly growing parameter choice. It checks stages `64,128,…` using a capped
upper envelope for the work and exact enumeration budget. Its cap is at most
`logCap n`, hence at most `n`. It may accept a stage later than a literal
implementation of the paper's abstract “run the generator for n steps” rule.
Every fixed stage is eventually accepted, the exact `E_k` of an accepted
stage is at most `n`, and the selector's own work and intermediate magnitudes
are bounded. The sentinel `k=32` selects the fixed-label fallback.

`Controller.horizon n = n * Nat.clog 2 n` bounds active interaction.
At the horizon the program materializes a compatible rank vector once and
uses that fixed vector for all later queries. `GraphWork.lean` counts the
closure and ranking operations, including evaluation of the stored history.
The freeze operation uses a stored closure table and cached rank vector.

`ControllerResources.lean` proves resource invariants on every replayed
query sequence, including histories whose supplied answer fields are
arbitrary. Reachable active states have total path depth at most `n²` and
endpoints on a dyadic grid of exponent at most `n³` at an admitted stage.
`ControllerWorkBounds.lean` propagates explicit depth, grid and history caps
through all intermediate states of each selection and repair.

### Concrete computation and binary arithmetic

`StateWork.lean`, `GraphScanWork.lean`, `GraphWork.lean` and
`NeighborhoodWork.lean` implement counted state updates, routing, degree and
path scans, closure, topological ordering and neighborhood construction.
The neighborhood implementation uses stored vectors and Boolean matrices;
its scans are charged in terms of the ambient input size `n`. The locality
theorem identifies the required retained graph and endpoint computation
exactly, while this implementation proves polynomial work in `n`. It does
not claim that discovering the retained neighborhood in this representation
takes time independent of `n`.

`StageWork.lean` executes the integer calibration searches, including every
failed test before success. `EnclosureWork.lean` enumerates the actual digit
words and computes their endpoint trajectories. `CertificateWork.lean`,
`RoundingWork.lean` and `SelectionWork.lean` count the finite lists, order
statistics, tests and dyadic rounding. Their returned values are proved equal
to the public selection and anchor procedures. `ConcreteRoutines.lean`
instantiates every component of the controller with these routines and
discharges their work bounds at the admitted parameter.

`UniformInitializationWork.lean` includes calculation of the logarithmic cap,
the capped stage scan, degree doublings, horizon calculation and stored-state
construction. `UniformMachineWork.lean` supplies the actual online
transition. A query takes the previously initialized program and its current
state; it does not run the semantic transcript replay. Reachability holds
initially and is preserved by every transition. Agreement with the reference
strategy holds even on histories with arbitrary supplied answer fields.

The primitive bounds are deliberately loose:

- initialization: `(7 * Recipe.budget.nodes + 100) * (n+1)^2`;
- every reachable query: `100000000000 * (n+3)^17`;
- a query after freezing: exactly ten counted operations, preserving the
  cached rank vector.

`OperandBounds.lean` proves exact rational arithmetic profiles, including
unnormalized products and Euclidean reduction. `StateOperandBounds.lean`
checks raw decoder operands and the scans used by normalization.
`RuntimeOperands.lean`
derives certificates for stored endpoints and anchor codes, routed
thresholds, all endpoint-update prefixes and affine intermediates, finite
certificate operands, rounding and decoding, and calibration tests. These
certificates hold for every admissible component call within the depth,
grid and history caps propagated by `ControllerWorkBounds.lean`.

The binary model assigns the conservative charge `128 * (B+1)^3` to a
primitive scalar operation on inputs with numerator/denominator or integer
bit widths at most `B`. Exact normalized rational addition, subtraction,
multiplication, division, comparison, min/max and ceiling have checked
profiles below this charge. The common
allowance is `B = 10000 * (n+4)^3`. `UniformEfficient.lean` charges the actual
executed primitive counter at this allowance and proves:

| Operation | Binary charge bound |
| --- | --- |
| Initialization | `((7 * Recipe.budget.nodes + 100) * (128 * 10001^3)) * (n+4)^11` |
| Every reachable query | `(100000000000 * (128 * 10001^3)) * (n+4)^26` |

All coefficients are fixed. The final theorem assumes no local cost oracle
or component budget. The binary counter is a conservative model charge,
with the actual operand families and scalar arithmetic checked separately;
it is not an instruction-level trace of a compiled Lean executable. The
formalization does not certify a compiler, native bigint library, allocator,
or practical running time at the enormous asymptotic stage thresholds.

## Supplied partial information and conditional counting

`LayerReduction.lean` defines an ordered partition by a bijection between
the original labels and the disjoint union of the layers. Its executable
strategy routes every within-layer comparison to the actual continuous
controller at a common parameter and answers cross-layer comparisons by the
fixed layer order. The proof concatenates local rankings, derives local
uniqueness from global sorting correctness, and sums the local lower bounds.

`LayerAdversary.lean` closes the public theorems with the proved continuous
controller guarantee; there is no remaining controller hypothesis.

The weak-order extension and the retention inequality

`log₂ e(P) − loss ≤ Σ_i log₂(|A_i|!)`

are explicit external inputs. With the manuscript's Cardinal et al. theorem,
`loss = O(n log log n)`, this gives its supplied-poset consequence. The
external polynomial algorithm for constructing that weak order and its
entropy theorem are not postulated as Lean axioms.

`ApproximateCounting.lean` formalizes the branch-retention and logarithmic
argument in the added approximate-counting appendix. A larger relative-error
estimate retains at least `(1−η)/2` of the current extensions; iterating the
bound and using terminal uniqueness gives the stated comparison lower bound.
This is a numerical implication with relative-error estimates, branch-sum
and selected-branch equations, and a terminal count at most one as explicit
hypotheses. It constructs neither an approximation algorithm nor a separate
counting-based strategy. The existence of the proposed deterministic
approximation algorithm remains conditional. The manuscript's open
volume-approximation questions, literature
claims, and constant-factor-to-FPTAS implementation discussion are outside
the main adversary formalization.

## Proof trust and regression checks

`Continuous/Audit.lean` imports every continuous proof module and runs an
enforced all-declaration axiom audit. It includes private declarations,
generated auxiliary declarations and declarations placed outside the main
namespace. Only `propext`, `Classical.choice` and `Quot.sound` are allowed.
A placeholder, project-specific axiom, or native evaluator dependency is a
hard error. `scripts/check-continuous-audit-imports.sh` also rejects a proof
module omitted from that audit.

`Continuous/Examples.lean` checks duplicate multiplicity, comparison ties,
strict endpoint separation, central statistics, upward rounding, dyadic
coding, actual affine updates, path ordering, routing and fallback behavior.
Its decidable checks use kernel evaluation.

The old integer-colour construction remains under `Optimal/` and retains its
own strict axiom audit. Reused modules provide generic graph algorithms,
finite loops, capped arithmetic, the shared asymptotic specification and
ordinary sorting semantics. No theorem establishing the earlier adversary's
comparison bound is used to establish the continuous adversary's bound.

Run the source gate, build and continuous trust gate with:

```sh
./scripts/check-trusted-no-sorry.sh
./scripts/check-continuous-audit-imports.sh
lake build SortingAdversary
lake env lean SortingAdversary/Continuous/Audit.lean
lake env lean SortingAdversary/Optimal/Audit.lean
LEAN_NUM_THREADS=1 lake env leanchecker SortingAdversary
```

CI runs kernel replay separately with one worker to bound peak memory.
Run the audit and replay commands sequentially on memory-constrained hosts.

The interpretation of the primitive-operation model and its relation to a
particular compiler or bigint implementation are separate from the kernel's
proof checking. The repository does not assert a measured wall-clock
performance guarantee for the enormous asymptotic stage constants.
