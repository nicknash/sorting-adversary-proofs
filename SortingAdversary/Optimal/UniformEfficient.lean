import SortingAdversary.Optimal.UniformBitResources
import SortingAdversary.Optimal.UniformMachineWork
import SortingAdversary.Optimal.HubBitBounds
import SortingAdversary.Optimal.UniformOptimal
import SortingAdversary.Optimal.UniformInitializationBits

/-!
# One executable optimal adversary with certified polynomial resources

`ProgramOperands` follows the two concrete constructors returned by `build`.
Its admitted case includes the operand certificates for every actually
reachable active state, and therefore does not extend a binary-time claim
to arbitrary records with unbounded allocator counters. Frozen states hold
only finite ranks. `queryBitCost` requires this certificate and charges the
actual measured state transition in the stated bounded-operand schoolbook
model. The transcript in its argument identifies a reachable state; it is
not replayed by the online implementation.
-/

namespace SortingAdversary.Optimal.UniformEfficient

open UniformBitResources UniformMachineWork UniformStage UniformRepairWork
open RepresentationWork WidthRepair PrimitiveWork

variable {n j : ℕ}

theorem finite_label_bits (n : ℕ) (v : Fin n) : Nat.size v.val ≤ bits n := by
  apply (size_of_le v.isLt.le).trans
  exact (Nat.le_succ _).trans (by simpa using small_polynomial_le n 1 1 (by decide) (by decide))

theorem frozen_rank_bits (n : ℕ) (f : ControllerMachine.Frozen n) (v : Fin n) :
    Nat.size f.ranks[v].val ≤ bits n := finite_label_bits n _

def RankOperands (n : ℕ) : Prop :=
  (∀ (rows : RankWork.Rows n) (v : Fin n),
    Nat.size ((RankWork.keys (RankWork.predecessors rows).value).value[v]) ≤ bits n) ∧
    (∀ (f : ControllerMachine.Frozen n) (v : Fin n), Nat.size f.ranks[v].val ≤ bits n)

theorem rank_operands (n : ℕ) : RankOperands n := ⟨rank_key_bits, frozen_rank_bits n⟩

def HubOperands (n : ℕ) : Prop :=
  ∀ births, births ≤ localCap n + 1 →
    HubBitBounds.binaryBound births ≤ bits n ∧
      (∀ block ∈ (HubEnumerationWork.allBlocks births).value, HubBitBounds.BlockOperands births block) ∧
      (∀ lo hi veto block, (HubWork.selectBlock births lo hi veto).value = some block →
        HubBitBounds.BlockOperands births block) ∧
      (∀ rank lower upper count block,
        block ∈ (HubWork.selectPaletteGroup births rank lower upper count).value →
          HubBitBounds.BlockOperands births block)

theorem hub_operands (n : ℕ) : HubOperands n := by
  intro births hb
  refine ⟨?_, fun block h => HubBitBounds.block_operands h,
    fun lo hi veto block h => HubBitBounds.selected_operands lo hi veto h,
    fun rank lower upper count block h => HubBitBounds.paletteGroup_operands births rank lower upper count h⟩
  apply (HubBitBounds.binaryBound_mono hb).trans
  have h : HubBitBounds.binaryBound (localCap n + 1) ≤ 100 * (n + 1) ^ 4 := by
    unfold HubBitBounds.binaryBound localCap
    ring_nf
    gcongr <;> norm_num
  exact h.trans (small_polynomial_le n 100 4 (by decide) (by decide))

/-- These fields refer to the actual stage's computed powers, intervals,
and rational receipts. They also cover every recursive power prefix. -/
structure StageOperands (a : Accepted (Parameters.logCap n) j) : Prop where
  radii : Nat.size (UniformPreparedWork.prepare a).value.repair.radius ≤ bits n ∧
    Nat.size (UniformPreparedWork.prepare a).value.comparisonRadius ≤ bits n
  radiusIntermediates : ∀ E ∈ [16, 100 * j],
    let H := a.runtime.normalizer.scale.H
    let M := LocalAccuracy.influenceSize H a.runtime.normalizer.d
    Nat.size (LocalParameters.clockScale M ^ H) ≤ bits n ∧
      Nat.size (4 ^ (2 * M)) ≤ bits n ∧
      Nat.size (LocalParameters.momentOrder H M) ≤ bits n ∧
      Nat.size (LocalParameters.insertionConstant M) ≤ bits n ∧
      (∀ value ≤ StageScalars.sweeps H M a.runtime.normalizer.scale.R E,
        Nat.size value ≤ bits n)
  localPowers :
    (∀ e ≤ a.runtime.normalizer.scale.H + 1,
      Nat.size (WidthScalarWork.power (a.runtime.normalizer.d + 1) e).value ≤ bits n) ∧
    (∀ e ≤ a.runtime.normalizer.scale.H,
      Nat.size (WidthScalarWork.power
        (LocalParameters.clockScale (LocalAccuracy.influenceSize a.runtime.normalizer.scale.H
          a.runtime.normalizer.d)) e).value ≤ bits n) ∧
    (∀ e ≤ 2 * LocalAccuracy.influenceSize a.runtime.normalizer.scale.H a.runtime.normalizer.d,
      Nat.size (WidthScalarWork.power 4 e).value ≤ bits n)
  scalePowers :
    (∀ e ≤ 2 * a.runtime.normalizer.scale.H + 3,
      Nat.size (WidthScalarWork.power (a.runtime.normalizer.scale.width.L + 1) e).value ≤ bits n) ∧
    (∀ e ≤ a.runtime.normalizer.scale.J + 1,
      Nat.size (WidthScalarWork.power a.runtime.normalizer.scale.A e).value ≤ bits n)
  cheap : Nat.size (a.runtime.normalizer.scale.width.W₀ * 4 ^ a.runtime.normalizer.scale.width.B) ≤ bits n
  cut : Nat.size (WidthScalarWork.cut a.runtime.normalizer.scale.width).value.num.natAbs ≤ bits n ∧
    Nat.size (WidthScalarWork.cut a.runtime.normalizer.scale.width).value.den ≤ bits n
  widths : ∀ (s : WidthRepair.State n), s.pool.palette ≤ localCap n → ∀ v,
    Nat.size (a.runtime.normalizer.scale.width.L * s.width v) ≤ bits n ∧
      Nat.size (a.runtime.normalizer.scale.R * s.width v) ≤ bits n
  thresholds : ∀ (s : WidthRepair.State n), s.pool.palette ≤ localCap n → ∀ v i,
    i ≤ a.runtime.normalizer.scale.J + 1 →
    Nat.size ((WidthScalarWork.power a.runtime.normalizer.scale.A i).value * s.width v) ≤ bits n
  ordinary : ∀ length, length ≤ localCap n + 1 → Nat.size (16 * length) ≤ bits n
  scale : ∀ length palette, palette ≤ localCap n → length ≤ palette + 1 →
    Nat.size (2 * 4 ^ a.runtime.normalizer.scale.width.B * length) ≤ bits n

theorem stage_operands (a : Accepted (Parameters.logCap n) j) : StageOperands a where
  radii := prepared_radius_bits a
  radiusIntermediates E hE := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hE
    rcases hE with rfl | rfl
    · have h := UniformScalarWork.cdf_intermediates a
      exact ⟨capped_scalar_bits h.1, capped_scalar_bits h.2.1,
        capped_scalar_bits h.2.2.1, capped_scalar_bits h.2.2.2.1,
        fun _ hv => capped_scalar_bits (hv.trans h.2.2.2.2)⟩
    · have h := UniformScalarWork.comparison_intermediates a
      exact ⟨capped_scalar_bits h.1, capped_scalar_bits h.2.1,
        capped_scalar_bits h.2.2.1, capped_scalar_bits h.2.2.2.1,
        fun _ hv => capped_scalar_bits (hv.trans h.2.2.2.2)⟩
  localPowers := stage_power_bits a
  scalePowers := stage_base_power_bits a
  cheap := stage_cheap_bits a
  cut := stage_cut_bits a
  widths := stage_width_bits a
  thresholds := stage_threshold_bits a
  ordinary _ h := ordinary_receipt_bits h
  scale _ _ hp hl := stage_scale_receipt_bits a hp hl

/-- An indexed certificate for the exact executable program constructors.
The admitted constructor demands the real replay-state certificate; the
fixed constructor holds no growing state. No time bound is a field here. -/
inductive ProgramOperands : {n : ℕ} → Program n → Prop
  | fixed (n : ℕ)
      (actual : (UniformAdversary.fixedMachine n).strategy = UniformAdversary.strategy n)
      (labels : ∀ v : Fin n, Nat.size v.val ≤ bits n) :
      ProgramOperands (UniformMachineWork.fixed n actual)
  | admitted (N j : ℕ) (a : Accepted (Parameters.logCap (N + 2)) j)
      (hstage : selectController (N + 2) = some a.controller)
      (stage : StageOperands a) (hubs : HubOperands (N + 2)) (ranks : RankOperands (N + 2))
      (reachable : ∀ (past : History (N + 2))
        (clock : Fin (UniformAdversary.cutoff (N + 2) + 1))
        (state : MeasuredController.Active a.controller (N + 2)),
        (MeasuredController.machine a.controller N (UniformAdversary.cutoff (N + 2))
          (UniformRoutingWork.executor a (UniformPreparedWork.prepare a).value)).replay past =
            .active clock state → ActiveOperands clock state) :
      ProgramOperands (UniformMachineWork.admitted N a (UniformPreparedWork.prepare a).value
        (UniformAdversary.cutoff (N + 2)) rfl (MeasuredController.Active.initial a.controller N) rfl hstage)

theorem admitted_operands (N : ℕ) (a : Accepted (Parameters.logCap (N + 2)) j)
    (cutoff : ℕ) (hclock : cutoff = UniformAdversary.cutoff (N + 2))
    (initial : MeasuredController.Active a.controller (N + 2))
    (hi : initial = MeasuredController.Active.initial a.controller N)
    (hstage : selectController (N + 2) = some a.controller) :
    ProgramOperands (UniformMachineWork.admitted N a (UniformPreparedWork.prepare a).value
      cutoff hclock initial hi hstage) := by
  subst cutoff initial
  exact .admitted N j a hstage (stage_operands a) (hub_operands _) (rank_operands _)
    (active_operands (UniformRoutingWork.executor a (UniformPreparedWork.prepare a).value))

theorem afterSelection_operands (N : ℕ) (selected : UniformSelectionWork.Selected (N + 2)) :
    ProgramOperands (UniformMachineWork.afterSelection N selected).value := by
  unfold UniformMachineWork.afterSelection
  split
  · exact .fixed _ _ (finite_label_bits _)
  · rename_i j hj a hselected
    have hstage : selectController (N + 2) = some a.controller := by
      unfold selectController
      rw [← selected.actual, hselected]
    exact admitted_operands N a _ (UniformMachineWork.clock_value _)
      _ (UniformInitialWork.active_eq _ _) hstage

/-- The concrete build returns a program with the complete resource
certificate, with no hypothesis on input size, stage, or caller transcript. -/
theorem built_resources (n : ℕ) : ProgramOperands (build n).value := by
  cases n with
  | zero => exact .fixed _ _ (finite_label_bits _)
  | succ n =>
    cases n with
    | zero => exact .fixed _ _ (finite_label_bits _)
    | succ N => exact afterSelection_operands N (UniformSelectionWork.choose (N + 2)).value

def strategy (n : ℕ) : Strategy n := (build n).value.machine.strategy

theorem strategy_eq : strategy = UniformAdversary.strategy := by
  funext n
  exact UniformMachineWork.strategy_eq n

theorem asymptoticallyOptimal : AsymptoticallyOptimal strategy := by
  rw [strategy_eq]
  exact UniformAdversary.asymptoticallyOptimal

/-- Binary cost is asserted only together with a certificate of the exact
program's reachable operands. This proof argument erases. -/
def queryBitCost (n : ℕ) (_resources : ProgramOperands (build n).value)
    (past : History n) (query : Query n) : ℕ :=
  RationalBitWork.Model.charge
    ((build n).value.step ((build n).value.machine.replay past) query).work (bits n)

theorem query_bit_polynomial (n : ℕ) (resources : ProgramOperands (build n).value)
    (past : History n) (query : Query n) :
    queryBitCost n resources past query ≤ 10000000000000000000000000 * (n + 1) ^ 32 := by
  unfold queryBitCost
  apply (RationalBitWork.Model.charge_mono
    (UniformMachineWork.per_query_polynomial n _ query) le_rfl).trans
  apply (charge_polynomial n 4000000000000 16).trans
  exact Nat.mul_le_mul_right _ (by decide)

/-- Initialization uses the same binary width, backed by the certificate
for the actual capped evaluator, compiler, and constructed initial state. -/
def initializationBitCost (n : ℕ)
    (_resources : UniformInitializationBits.InitializationOperands n) : ℕ :=
  RationalBitWork.Model.charge (build n).work (bits n)

theorem initialization_bit_polynomial (n : ℕ)
    (resources : UniformInitializationBits.InitializationOperands n) :
    initializationBitCost n resources ≤
      100000000000000000 * (UniformStage.recipeSize + 1) * (n + 1) ^ 18 := by
  unfold initializationBitCost
  apply (RationalBitWork.Model.charge_mono
    (UniformMachineWork.initialization_polynomial n) le_rfl).trans
  apply (charge_polynomial n (10000 * (UniformStage.recipeSize + 1)) 2).trans
  apply Nat.mul_le_mul_right
  calc
    10000 * (UniformStage.recipeSize + 1) * 1000001 ^ 2 =
        (10000 * 1000001 ^ 2) * (UniformStage.recipeSize + 1) := by ring
    _ ≤ 100000000000000000 * (UniformStage.recipeSize + 1) :=
      Nat.mul_le_mul_right _ (by decide)

/-- One concrete uniform online program realizes the verified optimal
adversary. Its actual initializer and every reachable query transition
have polynomial cost in the explicit bounded-operand schoolbook model.

The operand certificates are part of the conclusion: the query assertion
does not silently quantify over externally constructed active states with
arbitrarily large allocation counters. The cost model charges the measured
primitive program and uses the proved finite operand families; it does not
assert timing of Lean's native integer implementation. -/
theorem efficientOptimal :
    strategy = UniformAdversary.strategy ∧
      AsymptoticallyOptimal strategy ∧
      (∀ n, ProgramOperands (build n).value) ∧
      (∀ n, UniformInitializationBits.InitializationOperands n) ∧
      (∀ n, initializationBitCost n (UniformInitializationBits.initialization_operands n) ≤
        100000000000000000 * (UniformStage.recipeSize + 1) * (n + 1) ^ 18) ∧
      (∀ n (past : History n) (query : Query n),
        queryBitCost n (built_resources n) past query ≤
          10000000000000000000000000 * (n + 1) ^ 32) :=
  ⟨strategy_eq, asymptoticallyOptimal, built_resources,
    UniformInitializationBits.initialization_operands,
    fun n => initialization_bit_polynomial n _,
    fun n past query => query_bit_polynomial n _ past query⟩

end SortingAdversary.Optimal.UniformEfficient
