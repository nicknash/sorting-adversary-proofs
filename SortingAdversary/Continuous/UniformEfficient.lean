import SortingAdversary.Continuous.UniformMachineWork
import SortingAdversary.Continuous.RuntimeOperands

/-!
# The uniform adversary with a polynomial binary charge

The program here is the actual measured stateful implementation. Its values
are exactly those of `UniformAdversary`; its word counter is obtained by
executing the component loops, including initialization and rejected stages.

The binary model is explicit. An integer operation on bounded operands has
the schoolbook charge in `RationalBitWork.Model`. A rational operation is
implemented by signed integer products and the measured Euclidean reduction;
`OperandBounds` proves that `128 * (B+1)^3` covers this implementation when
the input numerator and denominator widths are at most `B`. The common
allowance is justified for the actual routine families by `RuntimeOperands`.
Multiplying the executed primitive counter by this common charge is a
conservative bound in that arithmetic model. It is not a timing theorem
about Lean's compiler, virtual machine or native big-integer library.

The degrees below are deliberately generous. They are fixed independently
of the selected parameter, transcript length and target decision tree.
-/

namespace SortingAdversary.Continuous.UniformEfficient

open SortingAdversary.Optimal
open UniformMachineWork RuntimeOperands OperandBounds

variable {n : ℕ}

def scalarCharge (n : ℕ) : ℕ := 128 * (operandBits n + 1) ^ 3

def charge (n work : ℕ) : ℕ := work * scalarCharge n

/-- The bit counter is a ghost charge; `result` executes the counted
initialization, including parameter selection and stored-state construction. -/
def build (n : ℕ) : RationalBitWork.Profile (Program n) :=
  let result := UniformMachineWork.build n
  ⟨result, charge n result.work⟩

/-- Online execution takes the previously initialized program and current
stored state. It does not execute initialization or replay the history. -/
def query (p : Program n) (s : State n) (q : Query n) :
    RationalBitWork.Profile (Answer × State n) :=
  let result := p.step s q
  ⟨result, charge n result.work⟩

@[simp] theorem build_result (n : ℕ) :
    (build n).result = UniformMachineWork.build n := rfl

@[simp] theorem query_result (p : Program n) (s : State n) (q : Query n) :
    (query p s q).result = p.step s q := rfl

theorem strategy_value (n : ℕ) :
    (build n).result.value.strategy = UniformAdversary.strategy n :=
  UniformMachineWork.strategy_eq n

theorem query_value (n : ℕ) (s : State n) (q : Query n) :
    UniformMachineWork.answerView (query (build n).result.value s q).result.value =
      Controller.step (UniformAdversary.parameter n) (UniformMachineWork.view s) q := by
  have h := (UniformMachineWork.build n).value.step_value
    (UniformInitializationWork.build_cutoff n) s q
  simpa only [query_result, build_result, UniformInitializationWork.build_parameter] using h

theorem query_reachable (n : ℕ) (s : State n)
    (hs : (build n).result.value.Reachable s) (q : Query n) :
    (build n).result.value.Reachable (query (build n).result.value s q).result.value.2 :=
  (build n).result.value.step_reachable hs q

/-- The recorded peak belongs to the actual capped evaluator and includes
failed stages. Its bit bound also covers every smaller integer it records. -/
theorem initialization_scan_bits (n : ℕ) (a : ℕ)
    (ha : a ≤ (CappedStageScan.select UniformStages.Recipe.budget n).peak) :
    a.size ≤ operandBits n := by
  have hp := UniformStages.selection_peak n
  have hs := Nat.size_le_size (ha.trans hp)
  have hm := RationalWork.size_mul_le
    (n + UniformStages.Recipe.budget.literalMax + 1)
    (n + UniformStages.Recipe.budget.literalMax + 1)
  rw [← pow_two] at hm
  have hc : UniformStages.Recipe.budget.literalMax ≤ 1000 := by decide
  have hz := OperandBounds.size_le_value (n + UniformStages.Recipe.budget.literalMax + 1)
  unfold operandBits
  nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)]

theorem initialization_parameter_bits (n : ℕ) :
    (build n).result.value.parameter.size ≤ operandBits n := by
  have hp := UniformInitializationWork.parameter_le_input_add n
  have hs := OperandBounds.size_le_value (build n).result.value.parameter
  change (UniformInitializationWork.build n).value.parameter.size ≤
    (UniformInitializationWork.build n).value.parameter at hs
  unfold operandBits
  change (UniformInitializationWork.build n).value.parameter.size ≤ _
  nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)]

theorem initialization_power_bits (n e : ℕ) (he : e ≤ UniformStages.selectedStage n + 5) :
    (StateWork.powTwo e).value.size ≤ operandBits n := by
  have hp : 2 ^ e ≤ (build n).result.value.parameter := by
    rw [build_result, UniformInitializationWork.build_parameter]
    exact Nat.pow_le_pow_right (by decide) he
  rw [StateWork.powTwo_value]
  exact (Nat.size_le_size hp).trans (initialization_parameter_bits n)

theorem initialization_cutoff_bits (n : ℕ) :
    (build n).result.value.cutoff.size ≤ operandBits n := by
  have hp := Controller.horizon_le_square n
  rw [build_result, UniformInitializationWork.build_cutoff]
  have hs := (OperandBounds.size_le_value _).trans hp
  unfold operandBits
  nlinarith [Nat.zero_le (n ^ 3)]

theorem input_and_clock_bits (n : ℕ) (a : ℕ) (ha : a ≤ n ^ 2 + n + 1001) :
    a.size ≤ operandBits n := by
  have hs := (OperandBounds.size_le_value a).trans ha
  unfold operandBits
  nlinarith [Nat.zero_le (n ^ 3)]

theorem frozen_operand_bits (n : ℕ) (ranks : Vector (Fin n) n) (x : Fin n) :
    x.val.size ≤ operandBits n ∧ (ranks[x]).val.size ≤ operandBits n := by
  exact ⟨input_and_clock_bits n _ (by have := x.isLt; nlinarith),
    input_and_clock_bits n _ (by have := (ranks[x]).isLt; nlinarith)⟩

/-- Exact normalized implementations of each rational arithmetic family
fit the charge used for a primitive scalar operation. -/
theorem scalar_operation_charge (n : ℕ) (q r : ℚ)
    (hq : Fits (operandBits n) q) (hr : Fits (operandBits n) r) :
    (addProfile q r).bitWork ≤ scalarCharge n ∧
      (mulProfile q r).bitWork ≤ scalarCharge n ∧
      (divProfile q r).bitWork ≤ scalarCharge n ∧
      (RationalBitWork.lessEqual q r).bitWork ≤ scalarCharge n := by
  have hB : 1 ≤ operandBits n := by
    have hp : 1 ≤ (n + 4) ^ 3 := Nat.one_le_pow _ _ (by omega)
    unfold operandBits
    omega
  refine ⟨(addProfile_bits hq hr).trans ?_, (mulProfile_bits hq hr).trans ?_,
    divProfile_bits hq hr hB, comparison_bit_charge hq hr⟩ <;>
    unfold scalarCharge <;> omega

theorem integer_operation_charge (n : ℕ) :
    RationalBitWork.Model.unit (operandBits n) ≤ scalarCharge n := by
  unfold RationalBitWork.Model.unit scalarCharge
  nlinarith [Nat.zero_le ((operandBits n) ^ 2), Nat.zero_le ((operandBits n) ^ 3)]

theorem remaining_scalar_operation_charge (n : ℕ) (q r : ℚ)
    (hq : Fits (operandBits n) q) (hr : Fits (operandBits n) r) :
    (subProfile q r).bitWork ≤ scalarCharge n ∧
      (ceilProfile q).bitWork ≤ scalarCharge n ∧
      (RationalBitWork.lessEqual q r).bitWork +
        2 * RationalBitWork.Model.unit (binaryWidth q r) ≤ scalarCharge n :=
  ⟨subProfile_bits hq hr, ceilProfile_bits hq, minmax_bit_charge hq hr⟩

theorem active_stage_cap (n : ℕ) (hk : 64 ≤ UniformAdversary.parameter n) :
    UniformStages.Recipe.budget.need (UniformStages.selectedStage n) ≤ n :=
  (CappedStageScan.stage_need UniformStages.Recipe.budget n
    (UniformAdversary.active_stage hk)).trans (Parameters.logCap_le_input n)

/-- This is the component premise established throughout a reachable
comparison by `ControllerWorkBounds`. Every operand field is proved from
these concrete state caps and the actual admitted parameter. -/
theorem component_context (n : ℕ) (hk : 64 ≤ UniformAdversary.parameter n)
    (M : StateWork.StoredMemory n)
    (hM : Controller.Admissible (UniformAdversary.parameter n) M.memory)
    (hs : ControllerWork.Sized M.memory (ControllerWork.depthCap n)
      (ControllerWork.gridCap n) (ControllerWork.historyCap n)) :
    RuntimeOperands.ComponentOperands M (UniformStages.selectedStage n) :=
  RuntimeOperands.component_operands M (UniformStages.selectedStage n) (active_stage_cap n hk) hM hs

/-- The actual reachable stored state supplies the full operand certificate:
both endpoint trajectories and their intermediate affine arithmetic, all
finite certificate lists and thresholds, both rounding branches, stored
anchor arithmetic, and every failed calibration test before success. -/
theorem reachable_components (n : ℕ) (M : StateWork.StoredMemory n)
    (hs : (build n).result.value.Reachable (.inl M)) :
    RuntimeOperands.ComponentOperands M (UniformStages.selectedStage n) := by
  obtain ⟨past, hpast⟩ := hs
  change (UniformMachineWork.build n).value.replay past = .inl M at hpast
  have hr : Controller.replay (UniformAdversary.parameter n) past = .active M.memory := by
    have hv := UniformMachineWork.replay_value n past
    rw [hpast] at hv
    exact hv.symm
  have hkpos : 0 < UniformAdversary.parameter n := UniformStages.degree_pos _
  have hrun := Controller.replay_runtimeInvariant (UniformAdversary.parameter n) hkpos past
  rw [hr] at hrun
  have hE := UniformAdversary.enumeration_budget hrun.1
  have hg := Controller.active_grid_bound (UniformAdversary.parameter n) hkpos past M.memory hr hE
  have hd := Controller.active_depth_bound (UniformAdversary.parameter n) hkpos past M.memory hr
  have hh := hrun.2.2.2.trans (Controller.horizon_le_square n)
  have hsize : ControllerWork.Sized M.memory (ControllerWork.depthCap n)
      (ControllerWork.gridCap n) (ControllerWork.historyCap n) := by
    refine ⟨hg.mono ?_, ?_, ?_⟩
    · unfold ControllerWork.gridCap
      nlinarith [Nat.zero_le (n ^ 2)]
    · unfold ControllerWork.depthCap
      nlinarith
    · unfold ControllerWork.historyCap
      omega
  exact component_context n hrun.1 M hrun.2.1.1.admissible hsize

theorem scalarCharge_polynomial (n : ℕ) :
    scalarCharge n ≤ (128 * 10001 ^ 3) * (n + 4) ^ 9 := by
  have hp : 1 ≤ (n + 4) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h : operandBits n + 1 ≤ 10001 * (n + 4) ^ 3 := by
    unfold operandBits
    omega
  have hc := Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left h 3)
  unfold scalarCharge
  convert hc using 1; ring

def initializationCoefficient : ℕ :=
  (7 * UniformStages.Recipe.budget.nodes + 100) * (128 * 10001 ^ 3)

def queryCoefficient : ℕ := 100000000000 * (128 * 10001 ^ 3)

theorem initialization_polynomial (n : ℕ) :
    (build n).bitWork ≤ initializationCoefficient * (n + 4) ^ 11 := by
  have hw := UniformMachineWork.initialization_work n
  have hb := scalarCharge_polynomial n
  have hp := Nat.pow_le_pow_left (show n + 1 ≤ n + 4 by omega) 2
  have hw' := hw.trans (Nat.mul_le_mul_left (7 * UniformStages.Recipe.budget.nodes + 100) hp)
  have hc := Nat.mul_le_mul hw' hb
  change (UniformMachineWork.build n).work * scalarCharge n ≤ _
  convert hc using 1; unfold initializationCoefficient; ring

/-- Every reachable subsequent query has this same bound, including
arbitrarily many calls after permanent freezing. -/
theorem query_polynomial (n : ℕ) (s : State n)
    (hs : (build n).result.value.Reachable s) (q : Query n) :
    (query (build n).result.value s q).bitWork ≤ queryCoefficient * (n + 4) ^ 26 := by
  have hw := UniformMachineWork.per_query_polynomial n s hs q
  have hb := scalarCharge_polynomial n
  have hp := Nat.pow_le_pow_left (show n + 3 ≤ n + 4 by omega) 17
  have hw' := hw.trans (Nat.mul_le_mul_left 100000000000 hp)
  have hc := Nat.mul_le_mul hw' hb
  change ((UniformMachineWork.build n).value.step s q).work * scalarCharge n ≤ _
  convert hc using 1; unfold queryCoefficient; ring

theorem frozen_word_work (p : Program n) (ranks : Vector (Fin n) n) (q : Query n) :
    (query p (.inr ranks) q).result.work = 10 := rfl

theorem frozen_charge (p : Program n) (ranks : Vector (Fin n) n) (q : Query n) :
    (query p (.inr ranks) q).bitWork = 10 * scalarCharge n := rfl

theorem frozen_state (p : Program n) (ranks : Vector (Fin n) n) (q : Query n) :
    (query p (.inr ranks) q).result.value.2 = .inr ranks := rfl

/-- The same concrete built program realizes the paper's asymptotically
optimal family and has a fixed polynomial binary charge for initialization
and every subsequent online query. No component budget or cost oracle is
assumed in this theorem. -/
theorem asymptoticallyOptimal_and_polynomial :
    SortingAdversary.Optimal.AsymptoticallyOptimal
      (fun n => (build n).result.value.strategy) ∧
      (∀ n, (build n).result.value.strategy = UniformAdversary.strategy n) ∧
      (∀ n, ∀ M : StateWork.StoredMemory n, (build n).result.value.Reachable (.inl M) →
        RuntimeOperands.ComponentOperands M (UniformStages.selectedStage n)) ∧
      (∀ n, (build n).bitWork ≤ initializationCoefficient * (n + 4) ^ 11) ∧
      ∀ n, ∀ s : State n, (build n).result.value.Reachable s → ∀ q : Query n,
        (query (build n).result.value s q).bitWork ≤ queryCoefficient * (n + 4) ^ 26 :=
  ⟨UniformMachineWork.asymptoticallyOptimal, strategy_value, reachable_components,
    initialization_polynomial, query_polynomial⟩

end SortingAdversary.Continuous.UniformEfficient
