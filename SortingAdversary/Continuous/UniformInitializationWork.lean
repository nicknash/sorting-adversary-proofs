import SortingAdversary.Continuous.UniformAdversary
import SortingAdversary.Continuous.StateWork
import SortingAdversary.Continuous.RoundingWork

/-!
# Counted initialization of the uniform continuous machine

The logarithmic cap is computed by successive divisions before the actual
capped stage scan runs. The selected degree is then materialized by counted
doublings. The cutoff uses a counted ceiling logarithm, and initialization
constructs either the complete stored memory or the frozen identity vector.
The displayed bound therefore includes parameter selection and construction,
including rejected stages; none of those calculations is treated as free.
-/

namespace SortingAdversary.Continuous.UniformInitializationWork

open SortingAdversary.Optimal
open UniformStages StateWork

def select (n : ℕ) : PrimitiveWork.Result ℕ :=
  let cap := StateWork.logTwo (n + 1)
  let chosen := CappedStageScan.scan Recipe.budget cap.value 0 cap.value
  ⟨chosen.stage, cap.work + chosen.work + 2⟩

@[simp] theorem select_value (n : ℕ) : (select n).value = selectedStage n := by
  simp only [select, StateWork.logTwo_value, selectedStage, CappedStageScan.stage,
    CappedStageScan.select, Parameters.logCap]

theorem select_work (n : ℕ) :
    (select n).work ≤
      n * (Recipe.budget.nodes * (5 * (n + 1) + 2) + 1) + 3 * n + 3 := by
  have hscan := selection_work n
  have hcap := Parameters.logCap_le_input n
  simp only [select, StateWork.logTwo_work, StateWork.logTwo_value]
  change (CappedStageScan.scan Recipe.budget (Nat.log 2 (n + 1)) 0 (Nat.log 2 (n + 1))).work ≤ _
    at hscan
  change Nat.log 2 (n + 1) ≤ n at hcap
  omega

def cutoff (n : ℕ) : PrimitiveWork.Result ℕ :=
  let ceiling := RoundingWork.clogTwo n
  ⟨n * ceiling.value, ceiling.work + 2⟩

@[simp] theorem cutoff_value (n : ℕ) : (cutoff n).value = Controller.horizon n := by
  simp only [cutoff, RoundingWork.clogTwo_value, Controller.horizon]

theorem cutoff_work (n : ℕ) : (cutoff n).work ≤ 4 * n + 3 := by
  have hlog : Nat.clog 2 n ≤ n := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  simp only [cutoff, RoundingWork.clogTwo_work]
  omega

abbrev InitialState (n : ℕ) := Sum (StoredMemory n) (Vector (Fin n) n)

def initial (n k : ℕ) : PrimitiveWork.Result (InitialState n) :=
  if 64 ≤ k then
    let memory := StateWork.initial n
    ⟨.inl memory.value, memory.work + 2⟩
  else
    let ranks := PrimitiveWork.vector (fun x : Fin n => (⟨x, 1⟩ : PrimitiveWork.Result (Fin n)))
    ⟨.inr ranks.value, ranks.work + 2⟩

def initialView {n : ℕ} : InitialState n → Controller.MachineState n
  | .inl memory => .active memory.memory
  | .inr ranks => .frozen (fun x => ranks[x])

@[simp] theorem initial_value (n k : ℕ) :
    initialView (initial n k).value = Controller.start n k := by
  by_cases hk : 64 ≤ k
  · simp only [initial, if_pos hk, initialView, StateWork.initial_value, Controller.start]
  · simp only [initial, if_neg hk, initialView, PrimitiveWork.vector_value,
      Fin.getElem_fin, Vector.getElem_ofFn, Controller.start]
    rfl

theorem initial_work (n k : ℕ) : (initial n k).work ≤ 12 * (n + 1) ^ 2 + 2 := by
  by_cases hk : 64 ≤ k
  · simpa only [initial, if_pos hk] using Nat.add_le_add_right (StateWork.initial_work n) 2
  · have hv := PrimitiveWork.vector_work_le
      (fun x : Fin n => (⟨x, 1⟩ : PrimitiveWork.Result (Fin n))) 1 (fun _ => le_rfl)
    simp only [initial, if_neg hk]
    nlinarith

structure Setup (n : ℕ) where
  parameter : ℕ
  positive : 0 < parameter
  cutoff : ℕ
  initial : InitialState n

def build (n : ℕ) : PrimitiveWork.Result (Setup n) :=
  let chosen := select n
  let degree := StateWork.powTwo (chosen.value + 5)
  have positive : 0 < degree.value := by
    simp only [degree, StateWork.powTwo_value]
    positivity
  let clock := cutoff n
  let memory := initial n degree.value
  ⟨⟨degree.value, positive, clock.value, memory.value⟩,
    chosen.work + degree.work + clock.work + memory.work + 4⟩

@[simp] theorem build_parameter (n : ℕ) :
    (build n).value.parameter = UniformAdversary.parameter n := by
  simp only [build, StateWork.powTwo_value, select_value, UniformAdversary.parameter, degree]

@[simp] theorem build_cutoff (n : ℕ) : (build n).value.cutoff = Controller.horizon n := by
  simp only [build, cutoff_value]

@[simp] theorem build_initial (n : ℕ) :
    initialView (build n).value.initial = Controller.start n (build n).value.parameter := by
  simp only [build, initial_value]

/-- The fixed expression size appears only in the coefficient, never in
the polynomial degree or in a premise about the selected stage. -/
def initializationBound (n : ℕ) : ℕ := (7 * Recipe.budget.nodes + 100) * (n + 1) ^ 2

theorem build_work (n : ℕ) : (build n).work ≤ initializationBound n := by
  have hs := select_work n
  have hj : (select n).value ≤ n := by
    rw [select_value]
    exact (CappedStageScan.stage_le Recipe.budget n).trans (Parameters.logCap_le_input n)
  have hp := StateWork.powTwo_work ((select n).value + 5)
  have hc := cutoff_work n
  have hi := initial_work n (StateWork.powTwo ((select n).value + 5)).value
  have hscan : n * (Recipe.budget.nodes * (5 * (n + 1) + 2) + 1) ≤
      7 * Recipe.budget.nodes * (n + 1) ^ 2 + n := by
    calc
      _ = Recipe.budget.nodes * (n * (5 * (n + 1) + 2)) + n := by ring
      _ ≤ Recipe.budget.nodes * (7 * (n + 1) ^ 2) + n :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ (by nlinarith)) n
      _ = _ := by ring
  simp only [build]
  unfold initializationBound
  nlinarith

theorem parameter_le_input_add (n : ℕ) : (build n).value.parameter ≤ n + 32 := by
  rw [build_parameter]
  by_cases hj : selectedStage n = 0
  · norm_num [UniformAdversary.parameter, hj, degree]
  · have hcap := CappedStageScan.stage_need Recipe.budget n (Nat.pos_of_ne_zero hj)
    have hk := (admitted_scalar_bounds (selectedStage n) n
      (hcap.trans (Parameters.logCap_le_input n))).1
    exact hk.trans (Nat.le_add_right _ _)

end SortingAdversary.Continuous.UniformInitializationWork
