import SortingAdversary.Continuous.SelectionWork
import SortingAdversary.Continuous.GraphScanWork
import SortingAdversary.Continuous.ControllerWorkBounds

/-!
# Concrete stored-data controller routines

Every component of the measured controller is instantiated here by an
executed stored-data routine. Routing uses the coded paths; selection
includes calibration, neighborhood preparation, word enumeration and
certification; mutations include materialized closure and normalization.
The common word bound follows from these component counters on the proved
reachable-state caps, rather than being assigned to an opaque controller.
-/

namespace SortingAdversary.Continuous.ConcreteRoutines

open SortingAdversary.Optimal
open StateWork ControllerWork UniformStages Precision

variable {n : ℕ}

def attempt (M : StoredMemory n) (k : ℕ) (hk : 0 < k) (q : Query n) :
    PrimitiveWork.Result (LocalSelection.Result n) :=
  let routed := StateWork.route M q
  match routed.value with
  | .coordinates =>
    let selected := SelectionWork.select M.data k hk q.left q.right
    ⟨selected.value, routed.work + selected.work + 1⟩
  | .leftFree c =>
    let selected := SelectionWork.selectThreshold M.data k hk q.left c
    ⟨selected.value, routed.work + selected.work + 1⟩
  | .rightFree c =>
    let selected := SelectionWork.selectThreshold M.data k hk q.right c
    ⟨Controller.reverseResult selected.value, routed.work + selected.work + 2⟩
  | .anchors c d =>
    ⟨.answer (if c < d then .less else .greater), routed.work + 2⟩

@[simp] theorem attempt_value (M : StoredMemory n) (k : ℕ) (hk : 0 < k) (q : Query n) :
    (attempt M k hk q).value = Controller.attempt M.memory k q := by
  simp only [attempt, StateWork.route_value, Controller.attempt]
  cases TreeState.route (M.memory.tree.location q.left) (M.memory.tree.location q.right) <;>
    simp only [SelectionWork.select_value, SelectionWork.selectThreshold_value]
  all_goals rfl

def firstPath (M : StoredMemory n) (k : ℕ) :
    PrimitiveWork.Result (Option (List (Fin n))) :=
  let height := StateWork.powTwo k
  let result := GraphScanWork.firstPath M.data height.value
  ⟨result.value, height.work + result.work + 1⟩

@[simp] theorem firstPath_value (M : StoredMemory n) (k : ℕ) :
    (firstPath M k).value = GraphPaths.firstPath M.memory.tree.system.edge (2 ^ k) := by
  simp only [firstPath, StateWork.powTwo_value, GraphScanWork.firstPath_value]
  rfl

def routines (n k : ℕ) (hk : 0 < k) : ControllerWork.Routines n k where
  State := StoredMemory n
  memory := StoredMemory.memory
  attempt M q := attempt M k hk q
  anchor M x := SelectionWork.chooseAnchor M.data k hk x
  refine := StateWork.refine
  record := StateWork.record
  firstPath M := firstPath M k
  degreeChoice M := GraphScanWork.degreeChoice M.data k
  attempt_value := fun M q => attempt_value M k hk q
  anchor_value := fun M x => SelectionWork.chooseAnchor_value M.data k hk x
  refine_value := StateWork.refine_value
  record_value := StateWork.record_value
  firstPath_value := fun M => firstPath_value M k
  degreeChoice_value := fun M => GraphScanWork.degreeChoice_value M.data k

theorem attempt_work (M : StoredMemory n) (j F : ℕ) (hk : 0 < degree j)
    (hcap : Recipe.budget.need j ≤ n) (hM : Controller.Admissible (degree j) M.memory)
    (hg : M.memory.OnGrid F) (q : Query n) :
    (attempt M (degree j) hk q).work ≤
      (2 * Controller.totalDepth M.memory + 1) * (4 * F + 20) +
        (StageWork.calibrate (degree j) hk).work + SelectionWork.localBound n F + 5 := by
  have hr := StateWork.route_work M q F hg
  have htwo := SelectionWork.select_work M.data j F hk hcap q.left q.right hg.1
    hM.toGeometric.rationalBounds hM.toGeometric.widths hM.degree
  have hone (x : Fin n) (c : ℚ) := SelectionWork.selectThreshold_work M.data j F hk hcap x c hg.1
    (hM.toGeometric.rationalBounds x) (hM.toGeometric.widths x) hM.degree
  unfold attempt
  dsimp only
  cases (StateWork.route M q).value with
  | coordinates => dsimp only; omega
  | leftFree c => dsimp only; have := hone q.left c; omega
  | rightFree c => dsimp only; have := hone q.right c; omega
  | anchors c d => dsimp only; omega

/-- A deliberately generous fixed polynomial, shared by every actual local
call under the controller's depth and dyadic-grid caps. -/
def wordBound (n : ℕ) : ℕ := 1000000000 * (n + 3) ^ 16

private theorem power_le_budget_power (n e : ℕ) (he : e ≤ 16) :
    (n + 3) ^ e ≤ (n + 3) ^ 16 := Nat.pow_le_pow_right (by omega) he

private theorem one_le_budget_power (n : ℕ) : 1 ≤ (n + 3) ^ 16 :=
  Nat.one_le_pow _ _ (by omega)

private theorem orderBound_le (n : ℕ) : orderBound n ≤ 60 * (n + 3) ^ 3 := by
  unfold orderBound GraphWork.closureRanksBound ClosureWork.workBound
  nlinarith

private theorem localBound_le (n : ℕ) :
    SelectionWork.localBound n (gridCap n) ≤ 62500000 * (n + 3) ^ 16 := by
  have harg : n + gridCap n + 1 ≤ 5 * (n + 3) ^ 3 := by
    have hn : n + 3 ≤ (n + 3) ^ 3 := by
      simpa only [pow_one] using Nat.pow_le_pow_right
        (show 0 < n + 3 by omega) (show 1 ≤ 3 by decide)
    unfold gridCap
    omega
  have hp := Nat.pow_le_pow_left harg 5
  have he : (5 * (n + 3) ^ 3) ^ 5 = 3125 * (n + 3) ^ 15 := by ring
  rw [he] at hp
  have hpow := power_le_budget_power n 15 (by decide)
  unfold SelectionWork.localBound
  nlinarith

private theorem routingBound_le (n depth : ℕ) (hd : depth ≤ depthCap n) :
    (2 * depth + 1) * (4 * gridCap n + 20) ≤ 108 * (n + 3) ^ 16 := by
  have h1 : 1 ≤ (n + 3) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (n + 3) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hl : 2 * depth + 1 ≤ 3 * (n + 3) ^ 2 := by
    unfold depthCap at hd
    omega
  have hr : 4 * gridCap n + 20 ≤ 36 * (n + 3) ^ 3 := by
    unfold gridCap
    omega
  have hm := Nat.mul_le_mul hl hr
  have he : (3 * (n + 3) ^ 2) * (36 * (n + 3) ^ 3) = 108 * (n + 3) ^ 5 := by ring
  rw [he] at hm
  have hp := power_le_budget_power n 5 (by decide)
  omega

private theorem stateBounds_le (n depth : ℕ) (hd : depth ≤ depthCap n) :
    refineBound n depth (gridCap n) ≤ wordBound n ∧
    recordBound n depth (gridCap n) ≤ wordBound n := by
  have ho := (orderBound_le n).trans (Nat.mul_le_mul_left 60 (power_le_budget_power n 3 (by decide)))
  have h2 := (Nat.pow_le_pow_left (show n + 1 ≤ n + 3 by omega) 2).trans
    (power_le_budget_power n 2 (by decide))
  have h3 := power_le_budget_power n 3 (by decide)
  have hdepth := hd.trans (power_le_budget_power n 2 (by decide))
  have hr := routingBound_le n depth hd
  unfold gridCap at hr
  have hp := one_le_budget_power n
  unfold refineBound recordBound wordBound gridCap
  constructor <;> omega

/-- The concrete routines satisfy every component premise of the measured
controller at an admitted stage. The only hypotheses select the fixed stage;
there is no assumed local running-time or certificate oracle. -/
theorem callBounds_admitted (n j : ℕ) (hcap : Recipe.budget.need j ≤ n) :
    ControllerWork.CallBounds (routines n (degree j) (degree_pos j))
      (depthCap n) (gridCap n) (historyCap n) (wordBound n) := by
  have hcal := StageWork.calibrate_work_admitted j n hcap
  have hscalar := admitted_scalar_bounds j n hcap
  have h2 := (Nat.pow_le_pow_left (show n + 1 ≤ n + 3 by omega) 2).trans
    (power_le_budget_power n 2 (by decide))
  have h4 := (Nat.pow_le_pow_left (show n + 1 ≤ n + 3 by omega) 4).trans
    (power_le_budget_power n 4 (by decide))
  have hn : n ≤ (n + 3) ^ 16 := by
    have hh := power_le_budget_power n 1 (by decide)
    simp only [pow_one] at hh
    omega
  have hp := one_le_budget_power n
  have hlocal := localBound_le n
  constructor
  · intro M hM hs q
    change (attempt M (degree j) (degree_pos j) q).work ≤ _
    have ha := attempt_work M j (gridCap n) (degree_pos j) hcap hM hs.grid q
    have hr := routingBound_le n (Controller.totalDepth M.memory) hs.depth
    unfold wordBound
    omega
  · intro M hM hs x
    change (SelectionWork.chooseAnchor M.data (degree j) (degree_pos j) x).work ≤ _
    have he := ArbitraryLabels.weak_endpoints M.data.system hM.normalized hM.toGeometric.widths
    have ha := SelectionWork.chooseAnchor_work M.data j (gridCap n) (degree_pos j) hcap x hs.grid.1
      (hM.toGeometric.rationalBounds x) hM.toGeometric.widths he.1 he.2 hM.degree
    unfold wordBound
    omega
  · intro M hM hs x c hc _ _
    exact (StateWork.refine_work M x c (gridCap n) hc).trans
      (stateBounds_le n _ hs.depth).1
  · intro M hM hs q a
    exact (StateWork.record_work M q a (gridCap n) hs.grid).trans
      (stateBounds_le n _ hs.depth).2
  · intro M hM hs
    change (firstPath M (degree j)).work ≤ _
    have hh := GraphScanWork.firstPath_work_admitted_input M.data j n hcap le_rfl
      hM.toGeometric.noLoop hM.degree
    simp only [firstPath, StateWork.powTwo_value, StateWork.powTwo_work]
    unfold wordBound
    omega
  · intro M hM hs
    change (GraphScanWork.degreeChoice M.data (degree j)).work ≤ _
    have hd := GraphScanWork.degreeChoice_work M.data (degree j)
    unfold wordBound
    omega

end SortingAdversary.Continuous.ConcreteRoutines
