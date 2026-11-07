import SortingAdversary.Optimal.RepresentationCells
import SortingAdversary.Optimal.SelectorWork
import SortingAdversary.Optimal.ScaleWalksWork

/-!
# Measured decisions on the real repair state

These adapters use the concrete stored-field getters. The returned early
moves and scale triggers are exactly those of the existing controller,
including all original label-order tie breaks. Proof fields are erased;
every executable choice is made by a counted scan.
-/

namespace SortingAdversary.Optimal.RepairSelectWork

open PrimitiveWork WidthRepair RepresentationWork

variable {n : ℕ} {s : State n}

def width (a : LocalAccess s) (v : Fin n) : Result ℕ :=
  WindowWork.width a.windows v

@[simp] theorem width_value (a : LocalAccess s) (v : Fin n) :
    (width a v).value = s.width v := by
  simp only [width, WindowWork.width_value, LocalAccess.windows_system, State.width]

def widthBound (n A : ℕ) : ℕ := 2 * WindowWork.endpointWorkBound n A A + 2

theorem width_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A) (v : Fin n) :
    (width a v).work ≤ widthBound n A :=
  WindowWork.width_work_le a.windows v A A h.publicRow h.lower h.upper

def free (a : LocalAccess s) (v : Fin n) : Result Bool :=
  let pin := a.pin v
  ⟨pin.value.isNone, pin.work + 1⟩

@[simp] theorem free_value (a : LocalAccess s) (v : Fin n) :
    (free a v).value = decide (v ∈ s.pool.free) := by
  apply Bool.eq_iff_iff.mpr
  simp [free, a.pin_value, s.pool.free_iff]

theorem free_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A) (v : Fin n) :
    (free a v).work ≤ A + 1 := Nat.add_le_add_right (h.pin v) 1

theorem active_values (a : LocalAccess s) : SelectorWork.values a.active = s.rows.active := by
  funext x y
  exact a.active_value x y

theorem active_relation (a : LocalAccess s) : ScaleWalksWork.relation a.active = s.rows.active := by
  funext x y
  exact a.active_value x y

def narrow (a : LocalAccess s) (W₀ : ℕ) : Result (Option (Fin n)) :=
  SelectorWork.narrow a.active (width a) W₀

@[simp] theorem narrow_value (a : LocalAccess s) (W₀ : ℕ) :
    (narrow a W₀).value = narrowWitness s W₀ :=
  SelectorWork.narrow_value s a.active (width a) W₀ (active_values a) (width_value a)

def steep (a : LocalAccess s) (L : ℕ) : Result (Option (Fin n × Fin n)) :=
  SelectorWork.steep a.active (width a) L

@[simp] theorem steep_value (a : LocalAccess s) (L : ℕ) :
    (steep a L).value = steepWitness s L :=
  SelectorWork.steep_value s a.active (width a) L (active_values a) (width_value a)

def degree (a : LocalAccess s) (D : ℕ) : Result (Option (Fin n)) :=
  SelectorWork.largeDegree a.active (free a) D

@[simp] theorem degree_value (a : LocalAccess s) (D : ℕ) :
    (degree a D).value = SparseRepairGraph.degreeWitness s.rows.active s.pool.free D := by
  rw [degree, SelectorWork.largeDegree_value _ _ _ _ (free_value a), active_values]

theorem narrow_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A) (W₀ : ℕ) :
    (narrow a W₀).work ≤ SelectorWork.narrowWorkBound n A (widthBound n A) :=
  SelectorWork.narrow_work_le a.active (width a) W₀ A (widthBound n A) h.active (width_work_le a h)

theorem steep_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A) (L : ℕ) :
    (steep a L).work ≤ SelectorWork.steepWorkBound n A (widthBound n A) :=
  SelectorWork.steep_work_le a.active (width a) L A (widthBound n A) h.active (width_work_le a h)

theorem degree_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A) (D : ℕ) :
    (degree a D).work ≤ SelectorWork.degreeWorkBound n A (A + 1) :=
  SelectorWork.largeDegree_work_le a.active (free a) D A (A + 1) h.active (free_work_le a h)

def early (a : LocalAccess s) (W₀ L : ℕ) : Result (Option (EarlyMove s W₀ L)) :=
  let chosenNarrow := narrow a W₀
  match hn : chosenNarrow.value with
  | some v =>
      have hv : narrowWitness s W₀ = some v := (narrow_value a W₀).symm.trans hn
      ⟨some (.cheap v (narrowWitness_some s W₀ hv).1 (narrowWitness_some s W₀ hv).2),
        chosenNarrow.work + 1⟩
  | none =>
      let chosenSteep := steep a L
      match he : chosenSteep.value with
      | none => ⟨none, chosenNarrow.work + chosenSteep.work + 2⟩
      | some uv =>
          have huv : steepWitness s L = some uv := (steep_value a L).symm.trans he
          let left := width a uv.1
          let right := width a uv.2
          if hs : L * right.value < left.value then
            have hlt : L * s.width uv.2 < s.width uv.1 := by
              simpa only [left, right, width_value] using hs
            ⟨some (.lower uv.1 uv.2 (steepWitness_some s L huv).1 hlt),
              chosenNarrow.work + chosenSteep.work + left.work + right.work + 4⟩
          else
            have hnot : ¬ L * s.width uv.2 < s.width uv.1 := by
              simpa only [left, right, width_value] using hs
            ⟨some (.upper uv.1 uv.2 (steepWitness_some s L huv).1
              ((steepWitness_some s L huv).2.resolve_left hnot)),
              chosenNarrow.work + chosenSteep.work + left.work + right.work + 4⟩

@[simp] theorem early_value (a : LocalAccess s) (W₀ L : ℕ) :
    (early a W₀ L).value = selectEarly s W₀ L := by
  simp only [early, selectEarly]
  repeat' split
  all_goals
    have hn := narrow_value a W₀
    have he := steep_value a L
    have hw := width_value a
    aesop <;> omega

def earlyBound (n A : ℕ) : ℕ :=
  SelectorWork.narrowWorkBound n A (widthBound n A) +
  SelectorWork.steepWorkBound n A (widthBound n A) + 2 * widthBound n A + 4

theorem early_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A) (W₀ L : ℕ) :
    (early a W₀ L).work ≤ earlyBound n A := by
  have hn := narrow_work_le a h W₀
  have he := steep_work_le a h L
  simp only [early]
  split
  · dsimp only
    unfold earlyBound
    omega
  · split
    · dsimp only
      unfold earlyBound
      omega
    · rename_i uv huv
      have hl := width_work_le a h uv.1
      have hr := width_work_le a h uv.2
      split <;> dsimp only <;> unfold earlyBound <;> omega

/-- The breadth matrix is computed once before the complete pair scan.
Widths at the two endpoints are computed once per tested pair. -/
def scaleWitness (a : LocalAccess s) (R : ℕ) : Result (Option (Fin n × Fin n)) :=
  let reachable := ScaleWalksWork.reach a.active n
  let answer := FiniteLoopWork.scanPairs (fun xy =>
    let low := width a xy.1
    let high := width a xy.2
    ⟨reachable.value[xy.1][xy.2] && decide (R * low.value < high.value), low.work + high.work + 5⟩)
  ⟨answer.value, reachable.work + answer.work⟩

@[simp] theorem scaleWitness_value (a : LocalAccess s) (R : ℕ) :
    (scaleWitness a R).value = WidthRepair.scaleWitness s R := by
  simp only [scaleWitness, FiniteLoopWork.scanPairs_value, width_value,
    ScaleWalksWork.reachTable_value, active_relation, WidthRepair.scaleWitness, Bool.decide_and]

def scaleBound (n A : ℕ) : ℕ :=
  ScaleWalksWork.reachBound n n A +
    (3 * n + n * (5 * n + 3) + n * n * (2 * widthBound n A + 7) + 3)

theorem scaleWitness_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A) (R : ℕ) :
    (scaleWitness a R).work ≤ scaleBound n A := by
  have hr := ScaleWalksWork.reach_work a.active n A h.active
  have hs := FiniteLoopWork.scanPairs_work_le
    (fun xy : Fin n × Fin n =>
      (⟨(ScaleWalksWork.reach a.active n).value[xy.1][xy.2] &&
        decide (R * (width a xy.1).value < (width a xy.2).value),
        (width a xy.1).work + (width a xy.2).work + 5⟩ : Result Bool))
    (2 * widthBound n A + 5) (by
      intro xy
      have hl := width_work_le a h xy.1
      have hu := width_work_le a h xy.2
      dsimp only
      omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hs
  change (ScaleWalksWork.reach a.active n).work + _ ≤ _
  unfold scaleBound
  simpa only [Nat.add_assoc] using Nat.add_le_add hr hs

def scale (a : LocalAccess s) (p : ScaleParameters) : Result (Option (ScaleTrigger s p)) :=
  let chosen := scaleWitness a p.R
  match he : chosen.value with
  | none => ⟨none, chosen.work + 1⟩
  | some xy =>
      have hxy : WidthRepair.scaleWitness s p.R = some xy :=
        (scaleWitness_value a p.R).symm.trans he
      ⟨some ⟨xy.1, xy.2, (scaleWitness_some s p.R hxy).1, (scaleWitness_some s p.R hxy).2⟩,
        chosen.work + 1⟩

@[simp] theorem scale_value (a : LocalAccess s) (p : ScaleParameters) :
    (scale a p).value = selectScale s p := by
  simp only [scale, selectScale]
  split <;> split
  all_goals
    have he := scaleWitness_value a p.R
    aesop <;> omega

theorem scale_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A) (p : ScaleParameters) :
    (scale a p).work ≤ scaleBound n A + 1 := by
  have hh := scaleWitness_work_le a h p.R
  simp only [scale]
  split <;> dsimp only <;> omega

end SortingAdversary.Optimal.RepairSelectWork

