import SortingAdversary.Optimal.ScaleWalkAccess
import SortingAdversary.Optimal.ScaleCrossingWork
import SortingAdversary.Optimal.RepairSelectWork
import SortingAdversary.Optimal.WidthScalarWork

/-!
# Measured construction of a scale reservation's labels

The length and vertex getter below are runtime data obtained from the counted
shortest-path reconstruction. In particular, the semantic walk is not called
to recover its length. Each scale threshold has a counted power computation
and finite first-crossing scan. The selected labels are then stored in a
vector for constant-work access during chronological group execution.
-/

namespace SortingAdversary.Optimal.ScaleVerticesWork

open PrimitiveWork RepresentationWork WidthRepair ScaleWalksWork GraphBalls ScaleGeometry

variable {n : ℕ} {s : State n}

structure PathData (n : ℕ) where
  length : ℕ
  get : Fin (length + 1) → Result (Fin n)

def PathData.values (data : PathData n) : Σ r : ℕ, Fin (r + 1) → Fin n :=
  ⟨data.length, fun i => (data.get i).value⟩

def path (E : Rows n) (x y : Fin n) (hc : Connected (relation E) x y) : Result (PathData n) :=
  let radius := distance E x y hc
  have reaches : y ∈ ball (relation E) x radius.value.val := by
    rw [distance_value]
    exact ScaleWalks.distance_reaches (relation E) x y hc
  let getter := ScaleWalkAccess.build E x y radius.value.val reaches
  ⟨⟨radius.value.val, getter.value⟩, radius.work + getter.work + 2⟩

theorem build_values_congr (E : SparseClosure.Rows (Fin n)) (x y : Fin n)
    {r q : ℕ} (equal : r = q) (hr : y ∈ ball E x r) (hq : y ∈ ball E x q) :
    (⟨r, (ScaleWalks.buildWalk E x y r hr).val.vertex⟩ : Σ r : ℕ, Fin (r + 1) → Fin n) =
      ⟨q, (ScaleWalks.buildWalk E x y q hq).val.vertex⟩ := by
  subst q
  rfl

theorem shortest_values_congr {E F : SparseClosure.Rows (Fin n)} (equal : E = F)
    (x y : Fin n) (hc : Connected E x y) (hf : Connected F x y) :
    (⟨(ScaleWalks.shortestPath E x y hc).length, (ScaleWalks.shortestPath E x y hc).walk.vertex⟩ :
      Σ r : ℕ, Fin (r + 1) → Fin n) =
      ⟨(ScaleWalks.shortestPath F x y hf).length, (ScaleWalks.shortestPath F x y hf).walk.vertex⟩ := by
  subst F
  rfl

theorem path_values (E : Rows n) (x y : Fin n) (hc : Connected (relation E) x y) :
    (path E x y hc).value.values =
      ⟨(ScaleWalks.shortestPath (relation E) x y hc).length,
        (ScaleWalks.shortestPath (relation E) x y hc).walk.vertex⟩ := by
  let radius := distance E x y hc
  have reaches : y ∈ ball (relation E) x radius.value.val := by
    rw [distance_value]
    exact ScaleWalks.distance_reaches (relation E) x y hc
  have hv : (fun i => ((ScaleWalkAccess.build E x y radius.value.val reaches).value i).value) =
      (ScaleWalks.buildWalk (relation E) x y radius.value.val reaches).val.vertex :=
    funext (ScaleWalkAccess.build_value E x y radius.value.val reaches)
  have hm : (path E x y hc).value.values =
      ⟨radius.value.val, (ScaleWalks.buildWalk (relation E) x y radius.value.val reaches).val.vertex⟩ :=
    congrArg (fun get => (⟨radius.value.val, get⟩ : Σ r : ℕ, Fin (r + 1) → Fin n)) hv
  exact hm.trans (build_values_congr (relation E) x y
    (congrArg Fin.val (distance_value E x y hc)) reaches (ScaleWalks.distance_reaches (relation E) x y hc))

theorem path_length_le (E : Rows n) (x y : Fin n) (hc : Connected (relation E) x y) :
    (path E x y hc).value.length ≤ n :=
  Nat.le_of_lt_succ (distance E x y hc).value.isLt

theorem path_get_work (E : Rows n) (x y : Fin n) (hc : Connected (relation E) x y)
    (i : Fin ((path E x y hc).value.length + 1)) :
    ((path E x y hc).value.get i).work ≤ 2 * n + 1 := by
  have h := ScaleWalkAccess.get_work_le E x y (distance E x y hc).value.val
    (by rw [distance_value]; exact ScaleWalks.distance_reaches (relation E) x y hc) i
  have hl := path_length_le E x y hc
  change _ ≤ 2 * n + 1
  change (distance E x y hc).value.val ≤ n at hl
  exact h.trans (by omega)

def pathBound (n A : ℕ) : ℕ := distanceBound n A + walkBound n n A + 2

theorem path_work_le (E : Rows n) {A : ℕ} (cost : ∀ x y, (E x y).work ≤ A)
    (x y : Fin n) (hc : Connected (relation E) x y) :
    (path E x y hc).work ≤ pathBound n A := by
  have hd := distance_work E A cost x y hc
  have hp := ScaleWalkAccess.build_work E A cost x y (distance E x y hc).value.val
    (by rw [distance_value]; exact ScaleWalks.distance_reaches (relation E) x y hc)
  have hm := walkBound_mono n A (Nat.le_of_lt_succ (distance E x y hc).value.isLt)
  change _ + _ + 2 ≤ _
  unfold pathBound
  omega

/-- Extensional correctness can mention the original walk, but runtime
selection takes only the measured length and vertex getter. -/
theorem crossing_of_values {E : SparseClosure.Rows (Fin n)} {r : ℕ} (walk : Walk E r)
    (data : PathData n) (same : data.values = ⟨r, walk.vertex⟩) (W : Fin n → ℕ)
    (width : Fin n → Result ℕ) (hw : ∀ v, (width v).value = W v)
    (threshold : ℕ) (hend : threshold ≤ W walk.finish) :
    (ScaleCrossingWork.crossing data.get width threshold).value =
      walk.vertex (walk.firstIndex W threshold hend) := by
  rcases data with ⟨length, getter⟩
  dsimp only [PathData.values] at same
  have hl : length = r := congrArg Sigma.fst same
  subst length
  have hv : (fun i => (getter i).value) = walk.vertex := by
    exact eq_of_heq (Sigma.mk.inj same).2
  apply ScaleCrossingWork.crossing_value walk W getter width (congrFun hv) hw threshold hend

def selected (data : PathData n) (width : Fin n → Result ℕ) (base lowWidth : ℕ) (i : ℕ) : Result (Fin n) :=
  let raised := WidthScalarWork.power base i
  let chosen := ScaleCrossingWork.crossing data.get width (raised.value * lowWidth)
  ⟨chosen.value, raised.work + chosen.work + 1⟩

def selectedBound (n J widthWork : ℕ) : ℕ :=
  2 * J + 1 + ScaleCrossingWork.firstBound n (2 * n + 1) widthWork + (2 * n + 1) + 2

theorem selected_work_le (data : PathData n) (width : Fin n → Result ℕ)
    (base lowWidth i J W : ℕ) (hi : i ≤ J) (hl : data.length ≤ n)
    (hv : ∀ j, (data.get j).work ≤ 2 * n + 1) (hw : ∀ v, (width v).work ≤ W) :
    (selected data width base lowWidth i).work ≤ selectedBound n J W := by
  have hc := ScaleCrossingWork.crossing_work_le data.get width
    ((WidthScalarWork.power base i).value * lowWidth) (2 * n + 1) W hv hw
  have hm := ScaleCrossingWork.firstBound_mono (widthWork := W) hl (le_refl (2 * n + 1))
  simp only [selected, WidthScalarWork.power_work]
  unfold selectedBound
  omega

def vertices (a : LocalAccess s) (p : ScaleParameters) (trigger : ScaleTrigger s p) :
    Result (Vector (Fin n) p.J) :=
  have connected : Connected (relation a.active) trigger.low trigger.high := by
    rw [RepairSelectWork.active_relation]
    exact trigger.connected
  let walk := path a.active trigger.low trigger.high connected
  let base := WidthScalarWork.base p
  let low := RepairSelectWork.width a trigger.low
  let answer := vector (fun i : Fin p.J => selected walk.value (RepairSelectWork.width a) base.value low.value i.val)
  ⟨answer.value, walk.work + base.work + low.work + answer.work + 3⟩

theorem vertices_value (a : LocalAccess s) (p : ScaleParameters) (trigger : ScaleTrigger s p) :
    (vertices a p trigger).value = Vector.ofFn trigger.vertices := by
  apply Vector.ext
  intro i hi
  simp only [vertices, vector_value, Vector.getElem_ofFn]
  let connected : Connected (relation a.active) trigger.low trigger.high := by
    rw [RepairSelectWork.active_relation]
    exact trigger.connected
  have hp := path_values a.active trigger.low trigger.high connected
  have hp' : (path a.active trigger.low trigger.high connected).value.values =
      ⟨trigger.path.length, trigger.path.walk.vertex⟩ := by
    exact hp.trans (shortest_values_congr (RepairSelectWork.active_relation a)
      trigger.low trigger.high connected trigger.connected)
  change (selected _ _ _ _ i).value = trigger.vertices ⟨i, hi⟩
  simp only [selected, WidthScalarWork.power_value, WidthScalarWork.base_value, RepairSelectWork.width_value]
  exact crossing_of_values trigger.path.walk _ hp' s.width (RepairSelectWork.width a)
    (RepairSelectWork.width_value a) _ _

def workBound (n A : ℕ) (p : ScaleParameters) : ℕ :=
  pathBound n A + (4 * p.H + 12) + RepairSelectWork.widthBound n A +
    p.J * (selectedBound n p.J (RepairSelectWork.widthBound n A) + 2) + 3

theorem vertices_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (p : ScaleParameters) (trigger : ScaleTrigger s p) :
    (vertices a p trigger).work ≤ workBound n A p := by
  let connected : Connected (relation a.active) trigger.low trigger.high := by
    rw [RepairSelectWork.active_relation]
    exact trigger.connected
  have hp := path_work_le a.active h.active trigger.low trigger.high connected
  have hl := RepairSelectWork.width_work_le a h trigger.low
  have hv := vector_work_le
    (fun i : Fin p.J => selected (path a.active trigger.low trigger.high connected).value
      (RepairSelectWork.width a) (WidthScalarWork.base p).value (RepairSelectWork.width a trigger.low).value i.val)
    (selectedBound n p.J (RepairSelectWork.widthBound n A)) (fun i =>
      selected_work_le _ _ _ _ i.val p.J _ i.isLt.le
        (path_length_le a.active trigger.low trigger.high connected)
        (path_get_work a.active trigger.low trigger.high connected) (RepairSelectWork.width_work_le a h))
  simp only [vertices, WidthScalarWork.base_work]
  unfold workBound
  omega

end SortingAdversary.Optimal.ScaleVerticesWork
