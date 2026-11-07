import SortingAdversary.Optimal.ScaleVerticesWork
import SortingAdversary.Optimal.ScaleBlocksWork

/-! The complete materialized reservation table, obtained from measured
shortest-path crossings and measured chronological hub selection. -/

namespace SortingAdversary.Optimal.MeasuredScalePlan

open PrimitiveWork WidthRepair RepresentationWork

variable {n : ℕ} {s : State n} {p : ScaleParameters}

structure Plan (trigger : ScaleTrigger s p) (normal : EarlyNormal s p.width.W₀ p.width.L) where
  entries : Vector (ScaleBlocksWork.TypedEntry n (s.pool.palette + 1)) p.J
  exact : ∀ i : Fin p.J, entries[i] =
    ⟨trigger.vertices i, trigger.colour normal i,
      ScaleMass.intervalLower s.numerical (trigger.vertices i),
      ScaleMass.intervalUpper s.numerical (trigger.vertices i), trigger.block normal i⟩

def build (a : LocalAccess s) (p : ScaleParameters) (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) : Result (Plan trigger normal) :=
  let labels := ScaleVerticesWork.vertices a p trigger
  let get : Fin p.J → Result (Fin n) := fun i => ⟨labels.value[i], 2⟩
  have hget : ∀ i, (get i).value = trigger.vertices i := by
    intro i
    simp only [get, labels, ScaleVerticesWork.vertices_value, Fin.getElem_fin, Vector.getElem_ofFn]
  let table := ScaleBlocksWork.typed (s.pool.palette + 1) p.J a.order get (CentralChoiceWork.interval a)
    (ScaleBlocksWork.trigger_colour_bound a trigger normal get hget)
  ⟨⟨table.value, ScaleBlocksWork.typed_trigger_get a trigger normal get hget⟩,
    labels.work + table.work + 3⟩

def workBound (n palette A : ℕ) (p : ScaleParameters) : ℕ :=
  ScaleVerticesWork.workBound n A p +
    ScaleBlocksWork.workBound (palette + 1) p.J A 2 (CentralChoiceWork.workBound n A) + 8 * p.J + 4

theorem build_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (p : ScaleParameters) (trigger : ScaleTrigger s p) (normal : EarlyNormal s p.width.W₀ p.width.L) :
    (build a p trigger normal).work ≤ workBound n s.pool.palette A p := by
  let labels := ScaleVerticesWork.vertices a p trigger
  let get : Fin p.J → Result (Fin n) := fun i => ⟨labels.value[i], 2⟩
  have hget : ∀ i, (get i).value = trigger.vertices i := by
    intro i
    simp only [get, labels, ScaleVerticesWork.vertices_value, Fin.getElem_fin, Vector.getElem_ofFn]
  have hv := ScaleVerticesWork.vertices_work_le a h p trigger
  have ht := ScaleBlocksWork.typed_trigger_work_le a h trigger normal get hget 2 (fun _ => le_rfl)
  change labels.work + (ScaleBlocksWork.typed _ _ _ get _ _).work + 3 ≤ _
  change labels.work ≤ _ at hv
  unfold workBound
  omega

theorem workBound_mono {n K L A : ℕ} (p : ScaleParameters) (hK : K ≤ L) :
    workBound n K A p ≤ workBound n L A p := by
  unfold workBound ScaleBlocksWork.workBound ScaleBlocksWork.entryBound HubWork.groupPolynomial
  gcongr

end SortingAdversary.Optimal.MeasuredScalePlan
