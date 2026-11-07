import SortingAdversary.Optimal.CentralChoiceWork
import SortingAdversary.Optimal.HubWork
import SortingAdversary.Optimal.WidthScaleSelect

/-!
# Measured scale-group block and colour tables

Reserved labels are supplied by their measured materialized getters. The
central intervals are cached once, the chronological veto selector runs on
those cached intervals, and every selected block is indexed and sorted with
its traversal cost paid. Runtime functions below take explicit carrier and
palette sizes; the semantic scale trigger appears only in correctness
proofs, so its path and first crossings are never recomputed.
-/

namespace SortingAdversary.Optimal.ScaleBlocksWork

open PrimitiveWork HubSelector HubSortWork

variable {n births count : ℕ}

structure Window (n : ℕ) where
  vertex : Fin n
  lower : ℕ
  upper : ℕ

structure Entry (n : ℕ) where
  window : Window n
  block : Block
  colour : ℕ

def prepare (vertices : Fin count → Result (Fin n))
    (central : Fin n → Result (ℕ × ℕ)) : Result (Vector (Window n) count) :=
  PrimitiveWork.vector fun i =>
    let vertex := vertices i
    let interval := central vertex.value
    ⟨⟨vertex.value, interval.value.1, interval.value.2⟩, vertex.work + interval.work + 4⟩

@[simp] theorem prepare_get (vertices : Fin count → Result (Fin n))
    (central : Fin n → Result (ℕ × ℕ)) (i : Fin count) :
    (prepare vertices central).value[i] =
      ⟨(vertices i).value, (central (vertices i).value).value.1,
        (central (vertices i).value).value.2⟩ := by
  simp only [prepare, PrimitiveWork.vector_value, Fin.getElem_fin, Vector.getElem_ofFn]

theorem prepare_work_le (vertices : Fin count → Result (Fin n))
    (central : Fin n → Result (ℕ × ℕ)) (V C : ℕ)
    (hv : ∀ i, (vertices i).work ≤ V) (hc : ∀ v, (central v).work ≤ C) :
    (prepare vertices central).work ≤ count * (V + C + 6) := by
  apply (PrimitiveWork.vector_work_le _ (V + C + 4) (fun i => by
    have hvi := hv i
    have hci := hc (vertices i).value
    dsimp only
    omega)).trans_eq
  congr 1

def lower (windows : Vector (Window n) count) (j : ℕ) : Result ℕ :=
  if hj : j < count then ⟨windows[j].lower, 3⟩ else ⟨0, 1⟩

def upper (windows : Vector (Window n) count) (j : ℕ) : Result ℕ :=
  if hj : j < count then ⟨windows[j].upper, 3⟩ else ⟨0, 1⟩

theorem lower_work_le (windows : Vector (Window n) count) (j : ℕ) :
    (lower windows j).work ≤ 3 := by unfold lower; split <;> dsimp only <;> omega

theorem upper_work_le (windows : Vector (Window n) count) (j : ℕ) :
    (upper windows j).work ≤ 3 := by unfold upper; split <;> dsimp only <;> omega

def blocks (births : ℕ) (get : Fin births → Result (Fin births))
    (windows : Vector (Window n) count) : Result (List Block) :=
  HubWork.selectPaletteGroup births (paletteRank get) (lower windows) (upper windows) count

theorem blocks_value (order : Equiv.Perm (Fin births))
    (get : Fin births → Result (Fin births)) (heq : ∀ i, (get i).value = order i)
    (windows : Vector (Window n) count) :
    (blocks births get windows).value = ScaleHubs.selectPaletteGroup order
      (fun j => (lower windows j).value) (fun j => (upper windows j).value) count :=
  HubWork.selectPaletteGroup_value order (paletteRank get) (paletteRank_value order get heq) _ _ _

theorem blocks_work_le (get : Fin births → Result (Fin births))
    (windows : Vector (Window n) count) (A : ℕ) (hA : ∀ i, (get i).work ≤ A) :
    (blocks births get windows).work ≤ HubWork.groupPolynomial births count (A + 1) 3 :=
  HubWork.selectPaletteGroup_polynomial births (paletteRank get) _ _ count (A + 1) 3
    (paletteRank_work_le get A hA) (lower_work_le windows) (upper_work_le windows)

def fallback : Block := ⟨⟨0, 0⟩, 0, 0⟩

def entry (get : Fin births → Result (Fin births)) (windows : Vector (Window n) count)
    (selected : List Block) (i : Fin count) : Result (Entry n) :=
  let block := getD fallback selected i.val
  let hub := hubColour (paletteRank get) block.value
  let position := paletteRank get hub.value
  ⟨⟨windows[i], block.value, position.value⟩, block.work + hub.work + position.work + 7⟩

theorem entry_get (order : Equiv.Perm (Fin births))
    (get : Fin births → Result (Fin births)) (heq : ∀ i, (get i).value = order i)
    (windows : Vector (Window n) count) (selected : List Block) (i : Fin count) :
    (entry get windows selected i).value =
      ⟨windows[i], selected.getD i.val fallback,
        BatchWindows.paletteRank order (HubSelector.hubColour (BatchWindows.paletteRank order)
          (BatchWindows.paletteRank_injective order) (selected.getD i.val fallback))⟩ := by
  have hrank := paletteRank_value order get heq
  have hinj : Function.Injective (rankValues (paletteRank get)) := by
    rw [hrank]
    exact BatchWindows.paletteRank_injective order
  simp only [entry, getD_value, hubColour_value _ hinj]
  change _ = Entry.mk _ _ _
  have hvalue : ∀ i, (paletteRank get i).value = BatchWindows.paletteRank order i :=
    fun i => congrFun hrank i
  simp only [hvalue, hrank]

def entryBound (births count A : ℕ) : ℕ :=
  (2 * count + 1) + (11 * births + 10 + (births + 1) ^ 2 * (2 * (A + 1) + 5)) + (A + 1) + 7

theorem entry_work_le (order : Equiv.Perm (Fin births))
    (get : Fin births → Result (Fin births)) (heq : ∀ i, (get i).value = order i)
    (windows : Vector (Window n) count) (selected : List Block) (i : Fin count)
    (hlen : selected.length = count) (hblocks : ∀ block ∈ selected, block ∈ allBlocks births)
    (A : ℕ) (hA : ∀ i, (get i).work ≤ A) :
    (entry get windows selected i).work ≤ entryBound births count A := by
  have hrank := paletteRank_value order get heq
  have hinj : Function.Injective (rankValues (paletteRank get)) := by
    rw [hrank]
    exact BatchWindows.paletteRank_injective order
  have hi : i.val < selected.length := by rw [hlen]; exact i.isLt
  have hb : (getD fallback selected i.val).value ∈ allBlocks births := by
    rw [getD_value, List.getD_eq_getElem _ _ hi]
    exact hblocks _ (List.getElem_mem _)
  have hindex := getD_work_le fallback selected i.val
  rw [hlen] at hindex
  have hhub := HubWork.current_hub_work_le births (paletteRank get) hinj
    (getD fallback selected i.val).value hb (A + 1) (paletteRank_work_le get A hA)
  have hposition := paletteRank_work_le get A hA
    (hubColour (paletteRank get) (getD fallback selected i.val).value).value
  change _ + _ + _ + 7 ≤ _
  unfold entryBound
  omega

def compute (births count : ℕ) (get : Fin births → Result (Fin births))
    (vertices : Fin count → Result (Fin n)) (central : Fin n → Result (ℕ × ℕ)) :
    Result (Vector (Entry n) count) :=
  let windows := prepare vertices central
  let selected := blocks births get windows.value
  let entries := PrimitiveWork.vector (entry get windows.value selected.value)
  ⟨entries.value, windows.work + selected.work + entries.work + 3⟩

theorem compute_get (order : Equiv.Perm (Fin births))
    (get : Fin births → Result (Fin births)) (heq : ∀ i, (get i).value = order i)
    (vertices : Fin count → Result (Fin n)) (central : Fin n → Result (ℕ × ℕ)) (i : Fin count) :
    (compute births count get vertices central).value[i] =
      (entry get (prepare vertices central).value
        (blocks births get (prepare vertices central).value).value i).value := by
  simp only [compute, PrimitiveWork.vector_value, Fin.getElem_fin, Vector.getElem_ofFn]

def workBound (births count A V C : ℕ) : ℕ :=
  count * (V + C + 6) + HubWork.groupPolynomial births count (A + 1) 3 +
    count * (entryBound births count A + 2) + 3

theorem compute_work_le (order : Equiv.Perm (Fin births))
    (get : Fin births → Result (Fin births)) (heq : ∀ i, (get i).value = order i)
    (vertices : Fin count → Result (Fin n)) (central : Fin n → Result (ℕ × ℕ))
    (hlen : (blocks births get (prepare vertices central).value).value.length = count)
    (A V C : ℕ) (hA : ∀ i, (get i).work ≤ A) (hV : ∀ i, (vertices i).work ≤ V)
    (hC : ∀ v, (central v).work ≤ C) :
    (compute births count get vertices central).work ≤ workBound births count A V C := by
  let windows := prepare vertices central
  let selected := blocks births get windows.value
  have hblocks : ∀ block ∈ selected.value, block ∈ allBlocks births := by
    intro block hb
    rw [blocks_value order get heq] at hb
    exact HubSelector.selectGroup_mem_allBlocks _ _ _ _ _ _ hb
  have hp := prepare_work_le vertices central V C hV hC
  have hs := blocks_work_le get windows.value A hA
  have he := PrimitiveWork.vector_work_le (entry get windows.value selected.value)
    (entryBound births count A)
    (fun i => entry_work_le order get heq windows.value selected.value i hlen hblocks A hA)
  change windows.work + selected.work +
    (PrimitiveWork.vector (entry get windows.value selected.value)).work + 3 ≤ _
  change windows.work ≤ _ at hp
  change selected.work ≤ _ at hs
  unfold workBound
  omega

open WidthRepair RepresentationWork

variable {s : State n} {p : ScaleParameters}

theorem prepare_trigger_get (a : LocalAccess s) (trigger : ScaleTrigger s p)
    (vertices : Fin p.J → Result (Fin n)) (heq : ∀ i, (vertices i).value = trigger.vertices i)
    (i : Fin p.J) :
    (prepare vertices (CentralChoiceWork.interval a)).value[i] =
      ⟨trigger.vertices i, ScaleMass.intervalLower s.numerical (trigger.vertices i),
        ScaleMass.intervalUpper s.numerical (trigger.vertices i)⟩ := by
  rw [prepare_get, heq, CentralChoiceWork.interval_value]

theorem lower_trigger (a : LocalAccess s) (trigger : ScaleTrigger s p)
    (vertices : Fin p.J → Result (Fin n)) (heq : ∀ i, (vertices i).value = trigger.vertices i) :
    (fun j => (lower (prepare vertices (CentralChoiceWork.interval a)).value j).value) = trigger.lower := by
  funext j
  by_cases hj : j < p.J
  · simp only [lower, ScaleTrigger.lower, dif_pos hj]
    exact congrArg Window.lower (prepare_trigger_get a trigger vertices heq ⟨j, hj⟩)
  · simp only [lower, ScaleTrigger.lower, dif_neg hj]

theorem upper_trigger (a : LocalAccess s) (trigger : ScaleTrigger s p)
    (vertices : Fin p.J → Result (Fin n)) (heq : ∀ i, (vertices i).value = trigger.vertices i) :
    (fun j => (upper (prepare vertices (CentralChoiceWork.interval a)).value j).value) = trigger.upper := by
  funext j
  by_cases hj : j < p.J
  · simp only [upper, ScaleTrigger.upper, dif_pos hj]
    exact congrArg Window.upper (prepare_trigger_get a trigger vertices heq ⟨j, hj⟩)
  · simp only [upper, ScaleTrigger.upper, dif_neg hj]

theorem blocks_trigger (a : LocalAccess s) (trigger : ScaleTrigger s p)
    (vertices : Fin p.J → Result (Fin n)) (heq : ∀ i, (vertices i).value = trigger.vertices i) :
    (blocks (s.pool.palette + 1) a.order (prepare vertices (CentralChoiceWork.interval a)).value).value =
      trigger.blocks := by
  rw [blocks_value s.order a.order a.order_value, lower_trigger a trigger vertices heq,
    upper_trigger a trigger vertices heq]
  rfl

theorem compute_trigger_get (a : LocalAccess s) (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L)
    (vertices : Fin p.J → Result (Fin n)) (heq : ∀ i, (vertices i).value = trigger.vertices i)
    (i : Fin p.J) :
    (compute (s.pool.palette + 1) p.J a.order vertices (CentralChoiceWork.interval a)).value[i] =
      ⟨⟨trigger.vertices i, ScaleMass.intervalLower s.numerical (trigger.vertices i),
        ScaleMass.intervalUpper s.numerical (trigger.vertices i)⟩,
        trigger.block normal i, (trigger.colour normal i).val⟩ := by
  rw [compute_get s.order a.order a.order_value,
    entry_get s.order a.order a.order_value, blocks_trigger a trigger vertices heq,
    prepare_trigger_get a trigger vertices heq]
  rw [List.getD_eq_getElem trigger.blocks fallback (by rw [trigger.blocks_length normal]; exact i.isLt)]
  rfl

theorem compute_trigger_work_le (a : LocalAccess s) {A : ℕ} (hA : AccessBound a A)
    (trigger : ScaleTrigger s p) (normal : EarlyNormal s p.width.W₀ p.width.L)
    (vertices : Fin p.J → Result (Fin n)) (heq : ∀ i, (vertices i).value = trigger.vertices i)
    (V : ℕ) (hV : ∀ i, (vertices i).work ≤ V) :
    (compute (s.pool.palette + 1) p.J a.order vertices (CentralChoiceWork.interval a)).work ≤
      workBound (s.pool.palette + 1) p.J A V (CentralChoiceWork.workBound n A) := by
  exact compute_work_le s.order a.order a.order_value vertices (CentralChoiceWork.interval a)
    (by rw [blocks_trigger a trigger vertices heq, trigger.blocks_length normal])
    A V (CentralChoiceWork.workBound n A) hA.order hV (CentralChoiceWork.interval_work_le a hA)

/-- The complete runtime scale-reservation row, with its checked finite colour. -/
structure TypedEntry (n births : ℕ) where
  vertex : Fin n
  colour : Fin births
  lower : ℕ
  upper : ℕ
  block : Block

def finiteEntries (table : Vector (Entry n) count) (hb : ∀ i : Fin count, table[i].colour < births) :
    Result (Vector (TypedEntry n births) count) :=
  PrimitiveWork.vector fun i =>
    let row := table[i]
    ⟨⟨row.window.vertex, ⟨row.colour, hb i⟩, row.window.lower, row.window.upper, row.block⟩, 6⟩

@[simp] theorem finiteEntries_get (table : Vector (Entry n) count)
    (hb : ∀ i : Fin count, table[i].colour < births) (i : Fin count) :
    (finiteEntries table hb).value[i] =
      ⟨table[i].window.vertex, ⟨table[i].colour, hb i⟩, table[i].window.lower,
        table[i].window.upper, table[i].block⟩ := by
  simp only [finiteEntries, PrimitiveWork.vector_value, Fin.getElem_fin, Vector.getElem_ofFn]

theorem finiteEntries_work_le (table : Vector (Entry n) count)
    (hb : ∀ i : Fin count, table[i].colour < births) : (finiteEntries table hb).work ≤ 8 * count := by
  simpa only [Nat.mul_comm, Nat.reduceAdd, finiteEntries] using PrimitiveWork.vector_work_le
    (fun i => (⟨(⟨table[i].window.vertex, ⟨table[i].colour, hb i⟩, table[i].window.lower,
      table[i].window.upper, table[i].block⟩ : TypedEntry n births), 6⟩ : Result (TypedEntry n births)))
    6 (fun _ => le_rfl)

def typed (births count : ℕ) (get : Fin births → Result (Fin births))
    (vertices : Fin count → Result (Fin n)) (central : Fin n → Result (ℕ × ℕ))
    (hb : ∀ i : Fin count, (compute births count get vertices central).value[i].colour < births) :
    Result (Vector (TypedEntry n births) count) :=
  let raw := compute births count get vertices central
  let result := finiteEntries raw.value hb
  ⟨result.value, raw.work + result.work + 1⟩

theorem trigger_colour_bound (a : LocalAccess s) (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L)
    (vertices : Fin p.J → Result (Fin n)) (heq : ∀ i, (vertices i).value = trigger.vertices i)
    (i : Fin p.J) :
    (compute (s.pool.palette + 1) p.J a.order vertices (CentralChoiceWork.interval a)).value[i].colour <
      s.pool.palette + 1 := by
  rw [compute_trigger_get a trigger normal vertices heq i]
  exact (trigger.colour normal i).isLt

theorem typed_trigger_get (a : LocalAccess s) (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L)
    (vertices : Fin p.J → Result (Fin n)) (heq : ∀ i, (vertices i).value = trigger.vertices i)
    (i : Fin p.J) :
    (typed (s.pool.palette + 1) p.J a.order vertices (CentralChoiceWork.interval a)
      (trigger_colour_bound a trigger normal vertices heq)).value[i] =
      ⟨trigger.vertices i, trigger.colour normal i,
        ScaleMass.intervalLower s.numerical (trigger.vertices i),
        ScaleMass.intervalUpper s.numerical (trigger.vertices i), trigger.block normal i⟩ := by
  simp only [typed, finiteEntries_get]
  simp only [compute_trigger_get a trigger normal vertices heq i]

theorem typed_trigger_work_le (a : LocalAccess s) {A : ℕ} (hA : AccessBound a A)
    (trigger : ScaleTrigger s p) (normal : EarlyNormal s p.width.W₀ p.width.L)
    (vertices : Fin p.J → Result (Fin n)) (heq : ∀ i, (vertices i).value = trigger.vertices i)
    (V : ℕ) (hV : ∀ i, (vertices i).work ≤ V) :
    (typed (s.pool.palette + 1) p.J a.order vertices (CentralChoiceWork.interval a)
      (trigger_colour_bound a trigger normal vertices heq)).work ≤
      workBound (s.pool.palette + 1) p.J A V (CentralChoiceWork.workBound n A) + 8 * p.J + 1 := by
  have hc := compute_trigger_work_le a hA trigger normal vertices heq V hV
  have hs := finiteEntries_work_le
    (compute (s.pool.palette + 1) p.J a.order vertices (CentralChoiceWork.interval a)).value
    (trigger_colour_bound a trigger normal vertices heq)
  change _ + _ + 1 ≤ _
  omega

end SortingAdversary.Optimal.ScaleBlocksWork
