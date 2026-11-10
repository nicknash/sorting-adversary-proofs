import SortingAdversary.Continuous.GraphOrder
import SortingAdversary.Continuous.EnclosureCoupling
import SortingAdversary.Continuous.EnclosureGuarantee
import Mathlib.Data.Finset.Sort

/-!
# Exact enclosure computation on an induced neighborhood

The retained graph contains every neighbor of each updated vertex. Thus its
conditional endpoints, affine updates and complete enumerated endpoint list
agree exactly with the full graph. The exterior does not need to be sampled,
normalized, or topologically sorted to compute these local certificates.
-/

namespace SortingAdversary.Continuous.InducedEnclosure

open FiniteAveraging OrderRegion GraphOrder MeasureTheory Set
open SortingAdversary.Optimal.GraphBalls

variable {ι κ K : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Induced interval and generating-arc data, in an explicit local indexing. -/
def induced (D : System ι K) (e : κ ↪ ι) : System κ K where
  lower x := D.lower (e x)
  upper x := D.upper (e x)
  edge x y := D.edge (e x) (e y)

section Scalar

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem induced_weaklyFeasible (D : System ι K) (e : κ ↪ ι) {Y : ι → K}
    (hY : D.WeaklyFeasible Y) : (induced D e).WeaklyFeasible (Y ∘ e) :=
  ⟨fun x => hY.1 (e x), fun x y h => hY.2 (e x) (e y) h⟩

theorem induced_strictlyFeasible (D : System ι K) (e : κ ↪ ι) {Y : ι → K}
    (hY : D.StrictlyFeasible Y) : (induced D e).StrictlyFeasible (Y ∘ e) :=
  ⟨fun x => hY.1 (e x), fun x y h => hY.2 (e x) (e y) h⟩

theorem induced_normalized (D : System ι K) (e : κ ↪ ι) (hD : Normalized D) :
    Normalized (induced D e) := fun x y h => hD (e x) (e y) h

/-- All graph neighbors of the local coordinate have been retained. -/
def ClosedAt (D : System ι K) (e : κ ↪ ι) (x : κ) : Prop :=
  ∀ y, D.edge (e x) y = true ∨ D.edge y (e x) = true → y ∈ Set.range e

theorem conditionalLower_induced (D : System ι K) (e : κ ↪ ι) (x : κ)
    (hx : ClosedAt D e x) (Y : ι → K) :
    conditionalLower (induced D e) x (Y ∘ e) = conditionalLower D (e x) Y := by
  apply le_antisymm
  · apply (Finset.fold_max_le _).mpr
    refine ⟨lower_le_conditionalLower D (e x) Y, ?_⟩
    intro y hy
    exact predecessor_le_conditionalLower D (e x) (e y) Y (Finset.mem_filter.mp hy).2
  · apply (Finset.fold_max_le _).mpr
    refine ⟨lower_le_conditionalLower (induced D e) x (Y ∘ e), ?_⟩
    intro y hy
    have hedge : D.edge y (e x) = true := by simpa using hy
    obtain ⟨z, rfl⟩ := hx y (Or.inr hedge)
    exact predecessor_le_conditionalLower (induced D e) x z (Y ∘ e) hedge

theorem conditionalUpper_induced (D : System ι K) (e : κ ↪ ι) (x : κ)
    (hx : ClosedAt D e x) (Y : ι → K) :
    conditionalUpper (induced D e) x (Y ∘ e) = conditionalUpper D (e x) Y := by
  apply le_antisymm
  · apply (Finset.le_fold_min _).mpr
    refine ⟨conditionalUpper_le_upper (induced D e) x (Y ∘ e), ?_⟩
    intro y hy
    have hedge : D.edge (e x) y = true := by simpa using hy
    obtain ⟨z, rfl⟩ := hx y (Or.inl hedge)
    exact conditionalUpper_le_successor (induced D e) x z (Y ∘ e) hedge
  · apply (Finset.le_fold_min _).mpr
    refine ⟨conditionalUpper_le_upper D (e x) Y, ?_⟩
    intro y hy
    exact conditionalUpper_le_successor D (e x) (e y) Y (Finset.mem_filter.mp hy).2

theorem update_induced (D : System ι K) (e : κ ↪ ι) (x : κ)
    (hx : ClosedAt D e x) (S : ℕ) (j : Fin S) (Y : ι → K) :
    update (induced D e) S j x (Y ∘ e) = update D S j (e x) Y ∘ e := by
  funext y
  by_cases hy : y = x
  · subst y
    simp only [Function.comp_apply, update_self,
      conditionalLower_induced D e x hx Y, conditionalUpper_induced D e x hx Y]
  · rw [update_other _ _ _ _ _ _ hy]
    exact (update_other D S j (e x) (e y) Y (e.injective.ne hy)).symm

theorem fullSteps_induced (D : System ι K) (e : κ ↪ ι) (S : ℕ)
    (steps : List (κ × Fin S)) (hclosed : ∀ step ∈ steps, ClosedAt D e step.1)
    (Y : ι → K) :
    fullSteps (induced D e) S steps (Y ∘ e) =
      fullSteps D S (steps.map fun step => (e step.1, step.2)) Y ∘ e := by
  induction steps generalizing Y with
  | nil => rfl
  | cons step steps ih =>
    simp only [fullSteps, List.foldl_cons, List.map_cons]
    rw [update_induced D e step.1 (hclosed step (by simp))]
    exact ih (fun a ha => hclosed a (by simp [ha])) _

def mapDigits {S : ℕ} (schedule : List κ) (e : κ ↪ ι)
    (digits : Fin schedule.length → Fin S) : Fin (schedule.map e).length → Fin S :=
  fun i => digits ⟨i.val, by simpa only [List.length_map] using i.isLt⟩

theorem assignedSteps_map {S : ℕ} (schedule : List κ) (e : κ ↪ ι)
    (digits : Fin schedule.length → Fin S) :
    assignedSteps S (schedule.map e) (mapDigits schedule e digits) =
      (assignedSteps S schedule digits).map (fun step => (e step.1, step.2)) := by
  unfold assignedSteps mapDigits
  simp [List.map_ofFn, Function.comp_def]

theorem words_cast (S : ℕ) {m n : ℕ} (h : m = n) :
    (words S m).map (fun digits => fun i => digits (Fin.cast h.symm i)) = words S n := by
  subst n
  simp

theorem words_mapDigits (S : ℕ) (schedule : List κ) (e : κ ↪ ι) :
    (words S schedule.length).map (mapDigits schedule e) = words S (schedule.map e).length := by
  have hm : mapDigits (S := S) schedule e =
      (fun digits i => digits (Fin.cast (List.length_map (f := (e : κ → ι)) (as := schedule)) i)) := by
    funext digits i
    congr 1
  rw [hm]
  exact words_cast S (List.length_map (f := (e : κ → ι)) (as := schedule)).symm

theorem endpointEntry_induced (D : System ι K) (e : κ ↪ ι) (S : ℕ)
    (schedule : List κ) (hclosed : ∀ x ∈ schedule, ClosedAt D e x)
    (digits : Fin schedule.length → Fin S) :
    endpointEntry (induced D e) S schedule digits =
      endpointEntry D S (schedule.map e) (mapDigits schedule e digits) ∘ e := by
  have hsteps : ∀ step ∈ assignedSteps S schedule digits, ClosedAt D e step.1 := by
    intro step hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
    exact hclosed _ (List.getElem_mem _)
  have hl := fullSteps_induced D e S (assignedSteps S schedule digits) hsteps D.lower
  have hu := fullSteps_induced D e S (assignedSteps S schedule digits) hsteps D.upper
  funext x
  simp only [endpointEntry, Function.comp_apply, assignedSteps_map]
  exact Prod.ext (congrFun hl x) (congrFun hu x)

theorem enclose_induced (D : System ι K) (e : κ ↪ ι) (S : ℕ)
    (schedule : List κ) (hclosed : ∀ x ∈ schedule, ClosedAt D e x) :
    enclose (induced D e) S schedule =
      (enclose D S (schedule.map e)).map (fun I => I ∘ e) := by
  have hentry := endpointEntry_induced D e S schedule hclosed
  unfold enclose
  rw [← words_mapDigits S schedule e]
  simp only [List.map_map]
  apply List.map_congr_left
  intro digits hdigits
  exact hentry digits

end Scalar

@[simp] theorem induced_toReal (D : System ι ℚ) (e : κ ↪ ι) :
    (induced D e).toReal = induced D.toReal e := rfl

theorem induced_volume_pos (D : System ι ℝ) (e : κ ↪ ι)
    (hV : 0 < volume (region D)) : 0 < volume (region (induced D e)) := by
  apply (volume_pos_iff_nonempty _).mpr
  obtain ⟨Y, hY⟩ := (volume_pos_iff_nonempty D).mp hV
  exact ⟨Y ∘ e, induced_strictlyFeasible D e hY⟩

theorem neighbors_induced_subset (D : System ι K) (e : κ ↪ ι) (x : κ) :
    (neighbors (induced D e).edge x).image e ⊆ neighbors D.edge (e x) := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  rw [mem_neighbors] at hz ⊢
  exact ⟨e.injective.ne hz.1, hz.2⟩

theorem neighbors_induced_card (D : System ι K) (e : κ ↪ ι) (x : κ) :
    (neighbors (induced D e).edge x).card ≤ (neighbors D.edge (e x)).card := by
  calc
    _ = ((neighbors (induced D e).edge x).image e).card :=
      (Finset.card_image_of_injective _ e.injective).symm
    _ ≤ _ := Finset.card_le_card (neighbors_induced_subset D e x)

theorem ball_induced_subset (D : System ι K) (e : κ ↪ ι) (x : κ) (r : ℕ) :
    (ball (induced D e).edge x r).image e ⊆ ball D.edge (e x) r := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  clear hy
  induction r generalizing x z with
  | zero => simpa only [ball_zero, Finset.mem_singleton] using congrArg e (Finset.mem_singleton.mp hz)
  | succ r ih =>
    obtain ⟨w, hw, hzw⟩ := (mem_ball_succ _ _ _ _).mp hz
    apply (mem_ball_succ _ _ _ _).mpr
    refine ⟨e w, ?_, ih w z hzw⟩
    simpa only [mem_closedNeighbors, induced, e.injective.eq_iff] using hw

section Indexing

variable {n : ℕ}

/-- Retained labels are indexed in their original increasing label order. -/
def label (R : Finset (Fin n)) : Fin R.card ↪ Fin n := (R.orderEmbOfFin rfl).toEmbedding

def localIndex (R : Finset (Fin n)) (x : Fin n) (hx : x ∈ R) : Fin R.card :=
  (R.orderIsoOfFin rfl).symm ⟨x, hx⟩

@[simp] theorem label_localIndex (R : Finset (Fin n)) (x : Fin n) (hx : x ∈ R) :
    label R (localIndex R x hx) = x := by
  exact congrArg Subtype.val ((R.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)

@[simp] theorem label_mem (R : Finset (Fin n)) (x : Fin R.card) : label R x ∈ R :=
  R.orderEmbOfFin_mem rfl x

theorem range_label (R : Finset (Fin n)) : Set.range (label R) = R := by
  exact R.range_orderEmbOfFin rfl

/-- The union of the required undirected generating-graph balls. -/
def retained (D : System (Fin n) K) (Q : Finset (Fin n)) (r : ℕ) : Finset (Fin n) :=
  Q.biUnion fun x => ball D.edge x r

theorem query_mem_retained (D : System (Fin n) K) (Q : Finset (Fin n)) (r : ℕ)
    (x : Fin n) (hx : x ∈ Q) : x ∈ retained D Q r :=
  Finset.mem_biUnion.mpr ⟨x, hx, center_mem_ball D.edge x r⟩

theorem retained_mono (D : System (Fin n) K) (Q : Finset (Fin n)) {r s : ℕ}
    (hrs : r ≤ s) : retained D Q r ⊆ retained D Q s := by
  intro x hx
  obtain ⟨q, hq, hxq⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨q, hq, ball_mono D.edge q hrs hxq⟩

theorem retained_closed (D : System (Fin n) K) (Q : Finset (Fin n)) (r : ℕ)
    (x : Fin (retained D Q (r + 1)).card) (hx : label _ x ∈ retained D Q r) :
    ClosedAt D (label (retained D Q (r + 1))) x := by
  intro y hy
  rw [range_label]
  obtain ⟨q, hq, hxq⟩ := Finset.mem_biUnion.mp hx
  refine Finset.mem_biUnion.mpr ⟨q, hq, mem_ball_add D.edge hxq ?_⟩
  exact (mem_ball_one D.edge _ y).mpr ((mem_closedNeighbors D.edge _ y).mpr (Or.inr hy))

theorem retained_card (D : System (Fin n) K) (Q : Finset (Fin n)) (d r : ℕ)
    (hdegree : ∀ x, (neighbors D.edge x).card ≤ d) :
    (retained D Q r).card ≤ Q.card * (d + 1) ^ r := by
  calc
    _ ≤ ∑ x ∈ Q, (ball D.edge x r).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ Q, (d + 1) ^ r := Finset.sum_le_sum (fun x _ => ball_card_le D.edge d hdegree x r)
    _ = _ := by simp

end Indexing

end SortingAdversary.Continuous.InducedEnclosure
