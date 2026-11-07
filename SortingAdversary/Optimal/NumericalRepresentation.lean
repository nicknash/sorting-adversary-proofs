import SortingAdversary.Optimal.CutNormalization
import SortingAdversary.Optimal.PinElimination
import SortingAdversary.Optimal.RefinementTransitions
import SortingAdversary.Optimal.Promotion
import SortingAdversary.Optimal.SparseRepairGraph

/-!
# Persistent source rows and the sparse numerical view

Primitive comparison rows are retained as history. The public relation is
their closure. A source row may leave the active free graph only when it is
incident to a physical pin or its endpoints have strictly separated primitive
walls. Numerical lists are recomputed from the public closure and are never
stored back as primitive artificial walls.
-/

namespace SortingAdversary.Optimal.NumericalRepresentation

open WeakMaps WeakMaps.WeakSystem SparseClosure FiniteRefinement
open ControllerRouting PinTransitions RefinementTransitions CutNormalization
open scoped BigOperators

variable {n K L : ℕ}

theorem along_subset_closed (R P : Rows (Fin n))
    (htrans : ∀ x y z, P x y = true → P y z = true → P x z = true)
    (hsub : ∀ x y, R x y = true → P x y = true) (ks : List (Fin n)) :
    ∀ x y, along R ks x y = true → P x y = true := by
  induction ks generalizing R with
  | nil => exact hsub
  | cons k ks ih =>
    apply ih (via R k)
    intro x y hxy
    rcases (via_true R k x y).mp hxy with hxy | ⟨hxk, hky⟩
    · exact hsub x y hxy
    · exact htrans x k y (hsub x k hxk) (hsub k y hky)

theorem closure_subset_closed (R P : Rows (Fin n))
    (hrefl : ∀ x, P x x = true)
    (htrans : ∀ x y z, P x y = true → P y z = true → P x z = true)
    (hsub : ∀ x y, R x y = true → P x y = true) :
    ∀ x y, closure R x y = true → P x y = true := by
  apply along_subset_closed (reflexive R) P htrans
  intro x y hxy
  have hh : R x y = true ∨ x = y := by simpa [reflexive] using hxy
  rcases hh with hh | rfl
  · exact hsub x y hh
  · exact hrefl x

/-- A source history and an explicitly justified active subset. -/
structure SourcePartition (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) where
  source : Rows (Fin n)
  active : Rows (Fin n)
  proper : ∀ u v, source u v = true → u ≠ v
  public_eq : S.edge = closure source
  active_source : ∀ u v, active u v = true → source u v = true
  active_free : ∀ u v, active u v = true → pins u = none ∧ pins v = none
  covered : ∀ u v, source u v = true →
    active u v = true ∨ pins u ≠ none ∨ pins v ≠ none ∨ S.upper u < S.lower v

namespace SourcePartition

variable {S : WeakSystem (Fin n) (K + 1)} {pins : Fin n → Option (Fin (K + 1))}

theorem closed (R : SourcePartition S pins) : S.Closed := by
  constructor
  · intro x
    rw [R.public_eq]
    exact closure_refl R.source x
  · intro x y z hxy hyz
    rw [R.public_eq] at hxy hyz ⊢
    exact closure_trans R.source x y z hxy hyz

theorem source_public (R : SourcePartition S pins) {u v : Fin n}
    (huv : R.source u v = true) : S.edge u v = true := by
  rw [R.public_eq]
  exact closure_old R.source huv

theorem active_public (R : SourcePartition S pins) {u v : Fin n}
    (huv : R.active u v = true) : S.edge u v = true :=
  R.source_public (R.active_source u v huv)

/-- Derived numerical bounds paired with the current sparse free graph. -/
def view (R : SourcePartition S pins) : WeakSystem (Fin n) (K + 1) where
  edge := R.active
  lower := S.effectiveLower
  upper := S.effectiveUpper

theorem primitive_bounds (R : SourcePartition S pins) {f : ColorMap (Fin n) (K + 1)}
    (hf : R.view.Valid f) (v : Fin n) : S.lower v ≤ f v ∧ f v ≤ S.upper v :=
  ⟨(S.lower_le_effectiveLower (R.closed.refl v)).trans (hf.1 v).1,
    (hf.1 v).2.trans (S.effectiveUpper_le_upper (R.closed.refl v))⟩

/-- Every omitted source row follows from a fixed pin or two primitive walls.
This proves equality of the complete finite laws, with no feasibility premise. -/
theorem view_valid (R : SourcePartition S pins) (hp : PinBounds S pins)
    (f : ColorMap (Fin n) (K + 1)) : R.view.Valid f ↔ S.Valid f := by
  constructor
  · intro hf
    have hb := R.primitive_bounds hf
    have hpin (x : Fin n) (c : Fin (K + 1)) (hx : pins x = some c) : f x = c := by
      obtain ⟨hl, hu⟩ := hp x c hx
      exact le_antisymm (hu ▸ (hb x).2) (hl ▸ (hb x).1)
    refine ⟨hb, ?_⟩
    change Respects S.edge f
    rw [R.public_eq]
    apply (respects_closure R.source f).mpr
    intro u v huv
    have hpublic := R.source_public huv
    rcases R.covered u v huv with hactive | hpu | hpv | hwall
    · exact hf.2 u v hactive
    · cases hu : pins u with
      | none => exact False.elim (hpu hu)
      | some c =>
        calc
          f u = c := hpin u c hu
          _ = S.lower u := (hp u c hu).1.symm
          _ ≤ S.effectiveLower v := S.lower_le_effectiveLower hpublic
          _ ≤ f v := (hf.1 v).1
    · cases hv : pins v with
      | none => exact False.elim (hpv hv)
      | some c =>
        calc
          f u ≤ S.effectiveUpper u := (hf.1 u).2
          _ ≤ S.upper v := S.effectiveUpper_le_upper hpublic
          _ = c := (hp v c hv).2
          _ = f v := (hpin v c hv).symm
    · exact (hb u).2.trans (hwall.le.trans (hb v).1)
  · intro hf
    exact ⟨fun v => S.valid_between_windows f hf v,
      fun u v huv => hf.2 u v (R.active_public huv)⟩

theorem view_maps (R : SourcePartition S pins) (hp : PinBounds S pins) : R.view.maps = S.maps := by
  ext f
  simp only [mem_maps, R.view_valid hp]

theorem view_count (R : SourcePartition S pins) (hp : PinBounds S pins) : R.view.count = S.count := by
  simp only [count, R.view_maps hp]

theorem view_fiber (R : SourcePartition S pins) (hp : PinBounds S pins)
    (v : Fin n) (c : Fin (K + 1)) : R.view.fiber v c = S.fiber v c := by
  simp only [fiber, R.view_maps hp]

theorem event_probability_eq (R : SourcePartition S pins) (hp : PinBounds S pins)
    (P : ColorMap (Fin n) (K + 1) → Prop) [DecidablePred P] :
    ((R.view.maps.filter P).card : ℚ) / R.view.count = ((S.maps.filter P).card : ℚ) / S.count := by
  rw [R.view_maps hp, R.view_count hp]

theorem view_windows (R : SourcePartition S pins) (hp : PinBounds S pins)
    (hne : ∃ f, S.Valid f) (v : Fin n) :
    (closeSystem R.view).effectiveLower v = S.effectiveLower v ∧
      (closeSystem R.view).effectiveUpper v = S.effectiveUpper v :=
  PinElimination.windows_eq_of_valid_iff S (closeSystem R.view) R.closed (closeSystem_closed _)
    hne (fun f => (closeSystem_valid _ f).trans (R.view_valid hp f)) v

theorem view_invariant (R : SourcePartition S pins) (h : Invariant S pins) (hp : PinBounds S pins) :
    Invariant (closeSystem R.view) pins := by
  have hold : ∀ u v, (closeSystem R.view).edge u v = true → S.edge u v = true := by
    intro u v huv
    have hh : closure R.active u v = true := by
      simpa only [closeSystem, view, lookup_tableClosure] using huv
    exact closure_subset_closed R.active S.edge h.closed.refl h.closed.trans
      (fun _ _ hab => R.active_public hab) u v hh
  have heq (f : ColorMap (Fin n) (K + 1)) : (closeSystem R.view).Valid f ↔ S.Valid f :=
    (closeSystem_valid R.view f).trans (R.view_valid hp f)
  refine ⟨closeSystem_closed _, ?_, ?_, ?_, ?_⟩
  · exact fun u v huv hvu => h.antisymm u v (hold u v huv) (hold v u hvu)
  · obtain ⟨f, hf⟩ := h.feasible
    exact ⟨f, (heq f).mpr hf⟩
  · exact fun f hf => h.pins_valid f ((heq f).mp hf)
  · intro v hv
    have hw := R.view_windows hp h.feasible v
    rw [hw.1, hw.2]
    exact h.free_window v hv

theorem propagate_view (R : SourcePartition S pins) (hp : PinBounds S pins)
    (hne : ∃ f, S.Valid f) : propagateSystem R.view = R.view := by
  have hl : (closeSystem R.view).effectiveLower = S.effectiveLower :=
    funext (fun v => (R.view_windows hp hne v).1)
  have hu : (closeSystem R.view).effectiveUpper = S.effectiveUpper :=
    funext (fun v => (R.view_windows hp hne v).2)
  change WeakSystem.mk R.active (closeSystem R.view).effectiveLower (closeSystem R.view).effectiveUpper =
    WeakSystem.mk R.active S.effectiveLower S.effectiveUpper
  rw [hl, hu]

theorem pin_isolated (R : SourcePartition S pins) {v : Fin n} (hv : pins v ≠ none) (x : Fin n) :
    R.active v x = false ∧ R.active x v = false := by
  constructor <;> apply Bool.eq_false_iff.mpr
  · exact fun h => hv (R.active_free v x h).1
  · exact fun h => hv (R.active_free x v h).2

end SourcePartition

/-- Bootstrap from a closed public system. Subsequent transitions add one
source row at a time, rather than rebuilding this transitive set. -/
def fromClosed (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) (hS : S.Closed) : SourcePartition S pins where
  source u v := S.edge u v && decide (u ≠ v)
  active u v := S.edge u v && decide (u ≠ v ∧ pins u = none ∧ pins v = none)
  proper := by
    intro u v h
    have hh : S.edge u v = true ∧ u ≠ v := by simpa using h
    exact hh.2
  public_eq := by
    funext u v
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro huv
      by_cases heq : u = v
      · subst v
        exact closure_refl _ _
      · exact closure_old _ (by simp [huv, heq])
    · apply closure_subset_closed _ S.edge hS.refl hS.trans
      intro x y hxy
      have hh : S.edge x y = true ∧ x ≠ y := by simpa using hxy
      exact hh.1
  active_source := by
    intro u v h
    have hh : S.edge u v = true ∧ u ≠ v ∧ pins u = none ∧ pins v = none := by simpa using h
    simp [hh.1, hh.2.1]
  active_free := by
    intro u v h
    have hh : S.edge u v = true ∧ u ≠ v ∧ pins u = none ∧ pins v = none := by simpa using h
    exact hh.2.2
  covered := by
    intro u v h
    have hh : S.edge u v = true ∧ u ≠ v := by simpa using h
    by_cases hu : pins u = none
    · by_cases hv : pins v = none
      · exact Or.inl (by simp [hh.1, hh.2, hu, hv])
      · exact Or.inr (Or.inr (Or.inl hv))
    · exact Or.inr (Or.inl hu)

namespace SourcePartition

variable {S : WeakSystem (Fin n) (K + 1)} {pins : Fin n → Option (Fin (K + 1))}

/-- Carry the history through a primitive-wall or palette update. Only rows
whose endpoints are still free remain active. -/
def transport (R : SourcePartition S pins) (T : WeakSystem (Fin n) (L + 1))
    (newPins : Fin n → Option (Fin (L + 1))) (hedge : T.edge = S.edge)
    (hpersist : ∀ x, pins x ≠ none → newPins x ≠ none)
    (hwall : ∀ u v, S.upper u < S.lower v → T.upper u < T.lower v) :
    SourcePartition T newPins where
  source := R.source
  active u v := R.active u v && decide (newPins u = none ∧ newPins v = none)
  proper := R.proper
  public_eq := hedge.trans R.public_eq
  active_source := by
    intro u v h
    have hh : R.active u v = true ∧ newPins u = none ∧ newPins v = none := by simpa using h
    exact R.active_source u v hh.1
  active_free := by
    intro u v h
    have hh : R.active u v = true ∧ newPins u = none ∧ newPins v = none := by simpa using h
    exact hh.2
  covered := by
    intro u v huv
    rcases R.covered u v huv with ha | hu | hv | hw
    · by_cases hu : newPins u = none
      · by_cases hv : newPins v = none
        · exact Or.inl (by simp [ha, hu, hv])
        · exact Or.inr (Or.inr (Or.inl hv))
      · exact Or.inr (Or.inl hu)
    · exact Or.inr (Or.inl (hpersist u hu))
    · exact Or.inr (Or.inr (Or.inl (hpersist v hv)))
    · exact Or.inr (Or.inr (Or.inr (hwall u v hw)))

/-- Retire one active numerical row while keeping its original source row. -/
def retire (R : SourcePartition S pins) (u v : Fin n) (hwall : S.upper u < S.lower v) :
    SourcePartition S pins where
  source := R.source
  active x y := if x = u ∧ y = v then false else R.active x y
  proper := R.proper
  public_eq := R.public_eq
  active_source := by
    intro x y h
    by_cases hxy : x = u ∧ y = v
    · simp only [if_pos hxy, Bool.false_eq_true] at h
    · exact R.active_source x y (by simpa only [if_neg hxy] using h)
  active_free := by
    intro x y h
    by_cases hxy : x = u ∧ y = v
    · simp only [if_pos hxy, Bool.false_eq_true] at h
    · exact R.active_free x y (by simpa only [if_neg hxy] using h)
  covered := by
    intro x y hsource
    rcases R.covered x y hsource with ha | hu | hv | hw
    · by_cases hxy : x = u ∧ y = v
      · obtain ⟨rfl, rfl⟩ := hxy
        exact Or.inr (Or.inr (Or.inr hwall))
      · exact Or.inl (by simpa only [if_neg hxy] using ha)
    · exact Or.inr (Or.inl hu)
    · exact Or.inr (Or.inr (Or.inl hv))
    · exact Or.inr (Or.inr (Or.inr hw))

/-- Install the actual two primitive walls and retire the corresponding raw
row. Other previously retired source rows remain justified by their walls. -/
def strictCut (R : SourcePartition S pins) (u v : Fin n) (a b : Fin (K + 1)) (hab : a < b) :
    SourcePartition (CutNormalization.cut S u v a b) pins :=
  (R.transport (CutNormalization.cut S u v a b) pins rfl (fun _ h => h)
    (fun x y h => (cut_upper_tightens S u v x a b).trans_lt
      (h.trans_le (cut_lower_tightens S u v y a b)))).retire u v (cut_walls_strict S u v a b hab)

theorem strictCut_removed (R : SourcePartition S pins) (u v : Fin n)
    (a b : Fin (K + 1)) (hab : a < b) : (R.strictCut u v a b hab).active u v = false := by
  simp [strictCut, retire]

theorem strictCut_active (R : SourcePartition S pins) (u v : Fin n)
    (a b : Fin (K + 1)) (hab : a < b) :
    (R.strictCut u v a b hab).active = SparseRepairGraph.eraseRow R.active u v := by
  funext x y
  by_cases ha : R.active x y = true
  · obtain ⟨hx, hy⟩ := R.active_free x y ha
    simp [strictCut, retire, transport, SparseRepairGraph.eraseRow, ha, hx, hy]
  · have hf : R.active x y = false := Bool.eq_false_iff.mpr ha
    simp [strictCut, retire, transport, SparseRepairGraph.eraseRow, hf]

def lowerWidthCut (R : SourcePartition S pins) (hne : ∃ f, S.Valid f) (u v : Fin n)
    (huv : S.edge u v = true) (hratio : 2 * width S v < width S u) :
    SourcePartition (CutNormalization.lowerWidthCut S u v) pins :=
  R.strictCut u v _ _ (floor_gap_of_width R.closed hne huv hratio).2

def upperWidthCut (R : SourcePartition S pins) (hne : ∃ f, S.Valid f) (u v : Fin n)
    (huv : S.edge u v = true) (hratio : 2 * width S u < width S v) :
    SourcePartition (CutNormalization.upperWidthCut S u v) pins :=
  R.strictCut u v _ _ (ceiling_gap_of_width R.closed hne huv hratio).1

theorem pin_lower_tightens (S : WeakSystem (Fin n) (K + 1)) (v x : Fin n) (c : Fin (K + 1)) :
    S.lower x ≤ (pinAt S v c).lower x := by
  unfold pinAt
  dsimp only
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem pin_upper_tightens (S : WeakSystem (Fin n) (K + 1)) (v x : Fin n) (c : Fin (K + 1)) :
    (pinAt S v c).upper x ≤ S.upper x := by
  unfold pinAt
  dsimp only
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- A physical pin removes all of its incident active rows. Their propagated
consequences continue to come from the unchanged source history. -/
def pin (R : SourcePartition S pins) (v : Fin n) (c : Fin (K + 1)) :
    SourcePartition (pinAt S v c) (recordPin pins v c) :=
  R.transport (pinAt S v c) (recordPin pins v c) rfl
    (fun _ hp hnew => hp (recordPin_none hnew).2)
    (fun x y h => (pin_upper_tightens S v x c).trans_lt
      (h.trans_le (pin_lower_tightens S v y c)))

theorem pin_removed (R : SourcePartition S pins) (v x : Fin n) (c : Fin (K + 1)) :
    (R.pin v c).active v x = false ∧ (R.pin v c).active x v = false := by
  exact (R.pin v c).pin_isolated (by simp) x

theorem pin_active (R : SourcePartition S pins) (v : Fin n) (c : Fin (K + 1)) :
    (R.pin v c).active = SparseRepairGraph.eraseVertex R.active v := by
  funext x y
  by_cases ha : R.active x y = true
  · obtain ⟨hx, hy⟩ := R.active_free x y ha
    by_cases hxv : x = v <;> by_cases hyv : y = v <;>
      simp [pin, transport, recordPin, SparseRepairGraph.eraseVertex, ha, hx, hy, hxv, hyv]
  · have hf : R.active x y = false := Bool.eq_false_iff.mpr ha
    simp [pin, transport, SparseRepairGraph.eraseVertex, hf]

end SourcePartition

theorem mapPins_none_iff (e : Fin (K + 1) → Fin (L + 1))
    (pins : Fin n → Option (Fin (K + 1))) (v : Fin n) :
    mapPins e pins v = none ↔ pins v = none := by
  cases h : pins v <;> simp [mapPins, h]

@[simp] theorem collapse_upperColor (c d : Fin (K + 1)) :
    Refinement.collapse c.val (upperColor c d).val = d.val :=
  Refinement.collapse_embedBefore c.val d.val

theorem collapse_split_bounds (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) (hp : PinBounds S pins)
    (c : Fin (K + 1)) (x : Fin n) :
    Refinement.collapse c.val ((splitPalette S pins c).lower x).val = (S.lower x).val ∧
      Refinement.collapse c.val ((splitPalette S pins c).upper x).val = (S.upper x).val := by
  cases hx : pins x with
  | none =>
    simp only [splitPalette, hx]
    exact ⟨Refinement.collapse_embed _ _, Refinement.collapse_embedBefore _ _⟩
  | some d =>
    simp only [splitPalette, hx, embedColor_val, Refinement.collapse_embed]
    exact ⟨congrArg Fin.val (hp x d hx).1.symm, congrArg Fin.val (hp x d hx).2.symm⟩

theorem collapse_splitBefore_bounds (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) (hp : PinBounds S pins)
    (c : Fin (K + 1)) (x : Fin n) :
    Refinement.collapse c.val ((splitPaletteBefore S pins c).lower x).val = (S.lower x).val ∧
      Refinement.collapse c.val ((splitPaletteBefore S pins c).upper x).val = (S.upper x).val := by
  cases hx : pins x with
  | none =>
    simp only [splitPaletteBefore, hx]
    exact ⟨Refinement.collapse_embed _ _, Refinement.collapse_embedBefore _ _⟩
  | some d =>
    simp only [splitPaletteBefore, hx, embedColorBefore_val, Refinement.collapse_embedBefore]
    exact ⟨congrArg Fin.val (hp x d hx).1.symm, congrArg Fin.val (hp x d hx).2.symm⟩

namespace SourcePartition

variable {S : WeakSystem (Fin n) (K + 1)} {pins : Fin n → Option (Fin (K + 1))}

/-- The above-endpoint split preserves the retired primitive walls exactly
through their inverse-image endpoints. Derived numerical lists are recomputed. -/
def split (R : SourcePartition S pins) (hp : PinBounds S pins) (c : Fin (K + 1)) :
    SourcePartition (splitPalette S pins c) (mapPins (embedColor c) pins) :=
  R.transport _ _ rfl
    (fun x h hnew => h ((mapPins_none_iff _ _ x).mp hnew))
    (fun u v h => Refinement.strict_walls_survive h
      (collapse_split_bounds S pins hp c u).2.le (collapse_split_bounds S pins hp c v).1.ge)

/-- The below-endpoint split has the same artificial-wall inverse images;
only the immutable physical-pin embedding differs. -/
def splitBefore (R : SourcePartition S pins) (hp : PinBounds S pins) (c : Fin (K + 1)) :
    SourcePartition (splitPaletteBefore S pins c) (mapPins (embedColorBefore c) pins) :=
  R.transport _ _ rfl
    (fun x h hnew => h ((mapPins_none_iff _ _ x).mp hnew))
    (fun u v h => Refinement.strict_walls_survive h
      (collapse_splitBefore_bounds S pins hp c u).2.le
      (collapse_splitBefore_bounds S pins hp c v).1.ge)

def lowerRepair (R : SourcePartition S pins) (hp : PinBounds S pins)
    (v : Fin n) (c : Fin (K + 1)) :
    SourcePartition (lowerRefinement S pins v c)
      (recordPin (mapPins (embedColor c) pins) v (freshColor c)) :=
  (R.split hp c).pin v (freshColor c)

def upperRepair (R : SourcePartition S pins) (hp : PinBounds S pins)
    (v : Fin n) (c : Fin (K + 1)) :
    SourcePartition (upperRefinement S pins v c)
      (recordPin (mapPins (embedColorBefore c) pins) v c.castSucc) :=
  (R.splitBefore hp c).pin v c.castSucc

def ResultPartition {v : Fin n} {c : Fin (K + 1)} (r : Promotion.Result S pins v c) : Type :=
  SourcePartition r.system r.newPins

/-- The existing executable promotion, in all three colour cases, carries
the persistent source-row partition automatically. -/
def promote (R : SourcePartition S pins) (h : Invariant S pins) (hp : PinBounds S pins)
    (v : Fin n) (hv : pins v = none) (c : Fin (K + 1))
    (hc : S.effectiveLower v ≤ c ∧ c ≤ S.effectiveUpper v) :
    ResultPartition (Promotion.promote S pins h hp v hv c hc) := by
  unfold Promotion.promote
  split
  · exact R.lowerRepair hp v c
  · split
    · exact R.upperRepair hp v c
    · exact R.pin v c

theorem split_active (R : SourcePartition S pins) (hp : PinBounds S pins) (c : Fin (K + 1)) :
    (R.split hp c).active = R.active := by
  funext u v
  by_cases ha : R.active u v = true
  · obtain ⟨hu, hv⟩ := R.active_free u v ha
    simp [split, transport, mapPins, ha, hu, hv]
  · have hf : R.active u v = false := Bool.eq_false_iff.mpr ha
    simp [split, transport, hf]

theorem splitBefore_active (R : SourcePartition S pins) (hp : PinBounds S pins) (c : Fin (K + 1)) :
    (R.splitBefore hp c).active = R.active := by
  funext u v
  by_cases ha : R.active u v = true
  · obtain ⟨hu, hv⟩ := R.active_free u v ha
    simp [splitBefore, transport, mapPins, ha, hu, hv]
  · have hf : R.active u v = false := Bool.eq_false_iff.mpr ha
    simp [splitBefore, transport, hf]

/-- The single-new-row public closure formula equals closing the actual
augmented source history, including all previously retired rows. -/
theorem public_add_closure (R : SourcePartition S pins) (a b : Fin n) :
    (Safety.closedAdd S a b).edge = closure (SparseRepairGraph.addRow R.source a b) := by
  let E := SparseRepairGraph.addRow R.source a b
  have hOld : ∀ x y, S.edge x y = true → closure E x y = true := by
    intro x y hxy
    rw [R.public_eq] at hxy
    apply closure_subset_closed R.source (closure E) (closure_refl E) (closure_trans E)
      (fun u v huv => closure_old E (by simp [E, SparseRepairGraph.addRow, huv])) x y hxy
  have hNew : closure E a b = true := closure_old E (by simp [E, SparseRepairGraph.addRow])
  funext x y
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hxy
    rcases (Safety.closedAdd_edge S a b x y).mp hxy with hxy | ⟨hxa, hby⟩
    · exact hOld x y hxy
    · exact closure_trans E x b y (closure_trans E x a b (hOld x a hxa) hNew) (hOld b y hby)
  · apply closure_subset_closed E (Safety.closedAdd S a b).edge
      (Safety.closedAdd_closed S R.closed a b).refl (Safety.closedAdd_closed S R.closed a b).trans
    intro u v huv
    rcases (SparseRepairGraph.addRow_true R.source a b u v).mp huv with huv | ⟨hua, hvb⟩
    · exact (Safety.closedAdd_edge S a b u v).mpr (Or.inl (R.source_public huv))
    · subst u
      subst v
      exact (Safety.closedAdd_edge S a b a b).mpr (Or.inr ⟨R.closed.refl a, R.closed.refl b⟩)

/-- Record a new physical comparison. Its numerical row is added precisely
when both endpoints are free; delegated pin comparisons stay out of the graph. -/
def add (R : SourcePartition S pins) (a b : Fin n) (hab : a ≠ b) :
    SourcePartition (Safety.closedAdd S a b) pins where
  source := SparseRepairGraph.addRow R.source a b
  active x y := R.active x y || decide (x = a ∧ y = b ∧ pins a = none ∧ pins b = none)
  proper := by
    intro x y hxy
    rcases (SparseRepairGraph.addRow_true R.source a b x y).mp hxy with hxy | ⟨hxa, hyb⟩
    · exact R.proper x y hxy
    · simpa only [hxa, hyb] using hab
  public_eq := R.public_add_closure a b
  active_source := by
    intro x y hxy
    have hh : R.active x y = true ∨ (x = a ∧ y = b ∧ pins a = none ∧ pins b = none) := by
      simpa using hxy
    apply (SparseRepairGraph.addRow_true R.source a b x y).mpr
    exact hh.elim (fun h => Or.inl (R.active_source x y h)) (fun h => Or.inr ⟨h.1, h.2.1⟩)
  active_free := by
    intro x y hxy
    have hh : R.active x y = true ∨ (x = a ∧ y = b ∧ pins a = none ∧ pins b = none) := by
      simpa using hxy
    rcases hh with hh | ⟨hxa, hyb, ha, hb⟩
    · exact R.active_free x y hh
    · simpa only [hxa, hyb] using And.intro ha hb
  covered := by
    intro x y hxy
    rcases (SparseRepairGraph.addRow_true R.source a b x y).mp hxy with hxy | ⟨hxa, hyb⟩
    · rcases R.covered x y hxy with ha | hu | hv | hw
      · exact Or.inl (by simp [ha])
      · exact Or.inr (Or.inl hu)
      · exact Or.inr (Or.inr (Or.inl hv))
      · exact Or.inr (Or.inr (Or.inr hw))
    · subst x
      subst y
      by_cases ha : pins a = none
      · by_cases hb : pins b = none
        · exact Or.inl (by simp [ha, hb])
        · exact Or.inr (Or.inr (Or.inl hb))
      · exact Or.inr (Or.inl ha)

theorem add_active_free (R : SourcePartition S pins) (a b : Fin n) (hab : a ≠ b)
    (ha : pins a = none) (hb : pins b = none) :
    (R.add a b hab).active = SparseRepairGraph.addRow R.active a b := by
  funext x y
  simp [add, SparseRepairGraph.addRow, ha, hb]

theorem add_active_pinned_left (R : SourcePartition S pins) (a b : Fin n) (hab : a ≠ b)
    (ha : pins a ≠ none) : (R.add a b hab).active = R.active := by
  funext x y
  simp [add, ha]

theorem add_active_pinned_right (R : SourcePartition S pins) (a b : Fin n) (hab : a ≠ b)
    (hb : pins b ≠ none) : (R.add a b hab).active = R.active := by
  funext x y
  simp [add, hb]

/-- A same-colour delegated comparison changes the public closure but
preserves the entire parent weak-map family and hence its numerical count. -/
theorem delegated_valid (R : SourcePartition S pins) (hp : PinBounds S pins)
    (a b : Fin n) (c : Fin (K + 1)) (ha : pins a = some c) (hb : pins b = some c)
    (f : ColorMap (Fin n) (K + 1)) : (Safety.closedAdd S a b).Valid f ↔ S.Valid f := by
  rw [Safety.closedAdd_valid S R.closed]
  constructor
  · exact And.left
  · intro hf
    exact ⟨hf, by rw [valid_pin_value S pins hp hf ha, valid_pin_value S pins hp hf hb]⟩

theorem delegated_view_count (R : SourcePartition S pins) (hp : PinBounds S pins)
    (a b : Fin n) (hab : a ≠ b) (c : Fin (K + 1)) (ha : pins a = some c) (hb : pins b = some c) :
    (R.add a b hab).view.count = R.view.count := by
  rw [(R.add a b hab).view_count hp, R.view_count hp]
  have hm : (Safety.closedAdd S a b).maps = S.maps := by
    ext f
    simp only [mem_maps, R.delegated_valid hp a b c ha hb f]
  exact congrArg Finset.card hm

/-- Appending a new top colour preserves every strict primitive-wall gap. -/
def append (R : SourcePartition S pins) :
    SourcePartition S.enlarge (mapPins Fin.castSucc pins) :=
  R.transport _ _ rfl (fun x h hnew => h ((mapPins_none_iff _ _ x).mp hnew))
    (fun _ _ h => h)

theorem source_avoids_unused (R : SourcePartition S pins) {v : Fin n} {d : Fin (K + 1)}
    (hu : FreshAdmission.Unused S v d) {x y : Fin n} (hxy : R.source x y = true) :
    x ≠ v ∧ y ≠ v := by
  have hne := R.proper x y hxy
  have hpublic := R.source_public hxy
  constructor
  · intro hx
    subst x
    exact hne (hu.outgoing y hpublic).symm
  · intro hy
    subst y
    exact hne (hu.incoming x hpublic)

/-- A fresh child admission changes only an unused isolated coordinate, so
no historical source row can lose a pin-incident or strict-wall justification. -/
def admit (R : SourcePartition S pins) (v : Fin n) (d : Fin (K + 1))
    (hu : FreshAdmission.Unused S v d) :
    SourcePartition (FreshAdmission.admit S v) (FreshAdmission.unpin pins v) where
  source := R.source
  active := R.active
  proper := R.proper
  public_eq := R.public_eq
  active_source := R.active_source
  active_free := by
    intro x y hxy
    obtain ⟨hx, hy⟩ := R.source_avoids_unused hu (R.active_source x y hxy)
    simpa [FreshAdmission.unpin, hx, hy] using R.active_free x y hxy
  covered := by
    intro x y hxy
    obtain ⟨hx, hy⟩ := R.source_avoids_unused hu hxy
    rcases R.covered x y hxy with ha | hp | hp | hw
    · exact Or.inl ha
    · exact Or.inr (Or.inl (by simpa [FreshAdmission.unpin, hx] using hp))
    · exact Or.inr (Or.inr (Or.inl (by simpa [FreshAdmission.unpin, hy] using hp)))
    · exact Or.inr (Or.inr (Or.inr (by simpa [FreshAdmission.admit, hx, hy] using hw)))

theorem admit_view_count (R : SourcePartition S pins) (hp : PinBounds S pins)
    (v : Fin n) (d : Fin (K + 1)) (hu : FreshAdmission.Unused S v d) :
    (R.admit v d hu).view.count = R.view.count * (K + 1) := by
  rw [(R.admit v d hu).view_count (FreshAdmission.admission_pin_bounds hp v), R.view_count hp]
  exact FreshAdmission.admission_count hu

end SourcePartition

end SortingAdversary.Optimal.NumericalRepresentation
