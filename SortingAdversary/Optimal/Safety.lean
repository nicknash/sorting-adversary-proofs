import SortingAdversary.Optimal.WeakMaps
import SortingAdversary.Optimal.Routing

/-!
# The singleton safety test

Adding one comparison to a closed public order has an explicit effect on all
effective windows.  These formulas prove the second safety test in section 2
of the manuscript: if a feasible answer newly forces a formerly nonconstant
coordinate, the opposite answer retains every old map and has a strict witness.

In particular, this is a theorem about the finite weak-map semantics; the
all-retaining conclusion is not an assumption supplied by the controller.
-/

namespace SortingAdversary.Optimal.Safety

open WeakMaps WeakMaps.WeakSystem

variable {α : Type*} [Fintype α] {K : ℕ}

/-- Close a new row using the explicit single-new-edge path formula. -/
def closedAdd (S : WeakSystem α (K + 1)) (a b : α) : WeakSystem α (K + 1) where
  edge u v := S.edge u v || (S.edge u a && S.edge b v)
  lower := S.lower
  upper := S.upper

omit [Fintype α] in
@[simp] theorem closedAdd_edge (S : WeakSystem α (K + 1)) (a b u v : α) :
    (closedAdd S a b).edge u v = true ↔
      S.edge u v = true ∨ (S.edge u a = true ∧ S.edge b v = true) := by
  simp [closedAdd]

omit [Fintype α] in
theorem closedAdd_closed (S : WeakSystem α (K + 1)) (hS : S.Closed) (a b : α) :
    (closedAdd S a b).Closed := by
  constructor
  · intro v
    exact (closedAdd_edge S a b v v).mpr (Or.inl (hS.refl v))
  · intro u v w huv hvw
    apply (closedAdd_edge S a b u w).mpr
    exact Routing.adjoin_transitive (fun {x y z} hxy hyz => hS.trans x y z hxy hyz)
      a b ((closedAdd_edge S a b u v).mp huv) ((closedAdd_edge S a b v w).mp hvw)

omit [Fintype α] in
@[simp] theorem closedAdd_valid (S : WeakSystem α (K + 1)) (hS : S.Closed)
    (a b : α) (f : ColorMap α (K + 1)) :
    (closedAdd S a b).Valid f ↔ S.Valid f ∧ f a ≤ f b := by
  constructor
  · rintro ⟨hl, hr⟩
    refine ⟨⟨hl, fun u v huv => hr u v ((closedAdd_edge S a b u v).mpr
      (Or.inl huv))⟩, ?_⟩
    exact hr a b ((closedAdd_edge S a b a b).mpr (Or.inr ⟨hS.refl a, hS.refl b⟩))
  · rintro ⟨⟨hl, hr⟩, hab⟩
    refine ⟨hl, ?_⟩
    intro u v huv
    rcases (closedAdd_edge S a b u v).mp huv with huv | ⟨hua, hbv⟩
    · exact hr u v huv
    · exact (hr u a hua).trans (hab.trans (hr b v hbv))

theorem lower_mono_rows {S T : WeakSystem α (K + 1)}
    (hl : S.lower = T.lower)
    (hr : ∀ u v, S.edge u v = true → T.edge u v = true) (v : α) :
    S.effectiveLower v ≤ T.effectiveLower v := by
  apply Finset.sup_le
  intro u _
  split_ifs with huv
  · rw [hl]
    exact T.lower_le_effectiveLower (hr u v huv)
  · exact bot_le

theorem upper_antitone_rows {S T : WeakSystem α (K + 1)}
    (hu : S.upper = T.upper)
    (hr : ∀ u v, S.edge u v = true → T.edge u v = true) (v : α) :
    T.effectiveUpper v ≤ S.effectiveUpper v := by
  apply Finset.le_inf
  intro u _
  split_ifs with hvu
  · rw [hu]
    exact T.effectiveUpper_le_upper (hr v u hvu)
  · exact le_top

/-- A new lower bound travels exactly to the old successors of `b`. -/
theorem closedAdd_lower (S : WeakSystem α (K + 1)) (a b v : α) :
    (closedAdd S a b).effectiveLower v =
      if S.edge b v = true then max (S.effectiveLower v) (S.effectiveLower a)
      else S.effectiveLower v := by
  by_cases hbv : S.edge b v = true
  · rw [if_pos hbv]
    apply le_antisymm
    · apply Finset.sup_le
      intro u _
      split_ifs with huv
      · rcases (closedAdd_edge S a b u v).mp huv with hold | ⟨hua, _⟩
        · exact (S.lower_le_effectiveLower hold).trans (le_max_left _ _)
        · exact (S.lower_le_effectiveLower hua).trans (le_max_right _ _)
      · exact bot_le
    · apply max_le
      · exact lower_mono_rows (S := S) (T := closedAdd S a b) rfl
          (fun u w huw => (closedAdd_edge S a b u w).mpr (Or.inl huw)) v
      · apply Finset.sup_le
        intro u _
        split_ifs with hua
        · exact (closedAdd S a b).lower_le_effectiveLower
            ((closedAdd_edge S a b u v).mpr (Or.inr ⟨hua, hbv⟩))
        · exact bot_le
  · rw [if_neg hbv]
    have hbv' : S.edge b v = false := by simpa using hbv
    simp [effectiveLower, closedAdd, hbv']

/-- The dual formula: a new upper bound travels to old predecessors of `a`. -/
theorem closedAdd_upper (S : WeakSystem α (K + 1)) (a b v : α) :
    (closedAdd S a b).effectiveUpper v =
      if S.edge v a = true then min (S.effectiveUpper v) (S.effectiveUpper b)
      else S.effectiveUpper v := by
  by_cases hva : S.edge v a = true
  · rw [if_pos hva]
    apply le_antisymm
    · apply le_min
      · exact upper_antitone_rows (S := S) (T := closedAdd S a b) rfl
          (fun u w huw => (closedAdd_edge S a b u w).mpr (Or.inl huw)) v
      · apply Finset.le_inf
        intro u _
        split_ifs with hbu
        · exact (closedAdd S a b).effectiveUpper_le_upper
            ((closedAdd_edge S a b v u).mpr (Or.inr ⟨hva, hbu⟩))
        · exact le_top
    · apply Finset.le_inf
      intro u _
      split_ifs with hvu
      · rcases (closedAdd_edge S a b v u).mp hvu with hold | ⟨_, hbu⟩
        · exact (min_le_left _ _).trans (S.effectiveUpper_le_upper hold)
        · exact (min_le_right _ _).trans (S.effectiveUpper_le_upper hbu)
      · exact le_top
  · rw [if_neg hva]
    have hva' : S.edge v a = false := by simpa using hva
    simp [effectiveUpper, closedAdd, hva']

/-- Constancy of a feasible coordinate is equivalent to equal window ends. -/
theorem constant_iff_equal_windows (S : WeakSystem α (K + 1)) (hS : S.Closed)
    (hne : ∃ f, S.Valid f) (v : α) :
    (∃ c, ∀ f, S.Valid f → f v = c) ↔ S.effectiveLower v = S.effectiveUpper v := by
  have hw := (S.feasible_iff_windows hS).mp hne
  constructor
  · rintro ⟨c, hc⟩
    exact (hc _ (S.effectiveLower_valid hS hw)).trans
      (hc _ (S.effectiveUpper_valid hS hw)).symm
  · intro heq
    refine ⟨S.effectiveLower v, ?_⟩
    intro f hf
    obtain ⟨hl, hu⟩ := S.valid_between_windows f hf v
    rw [← heq] at hu
    exact le_antisymm hu hl

/-- The missing singleton-safety implication. Its strict witness is one of
the two concrete old endpoint maps. -/
theorem new_singleton_reverse (S : WeakSystem α (K + 1)) (hS : S.Closed)
    {a b w : α} (hba : S.edge b a ≠ true)
    (hne : ∃ f, S.Valid f)
    (hfree : S.effectiveLower w < S.effectiveUpper w)
    (hnew : (closedAdd S a b).effectiveLower w =
      (closedAdd S a b).effectiveUpper w) :
    (∀ f, S.Valid f → f b ≤ f a) ∧
      ∃ f, S.Valid f ∧ f b < f a := by
  have hw := (S.feasible_iff_windows hS).mp hne
  rw [closedAdd_lower, closedAdd_upper] at hnew
  by_cases hbw : S.edge b w = true
  · have hwa : S.edge w a ≠ true := fun h => hba (hS.trans b w a hbw h)
    rw [if_pos hbw, if_neg hwa] at hnew
    have hla : S.effectiveLower a = S.effectiveUpper w := by
      have hx := le_max_right (S.effectiveLower w) (S.effectiveLower a)
      rw [hnew] at hx
      apply le_antisymm hx
      by_contra hn
      have hh : max (S.effectiveLower w) (S.effectiveLower a) < S.effectiveUpper w :=
        max_lt hfree (lt_of_not_ge hn)
      rw [hnew] at hh
      exact lt_irrefl _ hh
    constructor
    · intro f hf
      calc
        f b ≤ f w := hf.2 b w hbw
        _ ≤ S.effectiveUpper w := (S.valid_between_windows f hf w).2
        _ = S.effectiveLower a := hla.symm
        _ ≤ f a := (S.valid_between_windows f hf a).1
    · refine ⟨S.effectiveLower, S.effectiveLower_valid hS hw, ?_⟩
      calc
        S.effectiveLower b ≤ S.effectiveLower w := S.effectiveLower_mono hS hbw
        _ < S.effectiveUpper w := hfree
        _ = S.effectiveLower a := hla.symm
  · rw [if_neg hbw] at hnew
    by_cases hwa : S.edge w a = true
    · rw [if_pos hwa] at hnew
      have hub : S.effectiveUpper b = S.effectiveLower w := by
        have hx := min_le_right (S.effectiveUpper w) (S.effectiveUpper b)
        rw [← hnew] at hx
        apply le_antisymm ?_ hx
        by_contra hn
        have hh : S.effectiveLower w < min (S.effectiveUpper w) (S.effectiveUpper b) :=
          lt_min hfree (lt_of_not_ge hn)
        rw [← hnew] at hh
        exact lt_irrefl _ hh
      constructor
      · intro f hf
        calc
          f b ≤ S.effectiveUpper b := (S.valid_between_windows f hf b).2
          _ = S.effectiveLower w := hub
          _ ≤ f w := (S.valid_between_windows f hf w).1
          _ ≤ f a := hf.2 w a hwa
      · refine ⟨S.effectiveUpper, S.effectiveUpper_valid hS hw, ?_⟩
        calc
          S.effectiveUpper b = S.effectiveLower w := hub
          _ < S.effectiveUpper w := hfree
          _ ≤ S.effectiveUpper a := S.effectiveUpper_mono hS hwa
    · rw [if_neg hwa] at hnew
      exact (ne_of_lt hfree hnew).elim

/-- A semantic singleton detected after a feasible branch has the same
all-retaining reverse and strict witness. -/
theorem forced_singleton_reverse (S : WeakSystem α (K + 1)) (hS : S.Closed)
    {a b w : α} (hba : S.edge b a ≠ true)
    (hne : ∃ f, S.Valid f)
    (hfree : S.effectiveLower w < S.effectiveUpper w)
    (hbranch : ∃ f, (closedAdd S a b).Valid f)
    (hconstant : ∃ c, ∀ f, (closedAdd S a b).Valid f → f w = c) :
    (∀ f, S.Valid f → f b ≤ f a) ∧ ∃ f, S.Valid f ∧ f b < f a := by
  apply new_singleton_reverse S hS hba hne hfree
  exact (constant_iff_equal_windows _ (closedAdd_closed S hS a b) hbranch w).mp hconstant

/-- The all-retaining reverse also preserves every effective window. -/
theorem retained_windows (S : WeakSystem α (K + 1)) (hS : S.Closed)
    (hne : ∃ f, S.Valid f) {a b : α}
    (hretain : ∀ f, S.Valid f → f a ≤ f b) (v : α) :
    (closedAdd S a b).effectiveLower v = S.effectiveLower v ∧
      (closedAdd S a b).effectiveUpper v = S.effectiveUpper v := by
  have hw := (S.feasible_iff_windows hS).mp hne
  have hlow := S.effectiveLower_valid hS hw
  have hupp := S.effectiveUpper_valid hS hw
  have hlow' : (closedAdd S a b).Valid S.effectiveLower :=
    (closedAdd_valid S hS a b _).mpr ⟨hlow, hretain _ hlow⟩
  have hupp' : (closedAdd S a b).Valid S.effectiveUpper :=
    (closedAdd_valid S hS a b _).mpr ⟨hupp, hretain _ hupp⟩
  constructor
  · exact le_antisymm ((closedAdd S a b).valid_between_windows _ hlow' v).1
      (lower_mono_rows (S := S) (T := closedAdd S a b) rfl (fun u w huw =>
        (closedAdd_edge S a b u w).mpr (Or.inl huw)) v)
  · exact le_antisymm
      (upper_antitone_rows (S := S) (T := closedAdd S a b) rfl (fun u w huw =>
        (closedAdd_edge S a b u w).mpr (Or.inl huw)) v)
      ((closedAdd S a b).valid_between_windows _ hupp' v).2

end SortingAdversary.Optimal.Safety
