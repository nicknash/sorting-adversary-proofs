import SortingAdversary.Optimal.WeakMaps
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Conditional refreshes of the actual weak-map law

This module constructs the conditional inclusive interval, proves that uniform
refresh on it preserves the uniform weak-map law, and proves the deterministic
common-clock discrepancy estimates.  The clocks are auxiliary proof objects;
the adversary evaluates local counts deterministically.
-/

namespace SortingAdversary.Optimal.LocalCoupling

open WeakMaps
open scoped BigOperators

/-- The manuscript's integer inverse CDF, with a rational common clock. -/
def quantile (a b : ℤ) (u : ℚ) : ℤ :=
  ⌊(1 - u) * a + u * b + u⌋

/-- An inclusive integer interval is sampled inside its endpoints. -/
theorem quantile_mem {a b : ℤ} {u : ℚ} (hab : a ≤ b)
    (hu0 : 0 ≤ u) (hu1 : u < 1) : a ≤ quantile a b u ∧ quantile a b u ≤ b := by
  have hab' : (a : ℚ) ≤ b := by exact_mod_cast hab
  constructor
  · apply Int.le_floor.mpr
    nlinarith
  · apply Int.floor_le_iff.mpr
    nlinarith

/-- Rounding costs at most one unit in a shared quantile refresh. -/
theorem quantile_discrepancy {a b c d : ℤ} {u : ℚ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |(quantile a b u : ℚ) - quantile c d u| ≤
      1 + (1 - u) * |(a : ℚ) - c| + u * |(b : ℚ) - d| := by
  have hfloor1 := Int.floor_le ((1 - u) * (a : ℚ) + u * b + u)
  have hfloor2 := Int.floor_le ((1 - u) * (c : ℚ) + u * d + u)
  have hlt1 := Int.lt_floor_add_one ((1 - u) * (a : ℚ) + u * b + u)
  have hlt2 := Int.lt_floor_add_one ((1 - u) * (c : ℚ) + u * d + u)
  have ha := (abs_le.mp (le_refl |(a : ℚ) - c|))
  have hb := (abs_le.mp (le_refl |(b : ℚ) - d|))
  unfold quantile
  apply abs_le.mpr
  constructor <;> nlinarith

/-- On a grid whose size is a multiple of the interval length, each output
colour occupies exactly one equal-sized block of clocks. -/
theorem quantile_grid_block (a : ℤ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (i : Fin n) (j : Fin m) :
    quantile a (a + n - 1) (((j.val : ℚ) + m * i.val) / (n * m)) = a + i.val := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hj0 : (0 : ℚ) ≤ j.val / (m : ℚ) := div_nonneg (Nat.cast_nonneg _) hm'.le
  have hj1 : (j.val : ℚ) / m < 1 := (div_lt_one hm').mpr (by exact_mod_cast j.isLt)
  have hexpr :
      (1 - ((j.val : ℚ) + m * i.val) / (n * m)) * a +
        (((j.val : ℚ) + m * i.val) / (n * m)) * (a + n - 1) +
        (((j.val : ℚ) + m * i.val) / (n * m)) = a + i.val + j.val / (m : ℚ) := by
    field_simp
    ring
  unfold quantile
  apply Int.floor_eq_iff.mpr
  push_cast
  rw [hexpr]
  constructor <;> linarith

/-- Exact finite-clock uniformity, without a limiting argument or continuous
probability. The integer `m` is the number of clock seeds per output colour. -/
theorem quantile_grid_sum (a : ℤ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (φ : ℤ → ℚ) :
    (∑ r : Fin (n * m), φ (quantile a (a + n - 1) ((r.val : ℚ) / (n * m)))) =
      m * ∑ i : Fin n, φ (a + i.val) := by
  calc
    _ = ∑ p : Fin n × Fin m,
        φ (quantile a (a + n - 1)
          (((finProdFinEquiv p).val : ℚ) / (n * m))) := by
      exact (Fintype.sum_equiv finProdFinEquiv _ _ (fun _ => rfl)).symm
    _ = ∑ i : Fin n, ∑ _j : Fin m, φ (a + i.val) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change φ (quantile a (a + n - 1) (((j.val + m * i.val : ℕ) : ℚ) / (n * m))) = _
      push_cast
      rw [quantile_grid_block a hn hm i j]
    _ = _ := by simp [← Finset.mul_sum]

/-- Normalised version: every admissible clock multiple gives exactly the
uniform distribution on the inclusive interval. A common factorial multiple
can therefore be used simultaneously for every interval in a palette. -/
theorem quantile_grid_uniform (a : ℤ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (φ : ℤ → ℚ) :
    (∑ r : Fin (n * m), φ (quantile a (a + n - 1) ((r.val : ℚ) / (n * m)))) /
      (n * m) = (∑ i : Fin n, φ (a + i.val)) / n := by
  rw [quantile_grid_sum a hn hm φ]
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

/-- The same rational clock grid can be used by every updated coordinate. -/
def gridClock {Q : ℕ} (r : Fin Q) : ℚ := (r.val : ℚ) / Q

theorem gridClock_mem {Q : ℕ} (r : Fin Q) : 0 ≤ gridClock r ∧ gridClock r < 1 := by
  have hQ : (0 : ℚ) < Q := by exact_mod_cast Nat.zero_lt_of_lt r.isLt
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hQ.le
  · exact (div_lt_one hQ).mpr (by exact_mod_cast r.isLt)

section Finite

variable {α : Type*} [Fintype α] [DecidableEq α] {K : ℕ}

/-- All immediate predecessors other than the refreshed coordinate contribute
to its conditional lower wall. Reflexive raw rows impose no extra condition. -/
def conditionalLower (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) : Fin (K + 1) :=
  max (S.lower v) (Finset.univ.sup fun x =>
    if x ≠ v ∧ S.edge x v = true then f x else ⊥)

/-- The corresponding inclusive upper wall. -/
def conditionalUpper (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) : Fin (K + 1) :=
  min (S.upper v) (Finset.univ.inf fun x =>
    if x ≠ v ∧ S.edge v x = true then f x else ⊤)

theorem conditionalLower_le_iff (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (c : Fin (K + 1)) :
    conditionalLower S v f ≤ c ↔
      S.lower v ≤ c ∧ ∀ x, x ≠ v → S.edge x v = true → f x ≤ c := by
  simp only [conditionalLower, max_le_iff, Finset.sup_le_iff, Finset.mem_univ, true_implies]
  apply and_congr Iff.rfl
  constructor
  · intro h x hx he
    simpa [hx, he] using h x
  · intro h x
    split_ifs with hx
    · exact h x hx.1 hx.2
    · exact bot_le

theorem le_conditionalUpper_iff (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (c : Fin (K + 1)) :
    c ≤ conditionalUpper S v f ↔
      c ≤ S.upper v ∧ ∀ x, x ≠ v → S.edge v x = true → c ≤ f x := by
  simp only [conditionalUpper, le_min_iff, Finset.le_inf_iff, Finset.mem_univ, true_implies]
  apply and_congr Iff.rfl
  constructor
  · intro h x hx he
    simpa [hx, he] using h x
  · intro h x
    split_ifs with hx
    · exact h x hx.1 hx.2
    · exact le_top

/-- Conditional refreshes use precisely the feasible inclusive interval,
with every other coordinate held fixed. -/
theorem valid_update_iff (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (hf : S.Valid f) (c : Fin (K + 1)) :
    S.Valid (Function.update f v c) ↔
      conditionalLower S v f ≤ c ∧ c ≤ conditionalUpper S v f := by
  rw [conditionalLower_le_iff, le_conditionalUpper_iff]
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simpa using (h.1 v).1
    · intro x hx he
      simpa [Function.update_of_ne hx] using h.2 x v he
    · simpa using (h.1 v).2
    · intro x hx he
      simpa [Function.update_of_ne hx] using h.2 v x he
  · rintro ⟨⟨hlo, hpred⟩, ⟨hhi, hsucc⟩⟩
    constructor
    · intro x
      by_cases hx : x = v
      · subst x; simpa using And.intro hlo hhi
      · simpa [Function.update_of_ne hx] using hf.1 x
    · intro x y he
      by_cases hx : x = v <;> by_cases hy : y = v
      · subst x; subst y; exact le_refl _
      · subst x; simpa [Function.update_of_ne hy] using hsucc y hy he
      · subst y; simpa [Function.update_of_ne hx] using hpred x hx he
      · simpa [Function.update_of_ne hx, Function.update_of_ne hy] using hf.2 x y he

/-- The currently occupied colour proves that its conditional interval is
nonempty. This requires no strictness or transitive closure of the raw graph. -/
theorem current_mem_conditional (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (hf : S.Valid f) :
    conditionalLower S v f ≤ f v ∧ f v ≤ conditionalUpper S v f := by
  apply (valid_update_iff S v f hf (f v)).mp
  simpa using hf

/-- A conditional lower wall is either the permanent floor or the colour
of an immediate predecessor. -/
theorem conditionalLower_attained (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) :
    conditionalLower S v f = S.lower v ∨
      ∃ x, x ≠ v ∧ S.edge x v = true ∧ conditionalLower S v f = f x := by
  rcases max_choice (S.lower v) (Finset.univ.sup fun x =>
      if x ≠ v ∧ S.edge x v = true then f x else ⊥) with h | h
  · exact Or.inl h
  · obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨v⟩)
      (fun x => if x ≠ v ∧ S.edge x v = true then f x else (⊥ : Fin (K + 1)))
    by_cases hp : x ≠ v ∧ S.edge x v = true
    · exact Or.inr ⟨x, hp.1, hp.2, h.trans (by simpa [hp] using hx)⟩
    · left
      have hb : conditionalLower S v f = ⊥ := h.trans (by simpa [hp] using hx)
      have hlo : S.lower v ≤ conditionalLower S v f := le_max_left _ _
      exact le_antisymm (hb ▸ bot_le) hlo

/-- Dually, a conditional upper wall is the permanent ceiling or a successor. -/
theorem conditionalUpper_attained (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) :
    conditionalUpper S v f = S.upper v ∨
      ∃ x, x ≠ v ∧ S.edge v x = true ∧ conditionalUpper S v f = f x := by
  rcases min_choice (S.upper v) (Finset.univ.inf fun x =>
      if x ≠ v ∧ S.edge v x = true then f x else ⊤) with h | h
  · exact Or.inl h
  · obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_inf Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨v⟩)
      (fun x => if x ≠ v ∧ S.edge v x = true then f x else (⊤ : Fin (K + 1)))
    by_cases hp : x ≠ v ∧ S.edge v x = true
    · exact Or.inr ⟨x, hp.1, hp.2, h.trans (by simpa [hp] using hx)⟩
    · left
      have ht : conditionalUpper S v f = ⊤ := h.trans (by simpa [hp] using hx)
      have hhi : conditionalUpper S v f ≤ S.upper v := min_le_left _ _
      exact le_antisymm hhi (ht ▸ le_top)

private theorem lower_le_add (S : WeakSystem α (K + 1)) (v : α)
    (f g : ColorMap α (K + 1)) (D : ℚ) (hD : 0 ≤ D)
    (hfg : ∀ x, x ≠ v → S.edge x v = true → (f x).val ≤ (g x).val + D) :
    ((conditionalLower S v f).val : ℚ) ≤ (conditionalLower S v g).val + D := by
  rcases conditionalLower_attained S v f with h | ⟨x, hx, he, h⟩
  · rw [h]
    have hbound : ((S.lower v).val : ℚ) ≤ (conditionalLower S v g).val := by
      exact_mod_cast (le_max_left (S.lower v) _)
    linarith
  · rw [h]
    have hbound : ((g x).val : ℚ) ≤ (conditionalLower S v g).val := by
      exact_mod_cast ((conditionalLower_le_iff S v g _).mp le_rfl).2 x hx he
    linarith [hfg x hx he]

private theorem upper_le_add (S : WeakSystem α (K + 1)) (v : α)
    (f g : ColorMap α (K + 1)) (D : ℚ) (hD : 0 ≤ D)
    (hfg : ∀ x, x ≠ v → S.edge v x = true → (f x).val ≤ (g x).val + D) :
    ((conditionalUpper S v f).val : ℚ) ≤ (conditionalUpper S v g).val + D := by
  rcases conditionalUpper_attained S v g with h | ⟨x, hx, he, h⟩
  · rw [h]
    have hbound : ((conditionalUpper S v f).val : ℚ) ≤ (S.upper v).val := by
      exact_mod_cast (min_le_left (S.upper v) _)
    linarith
  · rw [h]
    have hbound : ((conditionalUpper S v f).val : ℚ) ≤ (f x).val := by
      exact_mod_cast ((le_conditionalUpper_iff S v f _).mp le_rfl).2 x hx he
    linarith [hfg x hx he]

/-- Maxima with the same floor cannot amplify predecessor discrepancies. -/
theorem conditionalLower_discrepancy (S : WeakSystem α (K + 1)) (v : α)
    (f g : ColorMap α (K + 1)) (D : ℚ) (hD : 0 ≤ D)
    (hfg : ∀ x, x ≠ v → S.edge x v = true → |((f x).val : ℚ) - (g x).val| ≤ D) :
    |((conditionalLower S v f).val : ℚ) - (conditionalLower S v g).val| ≤ D := by
  have h1 := lower_le_add S v f g D hD (fun x hx he => by
    linarith [(abs_le.mp (hfg x hx he)).2])
  have h2 := lower_le_add S v g f D hD (fun x hx he => by
    linarith [(abs_le.mp (hfg x hx he)).1])
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Minima with the same ceiling cannot amplify successor discrepancies. -/
theorem conditionalUpper_discrepancy (S : WeakSystem α (K + 1)) (v : α)
    (f g : ColorMap α (K + 1)) (D : ℚ) (hD : 0 ≤ D)
    (hfg : ∀ x, x ≠ v → S.edge v x = true → |((f x).val : ℚ) - (g x).val| ≤ D) :
    |((conditionalUpper S v f).val : ℚ) - (conditionalUpper S v g).val| ≤ D := by
  have h1 := upper_le_add S v f g D hD (fun x hx he => by
    linarith [(abs_le.mp (hfg x hx he)).2])
  have h2 := upper_le_add S v g f D hD (fun x hx he => by
    linarith [(abs_le.mp (hfg x hx he)).1])
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A shared-clock refresh, converted back to the finite palette. -/
def refreshColor (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (hf : S.Valid f) (u : ℚ) (hu : 0 ≤ u ∧ u < 1) :
    Fin (K + 1) :=
  let lo := conditionalLower S v f
  let hi := conditionalUpper S v f
  let z := quantile lo.val hi.val u
  have hbounds := current_mem_conditional S v f hf
  have hlohi : (lo.val : ℤ) ≤ hi.val := by exact_mod_cast hbounds.1.trans hbounds.2
  have hz := quantile_mem hlohi hu.1 hu.2
  ⟨z.toNat, by have := hi.isLt; omega⟩

@[simp] theorem refreshColor_val (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (hf : S.Valid f) (u : ℚ) (hu : 0 ≤ u ∧ u < 1) :
    ((refreshColor S v f hf u hu).val : ℤ) =
      quantile (conditionalLower S v f).val (conditionalUpper S v f).val u := by
  dsimp [refreshColor]
  apply Int.toNat_of_nonneg
  have hb := current_mem_conditional S v f hf
  have hz := quantile_mem (show ((conditionalLower S v f).val : ℤ) ≤
    (conditionalUpper S v f).val by exact_mod_cast hb.1.trans hb.2) hu.1 hu.2
  omega

theorem refreshColor_mem (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (hf : S.Valid f) (u : ℚ) (hu : 0 ≤ u ∧ u < 1) :
    conditionalLower S v f ≤ refreshColor S v f hf u hu ∧
      refreshColor S v f hf u hu ≤ conditionalUpper S v f := by
  have hb := current_mem_conditional S v f hf
  have hz := quantile_mem (show ((conditionalLower S v f).val : ℤ) ≤
    (conditionalUpper S v f).val by exact_mod_cast hb.1.trans hb.2) hu.1 hu.2
  rw [← refreshColor_val S v f hf u hu] at hz
  exact_mod_cast hz

/-- The update itself remains in the feasible weak-map space. -/
theorem refresh_valid (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (hf : S.Valid f) (u : ℚ) (hu : 0 ≤ u ∧ u < 1) :
    S.Valid (Function.update f v (refreshColor S v f hf u hu)) :=
  (valid_update_iff S v f hf _).mpr (refreshColor_mem S v f hf u hu)

/-- The actual single-coordinate inequality used in the manuscript's sweep
coupling. During a topological sweep the predecessor discrepancies are new,
whereas successor discrepancies still belong to the preceding sweep. -/
theorem refresh_discrepancy (S : WeakSystem α (K + 1)) (v : α)
    (f g : ColorMap α (K + 1)) (hf : S.Valid f) (hg : S.Valid g)
    (u : ℚ) (hu : 0 ≤ u ∧ u < 1) (P T : ℚ) (hP : 0 ≤ P) (hT : 0 ≤ T)
    (hpred : ∀ x, x ≠ v → S.edge x v = true → |((f x).val : ℚ) - (g x).val| ≤ P)
    (hsucc : ∀ x, x ≠ v → S.edge v x = true → |((f x).val : ℚ) - (g x).val| ≤ T) :
    |((refreshColor S v f hf u hu).val : ℚ) - (refreshColor S v g hg u hu).val| ≤
      1 + (1 - u) * P + u * T := by
  have hlo := conditionalLower_discrepancy S v f g P hP hpred
  have hhi := conditionalUpper_discrepancy S v f g T hT hsucc
  have hq := quantile_discrepancy
    (a := (conditionalLower S v f).val) (b := (conditionalUpper S v f).val)
    (c := (conditionalLower S v g).val) (d := (conditionalUpper S v g).val) hu.1 hu.2.le
  have hvf := congrArg (fun x : ℤ => (x : ℚ)) (refreshColor_val S v f hf u hu)
  have hvg := congrArg (fun x : ℤ => (x : ℚ)) (refreshColor_val S v g hg u hu)
  norm_cast at hvf hvg
  simp only [Int.cast_natCast] at hq
  rw [← hvf, ← hvg] at hq
  simp only [Int.cast_natCast] at hq
  nlinarith

/-- Two states are in the same one-coordinate conditional fibre. -/
def SameOutside (v : α) (f g : ColorMap α (K + 1)) : Prop :=
  ∀ x, x ≠ v → f x = g x

instance (v : α) (f g : ColorMap α (K + 1)) : Decidable (SameOutside v f g) := by
  unfold SameOutside
  infer_instance

omit [Fintype α] [DecidableEq α] in
theorem sameOutside_refl (v : α) (f : ColorMap α (K + 1)) : SameOutside v f f :=
  fun _ _ => rfl

omit [Fintype α] [DecidableEq α] in
theorem sameOutside_symm {v : α} {f g : ColorMap α (K + 1)}
    (h : SameOutside v f g) : SameOutside v g f := fun x hx => (h x hx).symm

omit [Fintype α] [DecidableEq α] in
theorem sameOutside_trans {v : α} {f g h : ColorMap α (K + 1)}
    (hfg : SameOutside v f g) (hgh : SameOutside v g h) : SameOutside v f h :=
  fun x hx => (hfg x hx).trans (hgh x hx)

/-- The actual conditional fibre in the finite weak-map model. -/
def conditionalFiber (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) : Finset (ColorMap α (K + 1)) :=
  S.maps.filter (SameOutside v f)

@[simp] theorem mem_conditionalFiber (S : WeakSystem α (K + 1)) (v : α)
    (f g : ColorMap α (K + 1)) :
    g ∈ conditionalFiber S v f ↔ S.Valid g ∧ SameOutside v f g := by
  simp [conditionalFiber]

theorem conditionalFiber_eq {S : WeakSystem α (K + 1)} {v : α}
    {f g : ColorMap α (K + 1)} (hfg : SameOutside v f g) :
    conditionalFiber S v f = conditionalFiber S v g := by
  ext h
  simp only [mem_conditionalFiber]
  constructor
  · rintro ⟨hh, hfh⟩
    exact ⟨hh, sameOutside_trans (sameOutside_symm hfg) hfh⟩
  · rintro ⟨hh, hgh⟩
    exact ⟨hh, sameOutside_trans hfg hgh⟩

theorem conditionalFiber_card_pos (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (hf : S.Valid f) :
    0 < (conditionalFiber S v f).card := by
  apply Finset.card_pos.mpr
  exact ⟨f, (mem_conditionalFiber S v f f).mpr ⟨hf, sameOutside_refl v f⟩⟩

/-- A conditional fibre is exactly an update at a colour in its inclusive
conditional interval; it contains no additional hidden constraints. -/
theorem mem_conditionalFiber_iff (S : WeakSystem α (K + 1)) (v : α)
    (f g : ColorMap α (K + 1)) (hf : S.Valid f) :
    g ∈ conditionalFiber S v f ↔
      ∃ c, conditionalLower S v f ≤ c ∧ c ≤ conditionalUpper S v f ∧
        g = Function.update f v c := by
  rw [mem_conditionalFiber]
  constructor
  · rintro ⟨hg, hfg⟩
    have heq : g = Function.update f v (g v) := by
      funext x
      by_cases hx : x = v
      · subst x; simp
      · simpa [Function.update_of_ne hx] using (hfg x hx).symm
    refine ⟨g v, ?_, ?_, heq⟩
    · exact ((valid_update_iff S v f hf (g v)).mp (heq ▸ hg)).1
    · exact ((valid_update_iff S v f hf (g v)).mp (heq ▸ hg)).2
  · rintro ⟨c, hlo, hhi, rfl⟩
    refine ⟨(valid_update_iff S v f hf c).mpr ⟨hlo, hhi⟩, ?_⟩
    intro x hx
    simp [Function.update_of_ne hx]


/-- Number of colours in a feasible conditional interval. -/
def conditionalWidth (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) : ℕ :=
  (conditionalUpper S v f).val + 1 - (conditionalLower S v f).val

theorem conditionalWidth_pos (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (hf : S.Valid f) : 0 < conditionalWidth S v f := by
  have hb := current_mem_conditional S v f hf
  have : (conditionalLower S v f).val ≤ (conditionalUpper S v f).val := hb.1.trans hb.2
  unfold conditionalWidth
  omega

/-- Enumerate the conditional interval in increasing order. -/
def conditionalColor (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (hf : S.Valid f) (i : Fin (conditionalWidth S v f)) :
    Fin (K + 1) :=
  ⟨(conditionalLower S v f).val + i.val, by
    have hb := current_mem_conditional S v f hf
    have hle : (conditionalLower S v f).val ≤ (conditionalUpper S v f).val := hb.1.trans hb.2
    have hi := i.isLt
    have hu := (conditionalUpper S v f).isLt
    unfold conditionalWidth at hi
    omega⟩

theorem conditionalColor_mem (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (hf : S.Valid f) (i : Fin (conditionalWidth S v f)) :
    conditionalLower S v f ≤ conditionalColor S v f hf i ∧
      conditionalColor S v f hf i ≤ conditionalUpper S v f := by
  have hi := i.isLt
  unfold conditionalWidth at hi
  change (conditionalLower S v f).val ≤ (conditionalLower S v f).val + i.val ∧
    (conditionalLower S v f).val + i.val ≤ (conditionalUpper S v f).val
  omega

/-- The interval index parametrises the actual conditional fibre injectively. -/
def conditionalEmbedding (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (hf : S.Valid f) :
    Fin (conditionalWidth S v f) ↪ ColorMap α (K + 1) where
  toFun i := Function.update f v (conditionalColor S v f hf i)
  inj' := by
    intro i j h
    have hv := congrArg (fun g => (g v).val) h
    simp [conditionalColor] at hv
    exact Fin.ext (by omega)

theorem conditionalFiber_eq_map (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (hf : S.Valid f) :
    conditionalFiber S v f = Finset.univ.map (conditionalEmbedding S v f hf) := by
  ext g
  rw [mem_conditionalFiber_iff S v f g hf, Finset.mem_map]
  constructor
  · rintro ⟨c, hlo, hhi, rfl⟩
    let i : Fin (conditionalWidth S v f) :=
      ⟨c.val - (conditionalLower S v f).val, by
        have hl : (conditionalLower S v f).val ≤ c.val := hlo
        have hh : c.val ≤ (conditionalUpper S v f).val := hhi
        unfold conditionalWidth
        omega⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply congrArg (Function.update f v)
    apply Fin.ext
    change (conditionalLower S v f).val + (c.val - (conditionalLower S v f).val) = c.val
    exact Nat.add_sub_of_le hlo
  · rintro ⟨i, _, rfl⟩
    exact ⟨conditionalColor S v f hf i, (conditionalColor_mem S v f hf i).1,
      (conditionalColor_mem S v f hf i).2, rfl⟩

theorem conditionalFiber_card (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (hf : S.Valid f) :
    (conditionalFiber S v f).card = conditionalWidth S v f := by
  rw [conditionalFiber_eq_map S v f hf]
  simp

/-- The finite common-clock update returns exactly the indexed interval colour
on each of its equal-sized clock blocks. -/
theorem refreshColor_grid_block (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (hf : S.Valid f) {m : ℕ} (hm : 0 < m)
    (i : Fin (conditionalWidth S v f)) (j : Fin m) :
    refreshColor S v f hf (gridClock (finProdFinEquiv (i, j)))
      (gridClock_mem _) = conditionalColor S v f hf i := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [refreshColor_val]
  have hb := current_mem_conditional S v f hf
  have hlohi : (conditionalLower S v f).val ≤ (conditionalUpper S v f).val := hb.1.trans hb.2
  have hhi : ((conditionalUpper S v f).val : ℤ) =
      (conditionalLower S v f).val + conditionalWidth S v f - 1 := by
    unfold conditionalWidth
    omega
  rw [hhi]
  simpa [gridClock, finProdFinEquiv, conditionalColor] using
    quantile_grid_block ((conditionalLower S v f).val : ℤ)
      (conditionalWidth_pos S v f hf) hm i j

/-- Exact clock average for the actual coordinate update, before normalisation. -/
theorem refresh_grid_sum (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (hf : S.Valid f) {m : ℕ} (hm : 0 < m)
    (φ : ColorMap α (K + 1) → ℚ) :
    (∑ r : Fin (conditionalWidth S v f * m),
      φ (Function.update f v (refreshColor S v f hf (gridClock r) (gridClock_mem r)))) =
      m * ∑ i : Fin (conditionalWidth S v f), φ (conditionalEmbedding S v f hf i) := by
  calc
    _ = ∑ p : Fin (conditionalWidth S v f) × Fin m,
      φ (Function.update f v (refreshColor S v f hf (gridClock (finProdFinEquiv p))
        (gridClock_mem _))) :=
      (Fintype.sum_equiv finProdFinEquiv _ _ (fun _ => rfl)).symm
    _ = ∑ i : Fin (conditionalWidth S v f), ∑ _j : Fin m,
      φ (conditionalEmbedding S v f hf i) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [refreshColor_grid_block S v f hf hm i j]
        rfl
    _ = _ := by simp [← Finset.mul_sum]
/-- The exact conditional refresh transition. Sums below range only over
feasible weak maps. Its symmetry is the finite detailed-balance identity. -/
def refreshKernel (S : WeakSystem α (K + 1)) (v : α)
    (f g : ColorMap α (K + 1)) : ℚ :=
  if SameOutside v f g then ((conditionalFiber S v f).card : ℚ)⁻¹ else 0

theorem refreshKernel_nonneg (S : WeakSystem α (K + 1)) (v : α)
    (f g : ColorMap α (K + 1)) : 0 ≤ refreshKernel S v f g := by
  unfold refreshKernel
  split_ifs
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact le_refl _

theorem refreshKernel_symm (S : WeakSystem α (K + 1)) (v : α)
    (f g : ColorMap α (K + 1)) : refreshKernel S v f g = refreshKernel S v g f := by
  by_cases h : SameOutside v f g
  · simp only [refreshKernel, if_pos h, if_pos (sameOutside_symm h)]
    rw [conditionalFiber_eq h]
  · have h' : ¬ SameOutside v g f := fun hg => h (sameOutside_symm hg)
    simp [refreshKernel, h, h']

theorem refreshKernel_row_sum (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (hf : S.Valid f) :
    (∑ g ∈ S.maps, refreshKernel S v f g) = 1 := by
  unfold refreshKernel
  rw [← Finset.sum_filter]
  change (∑ _ ∈ conditionalFiber S v f, ((conditionalFiber S v f).card : ℚ)⁻¹) = 1
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast (conditionalFiber_card_pos S v f hf).ne')

theorem refreshKernel_column_sum (S : WeakSystem α (K + 1)) (v : α)
    (g : ColorMap α (K + 1)) (hg : S.Valid g) :
    (∑ f ∈ S.maps, refreshKernel S v f g) = 1 := by
  simp_rw [refreshKernel_symm S v _ g]
  exact refreshKernel_row_sum S v g hg

/-- Refresh one coordinate and then evaluate an observable. -/
def refreshObservable (S : WeakSystem α (K + 1)) (v : α)
    (φ : ColorMap α (K + 1) → ℚ) (f : ColorMap α (K + 1)) : ℚ :=
  ∑ g ∈ S.maps, refreshKernel S v f g * φ g


/-- The symmetric refresh kernel is precisely uniform averaging over the
actual conditional interval. -/
theorem refreshObservable_eq_interval_average (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (hf : S.Valid f) (φ : ColorMap α (K + 1) → ℚ) :
    refreshObservable S v φ f =
      (∑ i : Fin (conditionalWidth S v f), φ (conditionalEmbedding S v f hf i)) /
        conditionalWidth S v f := by
  simp only [refreshObservable, refreshKernel, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  change (∑ g ∈ conditionalFiber S v f,
    ((conditionalFiber S v f).card : ℚ)⁻¹ * φ g) = _
  rw [← Finset.mul_sum, conditionalFiber_card S v f hf,
    conditionalFiber_eq_map S v f hf, Finset.sum_map]
  rw [div_eq_mul_inv, mul_comm]

/-- A shared finite clock whose size is divisible by every conditional width
implements the exact Gibbs kernel, without discretisation error. -/
theorem refresh_grid_eq_kernel (S : WeakSystem α (K + 1)) (v : α)
    (f : ColorMap α (K + 1)) (hf : S.Valid f) {Q : ℕ} (hQ : 0 < Q)
    (hdiv : conditionalWidth S v f ∣ Q) (φ : ColorMap α (K + 1) → ℚ) :
    (∑ r : Fin Q,
      φ (Function.update f v (refreshColor S v f hf (gridClock r) (gridClock_mem r)))) /
      Q = refreshObservable S v φ f := by
  obtain ⟨m, rfl⟩ := hdiv
  have hm : 0 < m := Nat.pos_of_mul_pos_left hQ
  rw [refresh_grid_sum S v f hf hm φ, refreshObservable_eq_interval_average S v f hf φ]
  have hn' : (conditionalWidth S v f : ℚ) ≠ 0 := by
    exact_mod_cast (conditionalWidth_pos S v f hf).ne'
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp
/-- Uniform averaging is invariant under each actual conditional refresh.
Dividing both sides by the positive weak-map count gives stationarity of the
uniform probability law. The statement also handles the empty sum. -/
theorem refresh_preserves_uniform_sum (S : WeakSystem α (K + 1)) (v : α)
    (φ : ColorMap α (K + 1) → ℚ) :
    (∑ f ∈ S.maps, refreshObservable S v φ f) = ∑ f ∈ S.maps, φ f := by
  unfold refreshObservable
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g hg
  rw [← Finset.sum_mul, refreshKernel_column_sum S v g ((S.mem_maps g).mp hg), one_mul]

/-- A fixed sequence of conditional updates, in any supplied order. -/
def sweepObservable (S : WeakSystem α (K + 1)) : List α →
    (ColorMap α (K + 1) → ℚ) → ColorMap α (K + 1) → ℚ
  | [], φ => φ
  | v :: vs, φ => refreshObservable S v (sweepObservable S vs φ)

/-- In particular a bottom-to-top sweep, and any number of such sweeps,
preserve the uniform weak-map law exactly. -/
theorem sweep_preserves_uniform_sum (S : WeakSystem α (K + 1)) (vs : List α)
    (φ : ColorMap α (K + 1) → ℚ) :
    (∑ f ∈ S.maps, sweepObservable S vs φ f) = ∑ f ∈ S.maps, φ f := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [sweepObservable, refresh_preserves_uniform_sum, ih]

end Finite

/-- The bound used when eliminating successively earlier predecessor terms.
Increasing the rank weakens the bound for every clock floor in `[0,1]`. -/
theorem rank_bound_mono {A B : ℚ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hB : 0 ≤ B)
    {k l : ℕ} (hkl : k ≤ l) :
    (k : ℚ) + (1 - A ^ k) * B ≤ (l : ℚ) + (1 - A ^ l) * B := by
  have hp := pow_le_pow_of_le_one hA0 hA1 hkl
  have hk : (k : ℚ) ≤ l := by exact_mod_cast hkl
  nlinarith

/-- Deterministic expansion of a topological refresh recurrence. The relation
is the raw predecessor relation and `rank` strictly increases along every row.
The step premise is the already-proved one-coordinate inequality with any
common upper bound on refreshed predecessors. Thus the result does not assume
a contraction conclusion or a mixing hypothesis. -/
theorem sweep_contraction_of_rank {ι : Type*} (R : ι → ι → Prop)
    (rank : ι → ℕ) (hrank : ∀ {x y}, R x y → rank x < rank y)
    (p D : ι → ℚ) (A B : ℚ) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hB : 0 ≤ B)
    (hp : ∀ v, A ≤ p v ∧ p v ≤ 1)
    (hstep : ∀ v E, 0 ≤ E → (∀ x, R x v → D x ≤ E) →
      D v ≤ 1 + p v * E + (1 - p v) * B) :
    ∀ v, D v ≤ (rank v + 1 : ℕ) + (1 - A ^ (rank v + 1)) * B := by
  intro v
  induction hn : rank v using Nat.strong_induction_on generalizing v with
  | h n ih =>
    have hpow : 0 ≤ A ^ n := pow_nonneg hA0 _
    have hpow1 : A ^ n ≤ 1 := pow_le_one₀ hA0 hA1
    have hE : 0 ≤ (n : ℚ) + (1 - A ^ n) * B := by positivity
    have hpred : ∀ x, R x v → D x ≤ (n : ℚ) + (1 - A ^ n) * B := by
      intro x hx
      have hxn : rank x < n := hn ▸ hrank hx
      have hxbound := ih (rank x) hxn x rfl
      exact hxbound.trans (rank_bound_mono hA0 hA1 hB (Nat.succ_le_of_lt hxn))
    have h := hstep v _ hE hpred
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    have hpv := hp v
    have hpn : p v * n ≤ (n : ℚ) := mul_le_of_le_one_left (Nat.cast_nonneg n) hpv.2
    have hterm : A ^ n * A * B ≤ p v * (A ^ n * B) := by
      nlinarith [mul_nonneg hpow hB]
    nlinarith

/-- Uniform height version of the preceding exact rank estimate, corresponding
to inequality (II) in the manuscript. -/
theorem sweep_contraction_of_height {ι : Type*} (R : ι → ι → Prop)
    (rank : ι → ℕ) (H : ℕ) (hrank : ∀ {x y}, R x y → rank x < rank y)
    (hheight : ∀ v, rank v + 1 ≤ H) (p D : ι → ℚ) (A B : ℚ)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hB : 0 ≤ B)
    (hp : ∀ v, A ≤ p v ∧ p v ≤ 1)
    (hstep : ∀ v E, 0 ≤ E → (∀ x, R x v → D x ≤ E) →
      D v ≤ 1 + p v * E + (1 - p v) * B) :
    ∀ v, D v ≤ (H : ℚ) + (1 - A ^ H) * B := by
  intro v
  exact (sweep_contraction_of_rank R rank hrank p D A B hA0 hA1 hB hp hstep v).trans
    (rank_bound_mono hA0 hA1 hB (hheight v))

/-- Subtracting one additive height cost per sweep gives the pure
multiplicative recurrence for positive parts. -/
theorem shifted_discrepancy {D B c H j : ℚ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hH : 0 ≤ H) (hj : 0 ≤ j) (hstep : D ≤ H + c * B) :
    max (D - H * (j + 1)) 0 ≤ c * max (B - H * j) 0 := by
  apply max_le
  · have hmax := le_max_left (B - H * j) 0
    have hprod : 0 ≤ H * j := mul_nonneg hH hj
    nlinarith
  · exact mul_nonneg hc0 (le_max_right _ _)

end SortingAdversary.Optimal.LocalCoupling
