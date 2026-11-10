import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The continuous paper's finite digit calculation

The update in `for-humans/sections/positions.tex` is an affine update, not
the integer-colour heat-bath update in `Optimal/`.  This file implements that
update, its sequential sweeps, and the enumeration of their digit assignments.
The scalar is generic: `ℚ` gives executable exact arithmetic and `ℝ` gives the
same formula on continuous feasible assignments.

The checked enclosure statements are deterministic and hold for every digit
assignment. They do not by themselves assert that a continuously distributed
feasible assignment is stationary, or assert a mixing rate.
-/

namespace SortingAdversary.Continuous.FiniteAveraging

open scoped BigOperators

section Scalar

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- One of the paper's `S` affine updates.  A `Fin S` digit also certifies
that the alphabet is nonempty. -/
def digit (S : ℕ) (j : Fin S) (y l u : K) : K :=
  (y + ((S : K) - 1 - j.val) * l + j.val * u) / S

theorem alphabet_pos {S : ℕ} (j : Fin S) : (0 : K) < S := by
  exact_mod_cast (Nat.zero_lt_of_lt j.isLt)

theorem lower_coefficient_nonneg {S : ℕ} (j : Fin S) :
    (0 : K) ≤ (S : K) - 1 - j.val := by
  have h : (j.val : K) + 1 ≤ (S : K) := by
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  linarith

@[simp] theorem digit_same {S : ℕ} (j : Fin S) (c : K) : digit S j c c c = c := by
  unfold digit
  have hS : (S : K) ≠ 0 := ne_of_gt (alphabet_pos (K := K) j)
  field_simp
  <;> ring

/-- The coefficients are nonnegative, so all three inputs are monotone. -/
theorem digit_mono {S : ℕ} (j : Fin S) {y y' l l' u u' : K}
    (hy : y ≤ y') (hl : l ≤ l') (hu : u ≤ u') :
    digit S j y l u ≤ digit S j y' l' u' := by
  unfold digit
  apply div_le_div_of_nonneg_right _ (alphabet_pos (K := K) j).le
  exact add_le_add (add_le_add hy
    (mul_le_mul_of_nonneg_left hl (lower_coefficient_nonneg j)))
    (mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg _))

/-- A weakly feasible coordinate remains in its conditional interval. -/
theorem digit_mem {S : ℕ} (j : Fin S) {y l u : K} (hly : l ≤ y) (hyu : y ≤ u) :
    l ≤ digit S j y l u ∧ digit S j y l u ≤ u := by
  constructor
  · simpa using digit_mono j hly (le_refl l) (hly.trans hyu)
  · simpa using digit_mono j hyu (hly.trans hyu) (le_refl u)

/-- Even the extreme digits preserve strict feasibility because the old
coordinate has the strictly positive coefficient `1/S`. -/
theorem digit_mem_strict {S : ℕ} (j : Fin S) {y l u : K}
    (hly : l < y) (hyu : y < u) :
    l < digit S j y l u ∧ digit S j y l u < u := by
  have hS := alphabet_pos (K := K) j
  have hj : (0 : K) ≤ j.val := Nat.cast_nonneg _
  have hc := lower_coefficient_nonneg (K := K) j
  have hlu : 0 ≤ u - l := sub_nonneg.mpr (hly.trans hyu).le
  have hju := mul_nonneg hj hlu
  have hcl := mul_nonneg hc hlu
  unfold digit
  constructor
  · apply (lt_div_iff₀ hS).mpr
    nlinarith
  · apply (div_lt_iff₀ hS).mpr
    nlinarith

/-- The positive old-value coefficient preserves a strict lower bound even
when either of the other inputs lies on that bound. -/
theorem lt_digit_of_lt {S : ℕ} (j : Fin S) {c y l u : K}
    (hy : c < y) (hl : c ≤ l) (hu : c ≤ u) : c < digit S j y l u := by
  have hS := alphabet_pos (K := K) j
  have hl' := mul_le_mul_of_nonneg_left hl (lower_coefficient_nonneg (K := K) j)
  have hu' := mul_le_mul_of_nonneg_left hu (show (0 : K) ≤ j.val from Nat.cast_nonneg _)
  unfold digit
  apply (lt_div_iff₀ hS).mpr
  nlinarith

/-- The analogous strict upper-bound statement. -/
theorem digit_lt_of_lt {S : ℕ} (j : Fin S) {c y l u : K}
    (hy : y < c) (hl : l ≤ c) (hu : u ≤ c) : digit S j y l u < c := by
  have hS := alphabet_pos (K := K) j
  have hl' := mul_le_mul_of_nonneg_left hl (lower_coefficient_nonneg (K := K) j)
  have hu' := mul_le_mul_of_nonneg_left hu (show (0 : K) ≤ j.val from Nat.cast_nonneg _)
  unfold digit
  apply (div_lt_iff₀ hS).mpr
  nlinarith

/-- In normalized coordinates, the digit sends `r` to `(r+j)/S`. -/
theorem digit_normalized {S : ℕ} (j : Fin S) {y l u : K} (hlu : l ≠ u) :
    (digit S j y l u - l) / (u - l) = ((y - l) / (u - l) + j.val) / S := by
  have hS : (S : K) ≠ 0 := ne_of_gt (alphabet_pos (K := K) j)
  have hul : u - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hlu)
  unfold digit
  field_simp
  <;> ring

/-- Exact difference formula for shared digits. -/
theorem digit_sub {S : ℕ} (j : Fin S) (y y' l l' u u' : K) :
    digit S j y' l' u' - digit S j y l u =
      ((y' - y) + ((S : K) - 1 - j.val) * (l' - l) +
        j.val * (u' - u)) / S := by
  unfold digit
  ring

/-- The one-coordinate inequality used in the sweep-width recurrence. -/
theorem digit_width_le {S : ℕ} (j : Fin S) {y y' l l' u u' a b c : K}
    (hy : y' - y ≤ a) (hl : l' - l ≤ b) (hu : u' - u ≤ c) :
    digit S j y' l' u' - digit S j y l u ≤
      (a + ((S : K) - 1 - j.val) * b + j.val * c) / S := by
  rw [digit_sub]
  apply div_le_div_of_nonneg_right _ (alphabet_pos (K := K) j).le
  exact add_le_add (add_le_add hy
    (mul_le_mul_of_nonneg_left hl (lower_coefficient_nonneg j)))
    (mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg _))

end Scalar

/-- Interval data and an explicit directed graph. Acyclicity is not needed
for the single-update invariants, only for the later sweep estimates. -/
structure System (ι : Type*) (K : Type*) where
  lower : ι → K
  upper : ι → K
  edge : ι → ι → Bool

section System

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def System.WeaklyFeasible (D : System ι K) (Y : ι → K) : Prop :=
  (∀ v, D.lower v ≤ Y v ∧ Y v ≤ D.upper v) ∧
    ∀ v w, D.edge v w = true → Y v ≤ Y w

def System.StrictlyFeasible (D : System ι K) (Y : ι → K) : Prop :=
  (∀ v, D.lower v < Y v ∧ Y v < D.upper v) ∧
    ∀ v w, D.edge v w = true → Y v < Y w

def conditionalLower (D : System ι K) (v : ι) (Y : ι → K) : K :=
  (Finset.univ.filter fun w => D.edge w v).fold max (D.lower v) Y

def conditionalUpper (D : System ι K) (v : ι) (Y : ι → K) : K :=
  (Finset.univ.filter fun w => D.edge v w).fold min (D.upper v) Y

theorem lower_le_conditionalLower (D : System ι K) (v : ι) (Y : ι → K) :
    D.lower v ≤ conditionalLower D v Y :=
  (Finset.le_fold_max _).mpr (Or.inl le_rfl)

theorem conditionalUpper_le_upper (D : System ι K) (v : ι) (Y : ι → K) :
    conditionalUpper D v Y ≤ D.upper v :=
  (Finset.fold_min_le _).mpr (Or.inl le_rfl)

theorem predecessor_le_conditionalLower (D : System ι K) (v w : ι) (Y : ι → K)
    (h : D.edge w v = true) : Y w ≤ conditionalLower D v Y :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨w, by simp [h], le_rfl⟩)

theorem conditionalUpper_le_successor (D : System ι K) (v w : ι) (Y : ι → K)
    (h : D.edge v w = true) : conditionalUpper D v Y ≤ Y w :=
  (Finset.fold_min_le _).mpr (Or.inr ⟨w, by simp [h], le_rfl⟩)

theorem conditionalLower_mono (D : System ι K) (v : ι) {Y Z : ι → K}
    (h : ∀ w, Y w ≤ Z w) : conditionalLower D v Y ≤ conditionalLower D v Z := by
  apply (Finset.fold_max_le _).mpr
  refine ⟨lower_le_conditionalLower D v Z, ?_⟩
  intro w hw
  exact (h w).trans (predecessor_le_conditionalLower D v w Z (by simpa using hw))

theorem conditionalUpper_mono (D : System ι K) (v : ι) {Y Z : ι → K}
    (h : ∀ w, Y w ≤ Z w) : conditionalUpper D v Y ≤ conditionalUpper D v Z := by
  apply (Finset.le_fold_min _).mpr
  refine ⟨conditionalUpper_le_upper D v Y, ?_⟩
  intro w hw
  exact (conditionalUpper_le_successor D v w Y (by simpa using hw)).trans (h w)

theorem conditional_mem (D : System ι K) (v : ι) {Y : ι → K}
    (hY : D.WeaklyFeasible Y) :
    conditionalLower D v Y ≤ Y v ∧ Y v ≤ conditionalUpper D v Y := by
  constructor
  · apply (Finset.fold_max_le _).mpr
    refine ⟨(hY.1 v).1, ?_⟩
    intro w hw
    exact hY.2 w v (by simpa using hw)
  · apply (Finset.le_fold_min _).mpr
    refine ⟨(hY.1 v).2, ?_⟩
    intro w hw
    exact hY.2 v w (by simpa using hw)

theorem conditional_mem_strict (D : System ι K) (v : ι) {Y : ι → K}
    (hY : D.StrictlyFeasible Y) :
    conditionalLower D v Y < Y v ∧ Y v < conditionalUpper D v Y := by
  constructor
  · apply (Finset.fold_max_lt _).mpr
    refine ⟨(hY.1 v).1, ?_⟩
    intro w hw
    exact hY.2 w v (by simpa using hw)
  · apply (Finset.lt_fold_min _).mpr
    refine ⟨(hY.1 v).2, ?_⟩
    intro w hw
    exact hY.2 v w (by simpa using hw)

theorem conditionalLower_sub_le (D : System ι K) (v : ι) (Y Z : ι → K)
    {P : K} (hP : 0 ≤ P) (h : ∀ w, D.edge w v = true → Z w - Y w ≤ P) :
    conditionalLower D v Z - conditionalLower D v Y ≤ P := by
  have hle : conditionalLower D v Z ≤ conditionalLower D v Y + P := by
    apply (Finset.fold_max_le _).mpr
    constructor
    · exact (lower_le_conditionalLower D v Y).trans (le_add_of_nonneg_right hP)
    · intro w hw
      have he : D.edge w v = true := by simpa using hw
      have hw' := predecessor_le_conditionalLower D v w Y he
      have hd := h w he
      linarith
  linarith

theorem conditionalUpper_sub_le (D : System ι K) (v : ι) (Y Z : ι → K)
    {P : K} (hP : 0 ≤ P) (h : ∀ w, D.edge v w = true → Z w - Y w ≤ P) :
    conditionalUpper D v Z - conditionalUpper D v Y ≤ P := by
  have hle : conditionalUpper D v Z - P ≤ conditionalUpper D v Y := by
    apply (Finset.le_fold_min _).mpr
    constructor
    · have hb := conditionalUpper_le_upper D v Z
      linarith
    · intro w hw
      have he : D.edge v w = true := by simpa using hw
      have hw' := conditionalUpper_le_successor D v w Z he
      have hd := h w he
      linarith
  linarith

/-- The exact state update in Algorithm `Enclose`. -/
def update (D : System ι K) (S : ℕ) (j : Fin S) (v : ι) (Y : ι → K) : ι → K :=
  Function.update Y v (digit S j (Y v) (conditionalLower D v Y) (conditionalUpper D v Y))

@[simp] theorem update_self (D : System ι K) (S : ℕ) (j : Fin S) (v : ι) (Y : ι → K) :
    update D S j v Y v = digit S j (Y v) (conditionalLower D v Y) (conditionalUpper D v Y) := by
  simp [update]

@[simp] theorem update_other (D : System ι K) (S : ℕ) (j : Fin S) (v w : ι) (Y : ι → K)
    (hw : w ≠ v) : update D S j v Y w = Y w := by
  simp [update, Function.update_of_ne hw]

theorem update_mono (D : System ι K) (S : ℕ) (j : Fin S) (v : ι) {Y Z : ι → K}
    (h : ∀ w, Y w ≤ Z w) : ∀ w, update D S j v Y w ≤ update D S j v Z w := by
  intro w
  by_cases hw : w = v
  · subst w
    simp only [update_self]
    exact digit_mono j (h v) (conditionalLower_mono D v h) (conditionalUpper_mono D v h)
  · simpa [update_other, hw] using h w

theorem update_weaklyFeasible (D : System ι K) (S : ℕ) (j : Fin S) (v : ι) {Y : ι → K}
    (hY : D.WeaklyFeasible Y) : D.WeaklyFeasible (update D S j v Y) := by
  have hm := conditional_mem D v hY
  have hd := digit_mem j hm.1 hm.2
  constructor
  · intro w
    by_cases hw : w = v
    · subst w
      simp only [update_self]
      exact ⟨(lower_le_conditionalLower D v Y).trans hd.1,
        hd.2.trans (conditionalUpper_le_upper D v Y)⟩
    · simpa [update_other, hw] using hY.1 w
  · intro a b hab
    by_cases ha : a = v
    · subst a
      by_cases hb : b = v
      · subst b
        exact le_refl _
      · rw [update_self, update_other D S j v b Y hb]
        exact hd.2.trans (conditionalUpper_le_successor D v b Y hab)
    · by_cases hb : b = v
      · subst b
        rw [update_other D S j v a Y ha, update_self]
        exact (predecessor_le_conditionalLower D v a Y hab).trans hd.1
      · simpa [update_other, ha, hb] using hY.2 a b hab

theorem update_strictlyFeasible (D : System ι K) (S : ℕ) (j : Fin S) (v : ι) {Y : ι → K}
    (hY : D.StrictlyFeasible Y) : D.StrictlyFeasible (update D S j v Y) := by
  have hm := conditional_mem_strict D v hY
  have hd := digit_mem_strict j hm.1 hm.2
  constructor
  · intro w
    by_cases hw : w = v
    · subst w
      simp only [update_self]
      exact ⟨(lower_le_conditionalLower D v Y).trans_lt hd.1,
        hd.2.trans_le (conditionalUpper_le_upper D v Y)⟩
    · simpa [update_other, hw] using hY.1 w
  · intro a b hab
    by_cases ha : a = v
    · subst a
      by_cases hb : b = v
      · subst b
        exact False.elim (lt_irrefl _ (hY.2 v v hab))
      · rw [update_self, update_other D S j v b Y hb]
        exact hd.2.trans_le (conditionalUpper_le_successor D v b Y hab)
    · by_cases hb : b = v
      · subst b
        rw [update_other D S j v a Y ha, update_self]
        exact (predecessor_le_conditionalLower D v a Y hab).trans_lt hd.1
      · simpa [update_other, ha, hb] using hY.2 a b hab

theorem update_strict_lower (D : System ι K) (S : ℕ) (j : Fin S) (v : ι) {Y : ι → K}
    (hY : D.WeaklyFeasible Y) (hstrict : ∀ w, D.lower w < Y w) :
    ∀ w, D.lower w < update D S j v Y w := by
  intro w
  by_cases hw : w = v
  · subst w
    rw [update_self]
    exact lt_digit_of_lt j (hstrict v) (lower_le_conditionalLower D v Y)
      ((hY.1 v).1.trans (conditional_mem D v hY).2)
  · simpa [update_other, hw] using hstrict w

theorem update_strict_upper (D : System ι K) (S : ℕ) (j : Fin S) (v : ι) {Y : ι → K}
    (hY : D.WeaklyFeasible Y) (hstrict : ∀ w, Y w < D.upper w) :
    ∀ w, update D S j v Y w < D.upper w := by
  intro w
  by_cases hw : w = v
  · subst w
    rw [update_self]
    exact digit_lt_of_lt j (hstrict v)
      ((conditional_mem D v hY).1.trans (hY.1 v).2) (conditionalUpper_le_upper D v Y)
  · simpa [update_other, hw] using hstrict w

/-- The coordinate-width recurrence follows from the implemented maxima,
minima, and affine update. -/
theorem update_width_le (D : System ι K) (S : ℕ) (j : Fin S) (v : ι) (Y Z : ι → K)
    {a b c : K} (hb : 0 ≤ b) (hc : 0 ≤ c) (hy : Z v - Y v ≤ a)
    (hp : ∀ w, D.edge w v = true → Z w - Y w ≤ b)
    (hs : ∀ w, D.edge v w = true → Z w - Y w ≤ c) :
    update D S j v Z v - update D S j v Y v ≤
      (a + ((S : K) - 1 - j.val) * b + j.val * c) / S := by
  simp only [update_self]
  exact digit_width_le j hy (conditionalLower_sub_le D v Y Z hb hp)
    (conditionalUpper_sub_le D v Y Z hc hs)

/-- A schedule is an explicit list of interior vertices. Boundary vertices
are omitted, so their stored endpoints remain frozen. -/
def sweep (D : System ι K) (S : ℕ) (digits : ι → Fin S) (schedule : List ι)
    (Y : ι → K) : ι → K :=
  schedule.foldl (fun Z v => update D S (digits v) v Z) Y

theorem sweep_mono (D : System ι K) (S : ℕ) (digits : ι → Fin S) (schedule : List ι)
    {Y Z : ι → K} (h : ∀ w, Y w ≤ Z w) :
    ∀ w, sweep D S digits schedule Y w ≤ sweep D S digits schedule Z w := by
  induction schedule generalizing Y Z with
  | nil => exact h
  | cons v schedule ih => exact ih (update_mono D S (digits v) v h)

theorem sweep_weaklyFeasible (D : System ι K) (S : ℕ) (digits : ι → Fin S)
    (schedule : List ι) {Y : ι → K} (hY : D.WeaklyFeasible Y) :
    D.WeaklyFeasible (sweep D S digits schedule Y) := by
  induction schedule generalizing Y with
  | nil => exact hY
  | cons v schedule ih => exact ih (update_weaklyFeasible D S (digits v) v hY)

theorem sweep_frozen (D : System ι K) (S : ℕ) (digits : ι → Fin S)
    (schedule : List ι) (Y : ι → K) (w : ι) (hw : w ∉ schedule) :
    sweep D S digits schedule Y w = Y w := by
  induction schedule generalizing Y with
  | nil => rfl
  | cons v schedule ih =>
    have hm : w ≠ v ∧ w ∉ schedule := by simpa only [List.mem_cons, not_or] using hw
    have hne : w ≠ v := hm.1
    change sweep D S digits schedule (update D S (digits v) v Y) w = Y w
    rw [ih _ hm.2, update_other D S (digits v) v w Y hne]

/-- The sweeps use successive independent digit families when the input is
enumerated uniformly. This is an executable finite fold. -/
def run (D : System ι K) (S : ℕ) (schedule : List ι)
    (digitFamilies : List (ι → Fin S)) (Y : ι → K) : ι → K :=
  digitFamilies.foldl (fun Z digits => sweep D S digits schedule Z) Y

theorem run_mono (D : System ι K) (S : ℕ) (schedule : List ι)
    (digitFamilies : List (ι → Fin S)) {Y Z : ι → K} (h : ∀ w, Y w ≤ Z w) :
    ∀ w, run D S schedule digitFamilies Y w ≤ run D S schedule digitFamilies Z w := by
  induction digitFamilies generalizing Y Z with
  | nil => exact h
  | cons digits families ih => exact ih (sweep_mono D S digits schedule h)

theorem run_weaklyFeasible (D : System ι K) (S : ℕ) (schedule : List ι)
    (digitFamilies : List (ι → Fin S)) {Y : ι → K} (hY : D.WeaklyFeasible Y) :
    D.WeaklyFeasible (run D S schedule digitFamilies Y) := by
  induction digitFamilies generalizing Y with
  | nil => exact hY
  | cons digits families ih => exact ih (sweep_weaklyFeasible D S digits schedule hY)

/-- Every digit history sandwiches the corresponding full feasible
trajectory between the two endpoint calculations. -/
theorem run_encloses (D : System ι K) (S : ℕ) (schedule : List ι)
    (digitFamilies : List (ι → Fin S)) {Y : ι → K} (hY : D.WeaklyFeasible Y) :
    ∀ w, run D S schedule digitFamilies D.lower w ≤ run D S schedule digitFamilies Y w ∧
      run D S schedule digitFamilies Y w ≤ run D S schedule digitFamilies D.upper w := by
  intro w
  exact ⟨run_mono D S schedule digitFamilies (fun w => (hY.1 w).1) w,
    run_mono D S schedule digitFamilies (fun w => (hY.1 w).2) w⟩

end System

section OrderedSweep

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {n S : ℕ}

/-- A full sweep indexed by a topological ordering of the vertices. -/
def orderedAfter (D : System (Fin n) K) (digits : Fin n → Fin S)
    (Y : Fin n → K) : ℕ → Fin n → K
  | 0 => Y
  | t + 1 => if h : t < n then update D S (digits ⟨t, h⟩) ⟨t, h⟩
      (orderedAfter D digits Y t) else orderedAfter D digits Y t

def orderedSweep (D : System (Fin n) K) (digits : Fin n → Fin S)
    (Y : Fin n → K) : Fin n → K := orderedAfter D digits Y n

theorem orderedAfter_succ_other (D : System (Fin n) K) (digits : Fin n → Fin S)
    (Y : Fin n → K) (t : ℕ) (x : Fin n) (hx : x.val ≠ t) :
    orderedAfter D digits Y (t + 1) x = orderedAfter D digits Y t x := by
  conv_lhs => rw [orderedAfter]
  split_ifs with ht
  · exact update_other D S (digits ⟨t, ht⟩) ⟨t, ht⟩ x _
      (fun h => hx (congrArg Fin.val h))
  · rfl

theorem orderedAfter_old (D : System (Fin n) K) (digits : Fin n → Fin S)
    (Y : Fin n → K) (t : ℕ) (x : Fin n) (hx : t ≤ x.val) :
    orderedAfter D digits Y t x = Y x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [orderedAfter_succ_other D digits Y t x (by omega)]
    exact ih (by omega)

theorem orderedAfter_stable (D : System (Fin n) K) (digits : Fin n → Fin S)
    (Y : Fin n → K) (t u : ℕ) (x : Fin n) (hx : x.val < t) (htu : t ≤ u) :
    orderedAfter D digits Y u x = orderedAfter D digits Y t x := by
  induction u, htu using Nat.le_induction with
  | base => rfl
  | succ u htu ih =>
    rw [orderedAfter_succ_other D digits Y u x (by omega), ih]

theorem orderedSweep_apply (D : System (Fin n) K) (digits : Fin n → Fin S)
    (Y : Fin n → K) (v : Fin n) :
    orderedSweep D digits Y v =
      update D S (digits v) v (orderedAfter D digits Y v.val) v := by
  unfold orderedSweep
  rw [orderedAfter_stable D digits Y (v.val + 1) n v (by omega) (by omega)]
  simp only [orderedAfter, dif_pos v.isLt]

/-- The paper's old/self, new/predecessor, old/successor width recurrence,
derived for the actual topologically ordered sweep. -/
theorem orderedSweep_width_recurrence (D : System (Fin n) K)
    (horder : ∀ x y, D.edge x y = true → x.val < y.val)
    (digits : Fin n → Fin S) (A B : Fin n → K) (v : Fin n)
    {C P U : K} (hP : 0 ≤ P) (hU : 0 ≤ U) (hself : B v - A v ≤ C)
    (hpred : ∀ x, D.edge x v = true →
      orderedSweep D digits B x - orderedSweep D digits A x ≤ P)
    (hsucc : ∀ x, D.edge v x = true → B x - A x ≤ U) :
    orderedSweep D digits B v - orderedSweep D digits A v ≤
      (C + ((S : K) - 1 - (digits v).val) * P + (digits v).val * U) / S := by
  rw [orderedSweep_apply, orderedSweep_apply]
  apply update_width_le D S (digits v) v _ _ hP hU
  · simpa [orderedAfter_old D digits B v.val v le_rfl,
      orderedAfter_old D digits A v.val v le_rfl] using hself
  · intro x hx
    have hidx := horder x v hx
    have hA := orderedAfter_stable D digits A v.val n x hidx v.isLt.le
    have hB := orderedAfter_stable D digits B v.val n x hidx v.isLt.le
    simpa only [orderedSweep, ← hA, ← hB] using hpred x hx
  · intro x hx
    have hidx := horder v x hx
    simpa only [orderedAfter_old D digits B v.val x hidx.le,
      orderedAfter_old D digits A v.val x hidx.le] using hsucc x hx

end OrderedSweep

section Dyadic

/-- A rational number has at most `F` fractional binary digits. -/
def OnDyadicGrid (F : ℕ) (q : ℚ) : Prop := ∃ z : ℤ, q = z / (2 : ℚ) ^ F

theorem onDyadicGrid_add {F : ℕ} {q : ℚ} (hq : OnDyadicGrid F q) (e : ℕ) :
    OnDyadicGrid (F + e) q := by
  obtain ⟨z, rfl⟩ := hq
  refine ⟨z * (2 : ℤ) ^ e, ?_⟩
  push_cast
  rw [pow_add]
  field_simp

theorem onDyadicGrid_max {F : ℕ} {a b : ℚ}
    (ha : OnDyadicGrid F a) (hb : OnDyadicGrid F b) : OnDyadicGrid F (max a b) := by
  rcases max_choice a b with h | h <;> rw [h]
  · exact ha
  · exact hb

theorem onDyadicGrid_min {F : ℕ} {a b : ℚ}
    (ha : OnDyadicGrid F a) (hb : OnDyadicGrid F b) : OnDyadicGrid F (min a b) := by
  rcases min_choice a b with h | h <;> rw [h]
  · exact ha
  · exact hb

/-- Dividing the integer linear combination by `S = 2^s` adds at most
`s` fractional binary digits, exactly as in the arithmetic appendix. -/
theorem digit_onDyadicGrid {F s : ℕ} (j : Fin (2 ^ s)) {y l u : ℚ}
    (hy : OnDyadicGrid F y) (hl : OnDyadicGrid F l) (hu : OnDyadicGrid F u) :
    OnDyadicGrid (F + s) (digit (2 ^ s) j y l u) := by
  obtain ⟨ny, rfl⟩ := hy
  obtain ⟨nl, rfl⟩ := hl
  obtain ⟨nu, rfl⟩ := hu
  refine ⟨ny + ((2 : ℤ) ^ s - 1 - j.val) * nl + (j.val : ℤ) * nu, ?_⟩
  dsimp [digit]
  push_cast
  rw [pow_add]
  field_simp
  <;> ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem conditionalLower_onDyadicGrid (D : System ι ℚ) (v : ι) (Y : ι → ℚ) (F : ℕ)
    (hl : OnDyadicGrid F (D.lower v)) (hY : ∀ w, OnDyadicGrid F (Y w)) :
    OnDyadicGrid F (conditionalLower D v Y) := by
  unfold conditionalLower
  induction Finset.univ.filter (fun w => D.edge w v) using Finset.induction_on with
  | empty => simpa using hl
  | @insert w rest hw ih =>
    rw [Finset.fold_insert_idem]
    exact onDyadicGrid_max (hY w) ih

theorem conditionalUpper_onDyadicGrid (D : System ι ℚ) (v : ι) (Y : ι → ℚ) (F : ℕ)
    (hu : OnDyadicGrid F (D.upper v)) (hY : ∀ w, OnDyadicGrid F (Y w)) :
    OnDyadicGrid F (conditionalUpper D v Y) := by
  unfold conditionalUpper
  induction Finset.univ.filter (fun w => D.edge v w) using Finset.induction_on with
  | empty => simpa using hu
  | @insert w rest hw ih =>
    rw [Finset.fold_insert_idem]
    exact onDyadicGrid_min (hY w) ih

theorem update_onDyadicGrid (D : System ι ℚ) (F s : ℕ) (j : Fin (2 ^ s))
    (v : ι) (Y : ι → ℚ)
    (hl : OnDyadicGrid F (D.lower v)) (hu : OnDyadicGrid F (D.upper v))
    (hY : ∀ w, OnDyadicGrid F (Y w)) :
    ∀ w, OnDyadicGrid (F + s) (update D (2 ^ s) j v Y w) := by
  intro w
  by_cases hw : w = v
  · subst w
    rw [update_self]
    exact digit_onDyadicGrid j (hY v)
      (conditionalLower_onDyadicGrid D v Y F hl hY)
      (conditionalUpper_onDyadicGrid D v Y F hu hY)
  · rw [update_other D (2 ^ s) j v w Y hw]
    exact onDyadicGrid_add (hY w) s

end Dyadic

end SortingAdversary.Continuous.FiniteAveraging
