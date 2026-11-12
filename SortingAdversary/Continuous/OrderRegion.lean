import SortingAdversary.Continuous.FiniteAveraging
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.Basic

/-!
# The continuous feasible region and coordinate sections

This file gives the geometric meaning of the finite calculation's `System`.
The region is the actual open set of real assignments satisfying its strict
interval and arc inequalities.  Normalized bounds and a topological ordering
give a constructive feasible assignment and prove that every value in a stored
interval is attained.  Deleting a coordinate replaces its incident arcs by
exact interval bounds; the resulting region is exactly the coordinate section.

These statements do not assume positivity, canonical projections, or a section
identity as certificate fields.  They derive them from the displayed finite
constraints.  Density estimates and log-concavity are separate obligations.
-/

namespace SortingAdversary.Continuous.OrderRegion

open FiniteAveraging Set MeasureTheory

section Algebra

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Propagated lower and upper endpoints increase along every arc. -/
def Normalized (D : System ι K) : Prop :=
  ∀ x y, D.edge x y = true →
    D.lower x ≤ D.lower y ∧ D.upper x ≤ D.upper y

/-- One forward normalization update. -/
def propagateLower (D : System ι K) (v : ι) : System ι K :=
  { D with lower := Function.update D.lower v (conditionalLower D v D.lower) }

/-- One reverse normalization update. -/
def propagateUpper (D : System ι K) (v : ι) : System ι K :=
  { D with upper := Function.update D.upper v (conditionalUpper D v D.upper) }

theorem propagateLower_feasible_iff (D : System ι K) (v : ι) (Y : ι → K) :
    (propagateLower D v).StrictlyFeasible Y ↔ D.StrictlyFeasible Y := by
  constructor
  · intro h
    refine ⟨?_, h.2⟩
    intro x
    by_cases hx : x = v
    · subst x
      exact ⟨lt_of_le_of_lt (lower_le_conditionalLower D v D.lower)
        (by simpa [propagateLower] using (h.1 v).1), (h.1 v).2⟩
    · simpa [propagateLower, Function.update_of_ne hx] using h.1 x
  · intro h
    refine ⟨?_, h.2⟩
    intro x
    by_cases hx : x = v
    · subst x
      constructor
      · simp only [propagateLower, Function.update_self]
        apply (Finset.fold_max_lt _).mpr
        refine ⟨(h.1 v).1, ?_⟩
        intro u hu
        exact (h.1 u).1.trans (h.2 u v (by simpa using hu))
      · exact (h.1 v).2
    · simpa [propagateLower, Function.update_of_ne hx] using h.1 x

theorem propagateUpper_feasible_iff (D : System ι K) (v : ι) (Y : ι → K) :
    (propagateUpper D v).StrictlyFeasible Y ↔ D.StrictlyFeasible Y := by
  constructor
  · intro h
    refine ⟨?_, h.2⟩
    intro x
    by_cases hx : x = v
    · subst x
      exact ⟨(h.1 v).1, lt_of_lt_of_le
        (by simpa [propagateUpper] using (h.1 v).2)
        (conditionalUpper_le_upper D v D.upper)⟩
    · simpa [propagateUpper, Function.update_of_ne hx] using h.1 x
  · intro h
    refine ⟨?_, h.2⟩
    intro x
    by_cases hx : x = v
    · subst x
      constructor
      · exact (h.1 v).1
      · simp only [propagateUpper, Function.update_self]
        apply (Finset.lt_fold_min _).mpr
        refine ⟨(h.1 v).2, ?_⟩
        intro u hu
        exact (h.2 v u (by simpa using hu)).trans (h.1 u).2
    · simpa [propagateUpper, Function.update_of_ne hx] using h.1 x

/-- The two endpoint-propagation passes of `Normalize`.  Correctness as a set
transformation holds for every order; topological order is used to establish
that the resulting endpoints are canonical. -/
def normalize (D : System ι K) (order : List ι) : System ι K :=
  order.reverse.foldl propagateUpper (order.foldl propagateLower D)

theorem normalize_feasible_iff (D : System ι K) (order : List ι) (Y : ι → K) :
    (normalize D order).StrictlyFeasible Y ↔ D.StrictlyFeasible Y := by
  have hlo : ∀ (l : List ι) (D : System ι K),
      (l.foldl propagateLower D).StrictlyFeasible Y ↔ D.StrictlyFeasible Y := by
    intro l
    induction l with
    | nil => intro D; rfl
    | cons v l ih =>
      intro D
      exact (ih (propagateLower D v)).trans (propagateLower_feasible_iff D v Y)
  have hhi : ∀ (l : List ι) (D : System ι K),
      (l.foldl propagateUpper D).StrictlyFeasible Y ↔ D.StrictlyFeasible Y := by
    intro l
    induction l with
    | nil => intro D; rfl
    | cons v l ih =>
      intro D
      exact (ih (propagateUpper D v)).trans (propagateUpper_feasible_iff D v Y)
  exact (hhi order.reverse _).trans (hlo order D)

/-- Strictly increasing interpolation parameters produce a feasible assignment
whenever normalized intervals have positive width. -/
theorem interpolate_feasible (D : System ι K) (hD : Normalized D)
    (hw : ∀ x, D.lower x < D.upper x)
    (θ : ι → K) (hθ : ∀ x, 0 < θ x ∧ θ x < 1)
    (horder : ∀ x y, D.edge x y = true → θ x < θ y) :
    D.StrictlyFeasible (fun x => (1 - θ x) * D.lower x + θ x * D.upper x) := by
  constructor
  · intro x
    have h₁ := mul_pos (hθ x).1 (sub_pos.mpr (hw x))
    have h₂ := mul_pos (sub_pos.mpr (hθ x).2) (sub_pos.mpr (hw x))
    constructor <;> nlinarith
  · intro x y hxy
    have hdiff := mul_pos (sub_pos.mpr (horder x y hxy)) (sub_pos.mpr (hw x))
    have hlo := mul_le_mul_of_nonneg_left (hD x y hxy).1
      (sub_nonneg.mpr (hθ y).2.le)
    have hhi := mul_le_mul_of_nonneg_left (hD x y hxy).2 (hθ y).1.le
    nlinarith

/-- A topological numbering supplies explicit increasing parameters in `(0,1)`.
No nonempty-coordinate assumption is needed. -/
theorem feasible_of_normalized (D : System ι K) (hD : Normalized D)
    (hw : ∀ x, D.lower x < D.upper x)
    {n : ℕ} (rank : ι → Fin n)
    (horder : ∀ x y, D.edge x y = true → rank x < rank y) :
    ∃ Y, D.StrictlyFeasible Y := by
  let θ : ι → K := fun x => ((rank x).val + 1 : K) / (n + 1 : K)
  refine ⟨_, interpolate_feasible D hD hw θ ?_ ?_⟩
  · intro x
    have hn : (0 : K) < n + 1 := by positivity
    constructor
    · exact div_pos (by positivity) hn
    · apply (div_lt_one hn).mpr
      have hx : ((rank x).val : K) < n := by exact_mod_cast (rank x).isLt
      linarith
  · intro x y hxy
    apply (div_lt_div_iff_of_pos_right (by positivity : (0 : K) < n + 1)).mpr
    have hxy' : ((rank x).val : K) < (rank y).val := by
      exact_mod_cast (horder x y hxy)
    linarith

/-- Around any prescribed parameter at a selected vertex, a sufficiently small
linear perturbation by topological rank keeps all parameters in `(0,1)`. -/
theorem exists_parameters_through {n : ℕ} (rank : ι → Fin n) (x : ι)
    (t : K) (ht : 0 < t ∧ t < 1) :
    ∃ θ : ι → K, (∀ y, 0 < θ y ∧ θ y < 1) ∧ θ x = t ∧
      ∀ y z, rank y < rank z → θ y < θ z := by
  let e : K := min t (1 - t) / (2 * (n + 1 : K))
  have hn : (0 : K) < n + 1 := by positivity
  have hmin : 0 < min t (1 - t) := lt_min ht.1 (sub_pos.mpr ht.2)
  have he : 0 < e := div_pos hmin (mul_pos (by norm_num) hn)
  have heq : e * (2 * (n + 1 : K)) = min t (1 - t) := by
    dsimp [e]
    exact div_mul_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) hn))
  have he₁ : e * (n : K) < t := by
    have := min_le_left t (1 - t)
    have heN : 0 ≤ e * (n : K) := mul_nonneg he.le (Nat.cast_nonneg _)
    nlinarith
  have he₂ : e * (n : K) < 1 - t := by
    have := min_le_right t (1 - t)
    have heN : 0 ≤ e * (n : K) := mul_nonneg he.le (Nat.cast_nonneg _)
    nlinarith
  refine ⟨fun y => t + e * ((rank y).val - (rank x).val : K), ?_, by simp, ?_⟩
  · intro y
    have hx : ((rank x).val : K) < n := by exact_mod_cast (rank x).isLt
    have hy : ((rank y).val : K) < n := by exact_mod_cast (rank y).isLt
    have hx0 : (0 : K) ≤ (rank x).val := Nat.cast_nonneg _
    have hy0 : (0 : K) ≤ (rank y).val := Nat.cast_nonneg _
    have hlo := mul_le_mul_of_nonneg_left
      (show -(n : K) ≤ ((rank y).val - (rank x).val : K) by linarith) he.le
    have hhi := mul_le_mul_of_nonneg_left
      (show ((rank y).val - (rank x).val : K) ≤ (n : K) by linarith) he.le
    constructor <;> nlinarith
  · intro y z hyz
    have hyz' : ((rank y).val : K) < (rank z).val := by exact_mod_cast hyz
    have := mul_pos he (sub_pos.mpr hyz')
    nlinarith

/-- Every point of a normalized interval occurs in a strictly feasible
assignment. This is the paper's canonical-coordinate statement. -/
theorem projection_eq_interval (D : System ι K) (hD : Normalized D)
    (hw : ∀ x, D.lower x < D.upper x)
    {n : ℕ} (rank : ι → Fin n)
    (horder : ∀ x y, D.edge x y = true → rank x < rank y)
    (x : ι) (c : K) :
    (∃ Y, D.StrictlyFeasible Y ∧ Y x = c) ↔
      D.lower x < c ∧ c < D.upper x := by
  constructor
  · rintro ⟨Y, hY, rfl⟩
    exact hY.1 x
  · intro hc
    let t : K := (c - D.lower x) / (D.upper x - D.lower x)
    have hwx : 0 < D.upper x - D.lower x := sub_pos.mpr (hw x)
    have ht : 0 < t ∧ t < 1 := by
      constructor
      · exact div_pos (sub_pos.mpr hc.1) hwx
      · exact (div_lt_one hwx).mpr (by linarith)
    obtain ⟨θ, hθ, hθx, hθorder⟩ := exists_parameters_through rank x t ht
    refine ⟨_, interpolate_feasible D hD hw θ hθ
      (fun y z hyz => hθorder y z (horder y z hyz)), ?_⟩
    rw [hθx]
    dsimp [t]
    field_simp [hwx.ne']
    <;> ring

/-- Surviving coordinates when `x` has been fixed and deleted. -/
abbrev Remaining (x : ι) := {y : ι // y ≠ x}

/-- Restore the removed coordinate to its specified value. -/
def restore (x : ι) (c : K) (Y : Remaining x → K) : ι → K :=
  fun y => if h : y = x then c else Y ⟨y, h⟩

@[simp] theorem restore_self (x : ι) (c : K) (Y : Remaining x → K) :
    restore x c Y x = c := by simp [restore]

@[simp] theorem restore_remaining (x : ι) (c : K) (Y : Remaining x → K)
    (y : Remaining x) : restore x c Y y = Y y := by simp [restore, y.property]

/-- The literal `Restrict` operation before endpoint normalization: incident
arcs become bounds, and all other arcs survive. -/
def restrictAt (D : System ι K) (x : ι) (c : K) : System (Remaining x) K where
  lower y := if D.edge x y then max (D.lower y) c else D.lower y
  upper y := if D.edge y x then min (D.upper y) c else D.upper y
  edge y z := D.edge y z

/-- Restriction is exactly a coordinate section, rather than merely an
inclusion in that section. -/
theorem restrictAt_feasible_iff (D : System ι K) (x : ι) (c : K)
    (hxx : D.edge x x = false) (hc : D.lower x < c ∧ c < D.upper x)
    (Y : Remaining x → K) :
    (restrictAt D x c).StrictlyFeasible Y ↔ D.StrictlyFeasible (restore x c Y) := by
  constructor
  · intro hY
    constructor
    · intro y
      by_cases hy : y = x
      · subst y
        simpa using hc
      · let z : Remaining x := ⟨y, hy⟩
        have hz := hY.1 z
        have hl : D.lower y < Y z := by
          exact lt_of_le_of_lt (by dsimp [restrictAt, z]; split <;> simp) hz.1
        have hu : Y z < D.upper y := by
          exact lt_of_lt_of_le hz.2 (by dsimp [restrictAt, z]; split <;> simp)
        simpa [restore, hy, z] using And.intro hl hu
    · intro y z hyz
      by_cases hy : y = x
      · subst y
        have hz : z ≠ x := by intro h; subst z; simp [hxx] at hyz
        have h := (hY.1 ⟨z, hz⟩).1
        have h' : max (D.lower z) c < Y ⟨z, hz⟩ := by simpa [restrictAt, hyz] using h
        have hc' : c < Y ⟨z, hz⟩ := by
          exact lt_of_le_of_lt (le_max_right (D.lower z) c) h'
        simpa [restore, hz] using hc'
      · by_cases hz : z = x
        · subst z
          have h := (hY.1 ⟨y, hy⟩).2
          have h' : Y ⟨y, hy⟩ < min (D.upper y) c := by simpa [restrictAt, hyz] using h
          have hc' : Y ⟨y, hy⟩ < c := by
            exact lt_of_lt_of_le h' (min_le_right (D.upper y) c)
          simpa [restore, hy] using hc'
        · have h := hY.2 ⟨y, hy⟩ ⟨z, hz⟩ hyz
          simpa [restore, hy, hz] using h
  · intro hY
    constructor
    · intro y
      have hy := hY.1 y
      constructor
      · dsimp [restrictAt]
        split_ifs with hxy
        · apply max_lt
          · simpa using hy.1
          · have h := hY.2 x y hxy
            simpa using h
        · simpa using hy.1
      · dsimp [restrictAt]
        split_ifs with hyx
        · apply lt_min
          · simpa using hy.2
          · have h := hY.2 y x hyx
            simpa using h
        · simpa using hy.2
    · intro y z hyz
      have h := hY.2 y z hyz
      simpa using h

/-- A feasible full assignment with `X x = c` restricts to a feasible section. -/
theorem restrictAt_feasible_of_full (D : System ι K) (x : ι) (c : K)
    (hxx : D.edge x x = false) (X : ι → K) (hX : D.StrictlyFeasible X)
    (hxc : X x = c) :
    (restrictAt D x c).StrictlyFeasible (fun y => X y) := by
  apply (restrictAt_feasible_iff D x c hxx (hxc ▸ hX.1 x) _).mpr
  have heq : restore x c (fun y : Remaining x => X y) = X := by
    funext y
    by_cases hy : y = x
    · subst y
      simpa using hxc.symm
    · simp [restore, hy]
  rwa [heq]

/-- Directed reachability, including the vertex itself. -/
def Reaches (D : System ι K) (x y : ι) : Prop :=
  Relation.ReflTransGen (fun u v => D.edge u v = true) x y

/-- Raising coordinates on an upward-closed subset by a second feasible
assignment preserves every strict constraint. -/
theorem feasible_splice_max (D : System ι K) (U : ι → Prop) [DecidablePred U]
    (hU : ∀ x y, U x → D.edge x y = true → U y)
    {A B : ι → K} (hA : D.StrictlyFeasible A) (hB : D.StrictlyFeasible B) :
    D.StrictlyFeasible (fun y => if U y then max (A y) (B y) else A y) := by
  constructor
  · intro y
    by_cases hy : U y
    · simp only [if_pos hy]
      exact ⟨(hA.1 y).1.trans_le (le_max_left _ _), max_lt (hA.1 y).2 (hB.1 y).2⟩
    · simpa only [if_neg hy] using hA.1 y
  · intro x y hxy
    by_cases hx : U x
    · have hy := hU x y hx hxy
      simp only [if_pos hx, if_pos hy]
      exact max_lt_max (hA.2 x y hxy) (hB.2 x y hxy)
    · by_cases hy : U y
      · simp only [if_neg hx, if_pos hy]
        exact (hA.2 x y hxy).trans_le (le_max_left _ _)
      · simpa only [if_neg hx, if_neg hy] using hA.2 x y hxy

/-- The dual operation lowers a downward-closed subset. -/
theorem feasible_splice_min (D : System ι K) (U : ι → Prop) [DecidablePred U]
    (hU : ∀ x y, U y → D.edge x y = true → U x)
    {A B : ι → K} (hA : D.StrictlyFeasible A) (hB : D.StrictlyFeasible B) :
    D.StrictlyFeasible (fun y => if U y then min (A y) (B y) else A y) := by
  constructor
  · intro y
    by_cases hy : U y
    · simp only [if_pos hy]
      exact ⟨lt_min (hA.1 y).1 (hB.1 y).1, (min_le_left _ _).trans_lt (hA.1 y).2⟩
    · simpa only [if_neg hy] using hA.1 y
  · intro x y hxy
    by_cases hy : U y
    · have hx := hU x y hy hxy
      simp only [if_pos hx, if_pos hy]
      exact min_lt_min (hA.2 x y hxy) (hB.2 x y hxy)
    · by_cases hx : U x
      · simp only [if_pos hx, if_neg hy]
        exact (min_le_left _ _).trans_lt (hA.2 x y hxy)
      · simpa only [if_neg hx, if_neg hy] using hA.2 x y hxy

/-- Conditioning on all coordinates incomparable with `x` leaves its full
canonical interval unchanged. The witness is constructed by a lattice splice,
so no conditional-projection assertion is assumed. -/
theorem projection_preserving_incomparables (D : System ι K) (hD : Normalized D)
    (hw : ∀ y, D.lower y < D.upper y)
    {n : ℕ} (rank : ι → Fin n)
    (horder : ∀ y z, D.edge y z = true → rank y < rank z)
    (A : ι → K) (hA : D.StrictlyFeasible A) (x : ι) (c : K)
    (hc : D.lower x < c ∧ c < D.upper x) :
    ∃ X, D.StrictlyFeasible X ∧ X x = c ∧
      ∀ y, ¬ Reaches D x y → ¬ Reaches D y x → X y = A y := by
  classical
  obtain ⟨B, hB, hBx⟩ := (projection_eq_interval D hD hw rank horder x c).mpr hc
  rcases le_total (A x) c with hAc | hcA
  · let U := Reaches D x
    let X : ι → K := fun y => if U y then max (A y) (B y) else A y
    refine ⟨X, feasible_splice_max D U ?_ hA hB, ?_, ?_⟩
    · intro y z hy hyz
      exact hy.tail hyz
    · have hx : U x := Relation.ReflTransGen.refl
      simp [X, hx, hBx, max_eq_right hAc]
    · intro y hxy _
      simp only [X, U, if_neg hxy]
  · let U := fun y => Reaches D y x
    let X : ι → K := fun y => if U y then min (A y) (B y) else A y
    refine ⟨X, feasible_splice_min D U ?_ hA hB, ?_, ?_⟩
    · intro y z hz hyz
      exact hz.head hyz
    · have hx : U x := Relation.ReflTransGen.refl
      simp [X, hx, hBx, min_eq_right hcA]
    · intro y _ hyx
      simp only [X, U, if_neg hyx]

end Algebra

section Geometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The genuine open order region in Euclidean coordinate space. -/
def region (D : System ι ℝ) : Set (ι → ℝ) := {X | D.StrictlyFeasible X}

@[simp] theorem normalize_region (D : System ι ℝ) (order : List ι) :
    region (normalize D order) = region D := by
  ext X
  exact normalize_feasible_iff D order X

theorem region_open (D : System ι ℝ) : IsOpen (region D) := by
  have heq : region D =
      (⋂ x, {X | D.lower x < X x} ∩ {X | X x < D.upper x}) ∩
      (⋂ x, ⋂ y, {X | D.edge x y = true → X x < X y}) := by
    ext X
    simp [region, System.StrictlyFeasible]
  rw [heq]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro x
    exact (isOpen_lt continuous_const (continuous_apply x)).inter
      (isOpen_lt (continuous_apply x) continuous_const)
  · apply isOpen_iInter_of_finite
    intro x
    apply isOpen_iInter_of_finite
    intro y
    by_cases hxy : D.edge x y = true
    · simpa [hxy] using isOpen_lt (continuous_apply x) (continuous_apply y)
    · simp [hxy]

theorem region_convex (D : System ι ℝ) : Convex ℝ (region D) := by
  intro X hX Y hY a b ha hb hab
  constructor
  · intro x
    constructor
    · change D.lower x < a * X x + b * Y x
      have := (convex_Ioi (D.lower x)) (hX.1 x).1 (hY.1 x).1 ha hb hab
      simpa using this
    · change a * X x + b * Y x < D.upper x
      have := (convex_Iio (D.upper x)) (hX.1 x).2 (hY.1 x).2 ha hb hab
      simpa using this
  · intro x y hxy
    change a * X x + b * Y x < a * X y + b * Y y
    have h₁ : 0 < X y - X x := sub_pos.mpr (hX.2 x y hxy)
    have h₂ : 0 < Y y - Y x := sub_pos.mpr (hY.2 x y hxy)
    have hpos : 0 < a * (X y - X x) + b * (Y y - Y x) := by
      rcases ha.eq_or_lt with rfl | ha
      · simp only [zero_mul, zero_add] at hab ⊢
        simpa [hab] using h₂
      · exact add_pos_of_pos_of_nonneg (mul_pos ha h₁) (mul_nonneg hb h₂.le)
    linarith

/-- Nonempty open finite-dimensional order regions have positive Lebesgue
volume, including the zero-coordinate case. -/
theorem volume_pos_iff_nonempty (D : System ι ℝ) :
    0 < volume (region D) ↔ (region D).Nonempty :=
  (region_open D).measure_pos_iff volume

/-- The region is contained in its coordinate box. -/
theorem region_subset_box (D : System ι ℝ) :
    region D ⊆ Set.Icc D.lower D.upper := by
  intro X hX
  exact ⟨fun x => (hX.1 x).1.le, fun x => (hX.1 x).2.le⟩

/-- All node volumes are finite; no separate finiteness certificate is needed. -/
theorem volume_ne_top (D : System ι ℝ) : volume (region D) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (measure_mono (region_subset_box D))
  rw [Real.volume_Icc_pi]
  exact ENNReal.prod_ne_top fun x _ => ENNReal.ofReal_ne_top

/-- Unit-bounded node intervals give the required volume bound `V(D) ≤ 1`. -/
theorem volume_le_one (D : System ι ℝ)
    (hl : ∀ x, 0 ≤ D.lower x) (hu : ∀ x, D.upper x ≤ 1) :
    volume (region D) ≤ 1 := by
  have hs : region D ⊆ Set.Icc (fun _ : ι => (0 : ℝ)) (fun _ : ι => (1 : ℝ)) := by
    intro X hX
    exact ⟨fun x => (hl x).trans (hX.1 x).1.le,
      fun x => (hX.1 x).2.le.trans (hu x)⟩
  simpa [Real.volume_Icc_pi] using measure_mono (μ := volume) hs

/-- Positivity is equivalent to positive coordinate widths after normalization
and topological indexing. -/
theorem volume_pos_iff_widths (D : System ι ℝ) (hD : Normalized D)
    {n : ℕ} (rank : ι → Fin n)
    (horder : ∀ x y, D.edge x y = true → rank x < rank y) :
    0 < volume (region D) ↔ ∀ x, D.lower x < D.upper x := by
  rw [volume_pos_iff_nonempty]
  constructor
  · rintro ⟨X, hX⟩ x
    exact (hX.1 x).1.trans (hX.1 x).2
  · intro hw
    exact feasible_of_normalized D hD hw rank horder

/-- Every interior coordinate section has positive volume in its remaining
coordinates. It is not measured as a hyperplane in the original dimension. -/
theorem restriction_volume_pos (D : System ι ℝ) (hD : Normalized D)
    (hw : ∀ x, D.lower x < D.upper x)
    {n : ℕ} (rank : ι → Fin n)
    (horder : ∀ x y, D.edge x y = true → rank x < rank y)
    (x : ι) (c : ℝ) (hc : D.lower x < c ∧ c < D.upper x) :
    0 < volume (region (restrictAt D x c)) := by
  obtain ⟨X, hX, hxc⟩ := (projection_eq_interval D hD hw rank horder x c).mpr hc
  have hxx : D.edge x x = false := by
    cases h : D.edge x x
    · rfl
    · exact (lt_irrefl _ (horder x x h)).elim
  apply (volume_pos_iff_nonempty _).mpr
  exact ⟨_, restrictAt_feasible_of_full D x c hxx X hX hxc⟩

/-- The section is defined by substituting the coordinate in the original
constraints, so it is empty automatically outside that coordinate's range. -/
def sectionAt (D : System ι ℝ) (x : ι) (c : ℝ) : Set (Remaining x → ℝ) :=
  {Y | D.StrictlyFeasible (restore x c Y)}

theorem section_eq_restrictAt (D : System ι ℝ) (x : ι) (c : ℝ)
    (hxx : D.edge x x = false) (hc : D.lower x < c ∧ c < D.upper x) :
    sectionAt D x c = region (restrictAt D x c) := by
  ext Y
  exact (restrictAt_feasible_iff D x c hxx hc Y).symm

theorem section_empty_of_outside (D : System ι ℝ) (x : ι) (c : ℝ)
    (hc : ¬ (D.lower x < c ∧ c < D.upper x)) : sectionAt D x c = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro Y hY
  apply hc
  simpa using hY.1 x

/-- The paper's real-valued node volume. -/
noncomputable def nodeVolume (D : System ι ℝ) : ℝ := (volume (region D)).toReal

@[simp] theorem normalize_nodeVolume (D : System ι ℝ) (order : List ι) :
    nodeVolume (normalize D order) = nodeVolume D := by
  simp only [nodeVolume, normalize_region]

/-- Pointwise section volume in the remaining coordinates. -/
noncomputable def sectionVolume (D : System ι ℝ) (x : ι) (c : ℝ) : ℝ :=
  (volume (sectionAt D x c)).toReal

/-- The coordinate density as defined in the manuscript. Integration of this
pointwise section formula is a separate Fubini statement. -/
noncomputable def density (D : System ι ℝ) (x : ι) (c : ℝ) : ℝ :=
  sectionVolume D x c / nodeVolume D

theorem nodeVolume_pos (D : System ι ℝ) (h : 0 < volume (region D)) :
    0 < nodeVolume D :=
  ENNReal.toReal_pos h.ne' (volume_ne_top D)

theorem nodeVolume_le_one (D : System ι ℝ)
    (hl : ∀ x, 0 ≤ D.lower x) (hu : ∀ x, D.upper x ≤ 1) :
    nodeVolume D ≤ 1 := by
  exact (ENNReal.toReal_le_toReal (volume_ne_top D) ENNReal.one_ne_top).mpr
    (volume_le_one D hl hu)

/-- The restriction-volume equation uses the actual Lebesgue section and its
pointwise density, with positivity discharged from normalized finite data. -/
theorem restriction_volume_identity (D : System ι ℝ) (hD : Normalized D)
    (hw : ∀ x, D.lower x < D.upper x)
    {n : ℕ} (rank : ι → Fin n)
    (horder : ∀ x y, D.edge x y = true → rank x < rank y)
    (x : ι) (c : ℝ) (hc : D.lower x < c ∧ c < D.upper x) :
    nodeVolume (restrictAt D x c) = nodeVolume D * density D x c ∧
      0 < density D x c := by
  have hxx : D.edge x x = false := by
    cases h : D.edge x x
    · rfl
    · exact (lt_irrefl _ (horder x x h)).elim
  have hv := (volume_pos_iff_widths D hD rank horder).mpr hw
  have hvR := restriction_volume_pos D hD hw rank horder x c hc
  have hV := nodeVolume_pos D hv
  have hVR := nodeVolume_pos (restrictAt D x c) hvR
  have hsection : sectionVolume D x c = nodeVolume (restrictAt D x c) := by
    simp only [sectionVolume, nodeVolume, section_eq_restrictAt D x c hxx hc]
  constructor
  · rw [density, hsection]
    field_simp [hV.ne']
  · rw [density, hsection]
    exact div_pos hVR hV

/-- Admitting a fresh child label introduces an independent unit coordinate. -/
def insertIsolated (D : System ι ℝ) : System (Option ι) ℝ where
  lower := Option.elim' 0 D.lower
  upper := Option.elim' 1 D.upper
  edge x y := match x, y with
    | some x, some y => D.edge x y
    | _, _ => false

theorem insertIsolated_feasible_iff (D : System ι ℝ) (Y : Option ι → ℝ) :
    (insertIsolated D).StrictlyFeasible Y ↔
      D.StrictlyFeasible (fun x => Y (some x)) ∧ 0 < Y none ∧ Y none < 1 := by
  constructor
  · intro h
    refine ⟨⟨fun x => h.1 (some x), fun x y hxy => h.2 (some x) (some y) hxy⟩,
      h.1 none⟩
  · rintro ⟨h, hnone⟩
    constructor
    · intro x
      cases x with
      | none => exact hnone
      | some x => exact h.1 x
    · intro x y hxy
      cases x with
      | none => simp [insertIsolated] at hxy
      | some x =>
        cases y with
        | none => simp [insertIsolated] at hxy
        | some y => exact h.2 x y hxy

/-- Adding the independent unit coordinate leaves the volume unchanged,
including when the old child has no coordinates. -/
theorem insertIsolated_volume (D : System ι ℝ) :
    volume (region (insertIsolated D)) = volume (region D) := by
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)
  have hm : (volume.prod volume).map e.symm =
      (volume : Measure (Option ι → ℝ)) := by
    exact Measure.pi_map_piOptionEquivProd (fun _ : Option ι => (volume : Measure ℝ))
  have hs : e.symm ⁻¹' region (insertIsolated D) = region D ×ˢ Ioo (0 : ℝ) 1 := by
    ext p
    have hSome : (fun x => e.symm p (some x)) = p.1 := rfl
    have hNone : e.symm p none = p.2 := rfl
    simpa only [mem_preimage, mem_prod, mem_Ioo, region, mem_setOf_eq, hSome, hNone] using
      insertIsolated_feasible_iff D (e.symm p)
  rw [← hm, e.symm.measurableEmbedding.map_apply, hs, Measure.prod_prod]
  simp

@[simp] theorem insertIsolated_nodeVolume (D : System ι ℝ) :
    nodeVolume (insertIsolated D) = nodeVolume D := by
  simp only [nodeVolume, insertIsolated_volume]

end Geometry

end SortingAdversary.Continuous.OrderRegion
