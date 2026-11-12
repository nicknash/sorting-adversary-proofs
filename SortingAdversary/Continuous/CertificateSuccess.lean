import SortingAdversary.Continuous.EnclosureGuarantee
import SortingAdversary.Continuous.EnclosureCoupling
import SortingAdversary.Continuous.LocalSelection
import SortingAdversary.Continuous.SmallDifference

/-!
# Success of the actual calibrated interval certificates

The list counts below are those computed by `Enclose`. Narrow unresolved
entries certify a small-difference event under the actual uniform region
measure. The geometric density bound and the calibrated bad-width fraction
therefore force the comparison and central-interval routines to succeed.
-/

namespace SortingAdversary.Continuous.CertificateSuccess

open FiniteAveraging Certificates EnclosureParameters LocalSelection
open OrderRegion MeasureTheory Set

private theorem countP_split {α : Type*} (L : List α) (P bad : α → Bool) :
    L.countP P ≤ L.countP bad + L.countP (fun x => !bad x && P x) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    cases hb : bad a <;> cases hp : P a <;> simp_all <;> omega

private theorem comparison_cover {α : Type*} (L : List α) (p q bad : α → Bool) :
    L.length ≤ L.countP p + L.countP q + L.countP bad +
      L.countP (fun x => !bad x && !(p x || q x)) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    cases hb : bad a <;> cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

variable {n : ℕ}

theorem good_width {Q : Finset (Fin n)} {δ : ℚ} {I : Fin n → ℚ × ℚ}
    (hgood : badWidth Q δ I = false) {x : Fin n} (hx : x ∈ Q) :
    (I x).2 - (I x).1 ≤ δ := by
  have h := of_decide_eq_false hgood
  exact le_of_not_gt (fun hwidth => h ⟨x, hx, hwidth⟩)

def narrowUnresolved (Q : Finset (Fin n)) (δ : ℚ) (x y : Fin n)
    (I : Fin n → ℚ × ℚ) : Bool :=
  !badWidth Q δ I && !(separated (I x, I y) || reverseSeparated (I x, I y))

def narrowCrossing (Q : Finset (Fin n)) (δ : ℚ) (x : Fin n) (c : ℚ)
    (I : Fin n → ℚ × ℚ) : Bool :=
  !badWidth Q δ I && decide ((I x).1 ≤ c ∧ c ≤ (I x).2)

theorem narrowUnresolved_sound (Q : Finset (Fin n)) (δ : ℚ) (x y : Fin n)
    (hx : x ∈ Q) (hy : y ∈ Q) (I : Fin n → ℚ × ℚ)
    (hI : narrowUnresolved Q δ x y I = true) (X : Fin n → ℝ)
    (hX : ∀ z, ((I z).1 : ℝ) ≤ X z ∧ X z ≤ ((I z).2 : ℝ)) :
    X x - X y ∈ Icc (-(2 * (δ : ℝ))) (2 * (δ : ℝ)) := by
  have hI' : badWidth Q δ I = false ∧ separated (I x, I y) = false ∧
      reverseSeparated (I x, I y) = false := by
    simpa only [narrowUnresolved, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false,
      Bool.or_eq_false_iff] using hI
  exact abs_le.mp (unresolved_close (I := (I x, I y)) (hX x) (hX y)
    (good_width hI'.1 hx) (good_width hI'.1 hy) hI'.2.1 hI'.2.2)

theorem narrowCrossing_sound (Q : Finset (Fin n)) (δ : ℚ) (x : Fin n)
    (hx : x ∈ Q) (c : ℚ) (I : Fin n → ℚ × ℚ)
    (hI : narrowCrossing Q δ x c I = true) (X : Fin n → ℝ)
    (hX : ∀ z, ((I z).1 : ℝ) ≤ X z ∧ X z ≤ ((I z).2 : ℝ)) :
    X x - (c : ℝ) ∈ Icc (-(δ : ℝ)) (δ : ℝ) := by
  have hI' : badWidth Q δ I = false ∧ (I x).1 ≤ c ∧ c ≤ (I x).2 := by
    simpa only [narrowCrossing, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, decide_eq_true_eq] using hI
  have hw : ((I x).2 : ℝ) - (I x).1 ≤ δ := by exact_mod_cast good_width hI'.1 hx
  have hc₁ : ((I x).1 : ℝ) ≤ c := by exact_mod_cast hI'.2.1
  have hc₂ : (c : ℝ) ≤ (I x).2 := by exact_mod_cast hI'.2.2
  constructor <;> linarith [hX x]

theorem enclose_valid (D : System (Fin n) ℚ) (S : ℕ) (schedule : List (Fin n))
    (hw : ∀ x, D.lower x ≤ D.upper x) :
    ∀ I ∈ enclose D S schedule, ∀ x, (I x).1 ≤ (I x).2 := by
  intro I hI x
  obtain ⟨digits, _, rfl⟩ := List.mem_map.mp hI
  exact fullSteps_mono D S (assignedSteps S schedule digits) hw x

theorem comparison_mass (D : System (Fin n) ℚ) (S : ℕ) (hS : 0 < S)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (hD : Normalized D.toReal) (schedule : List (Fin n))
    (Q : Finset (Fin n)) (x y : Fin n) (hx : x ∈ Q) (hy : y ∈ Q) (hne : x ≠ y)
    (B : ℕ) (hB : ComparableDensity.comparableCount D.toReal x ≤ B)
    (hw : D.lower x < D.upper x) (δ α : ℚ) (hδ : 0 ≤ δ)
    (hbad : ((enclose D S schedule).countP (badWidth Q δ) : ℚ) /
      (enclose D S schedule).length ≤ α) :
    1 - (α + 4 * (B + 1 : ℚ) * δ / (D.upper x - D.lower x)) ≤
      lowerFraction (comparisonList D S schedule x y) +
      upperFraction (comparisonList D S schedule x y) := by
  let L := enclose D S schedule
  have hN : (0 : ℝ) < L.length := by
    dsimp only [L]
    rw [enclose_length]
    positivity
  have hδR : (0 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hwR : D.toReal.lower x < D.toReal.upper x := by
    change (D.lower x : ℝ) < D.upper x
    exact_mod_cast hw
  have hnear := EnclosureCoupling.enclosure_probability_real D S hS hloop hV schedule
    (narrowUnresolved Q δ x y) {X | X x - X y ∈ Icc (-(2 * (δ : ℝ))) (2 * (δ : ℝ))}
    (measurableSet_Icc.preimage ((measurable_pi_apply x).sub (measurable_pi_apply y)))
    (narrowUnresolved_sound Q δ x y hx hy)
  have hgap := SmallDifference.difference_probability_le D.toReal hD x y hne B hB hwR
    (nodeVolume_pos D.toReal hV) (show -(2 * (δ : ℝ)) ≤ 2 * (δ : ℝ) by linarith)
  have hnarrow : (L.countP (narrowUnresolved Q δ x y) : ℝ) / L.length ≤
      ((4 * (B + 1 : ℚ) * δ / (D.upper x - D.lower x) : ℚ) : ℝ) := by
    calc
      _ ≤ _ := hnear.trans hgap
      _ = _ := by push_cast; dsimp only [System.toReal]; ring
  have hcover := comparison_cover L (fun I => separated (I x, I y))
    (fun I => reverseSeparated (I x, I y)) (badWidth Q δ)
  have hcoverR : (L.length : ℝ) ≤ (L.countP (fun I => separated (I x, I y)) : ℝ) +
      (L.countP (fun I => reverseSeparated (I x, I y)) : ℝ) +
      (L.countP (badWidth Q δ) : ℝ) + (L.countP (narrowUnresolved Q δ x y) : ℝ) := by
    exact_mod_cast hcover
  have hc := div_le_div_of_nonneg_right hcoverR hN.le
  rw [div_self hN.ne', add_div, add_div, add_div] at hc
  have hb : (L.countP (badWidth Q δ) : ℝ) / L.length ≤ (α : ℝ) := by
    have hb' := (Rat.cast_le (K := ℝ)).2 hbad
    simpa only [Rat.cast_div, Rat.cast_natCast, L] using hb'
  have hreal : (1 : ℝ) - ((α : ℝ) +
      ((4 * (B + 1 : ℚ) * δ / (D.upper x - D.lower x) : ℚ) : ℝ)) ≤
      (L.countP (fun I => separated (I x, I y)) : ℝ) / L.length +
      (L.countP (fun I => reverseSeparated (I x, I y)) : ℝ) / L.length := by linarith
  simpa only [lowerFraction, upperFraction, comparisonList, List.countP_map,
    List.length_map, Function.comp_def, L] using (show
      (1 : ℚ) - (α + 4 * (B + 1 : ℚ) * δ / (D.upper x - D.lower x)) ≤
        (L.countP (fun I => separated (I x, I y)) : ℚ) / L.length +
        (L.countP (fun I => reverseSeparated (I x, I y)) : ℚ) / L.length by
        apply (Rat.cast_le (K := ℝ)).mp
        push_cast at hreal ⊢
        exact hreal)

theorem crossing_fraction (D : System (Fin n) ℚ) (S : ℕ) (hS : 0 < S)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (hD : Normalized D.toReal) (schedule : List (Fin n))
    (Q : Finset (Fin n)) (x : Fin n) (hx : x ∈ Q)
    (B : ℕ) (hB : ComparableDensity.comparableCount D.toReal x ≤ B)
    (hw : D.lower x < D.upper x) (δ α : ℚ) (hδ : 0 ≤ δ)
    (hbad : ((enclose D S schedule).countP (badWidth Q δ) : ℚ) /
      (enclose D S schedule).length ≤ α) (c : ℚ) :
    (crossingCount ((enclose D S schedule).map (fun I => I x)) c : ℚ) /
      (enclose D S schedule).length ≤
        α + 2 * (B + 1 : ℚ) * δ / (D.upper x - D.lower x) := by
  let L := enclose D S schedule
  have hN : (0 : ℝ) < L.length := by
    dsimp only [L]
    rw [enclose_length]
    positivity
  have hδR : (0 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hwR : D.toReal.lower x < D.toReal.upper x := by
    change (D.lower x : ℝ) < D.upper x
    exact_mod_cast hw
  have hnear := EnclosureCoupling.enclosure_probability_real D S hS hloop hV schedule
    (narrowCrossing Q δ x c) {X | X x - (c : ℝ) ∈ Icc (-(δ : ℝ)) (δ : ℝ)}
    (measurableSet_Icc.preimage (show Measurable (fun X : Fin n → ℝ => X x - (c : ℝ)) from
      (measurable_pi_apply x).sub measurable_const))
    (narrowCrossing_sound Q δ x hx c)
  have hgap := SmallDifference.fixed_probability_le D.toReal hD x B hB hwR
    (nodeVolume_pos D.toReal hV) c (show -(δ : ℝ) ≤ (δ : ℝ) by linarith)
  have hnarrow : (L.countP (narrowCrossing Q δ x c) : ℝ) / L.length ≤
      ((2 * (B + 1 : ℚ) * δ / (D.upper x - D.lower x) : ℚ) : ℝ) := by
    calc
      _ ≤ _ := hnear.trans hgap
      _ = _ := by push_cast; dsimp only [System.toReal]; ring
  have hcount := countP_split L (fun I => decide ((I x).1 ≤ c ∧ c ≤ (I x).2)) (badWidth Q δ)
  have hcountR : (L.countP (fun I => decide ((I x).1 ≤ c ∧ c ≤ (I x).2)) : ℝ) ≤
      (L.countP (badWidth Q δ) : ℝ) + (L.countP (narrowCrossing Q δ x c) : ℝ) := by
    exact_mod_cast hcount
  have hc := div_le_div_of_nonneg_right hcountR hN.le
  rw [add_div] at hc
  have hb : (L.countP (badWidth Q δ) : ℝ) / L.length ≤ (α : ℝ) := by
    have hb' := (Rat.cast_le (K := ℝ)).2 hbad
    simpa only [Rat.cast_div, Rat.cast_natCast, L] using hb'
  have hreal : (L.countP (fun I => decide ((I x).1 ≤ c ∧ c ≤ (I x).2)) : ℝ) / L.length ≤
      (α : ℝ) + ((2 * (B + 1 : ℚ) * δ / (D.upper x - D.lower x) : ℚ) : ℝ) := by linarith
  simpa only [crossingCount, List.countP_map, Function.comp_def, L] using (show
    (L.countP (fun I => decide ((I x).1 ≤ c ∧ c ≤ (I x).2)) : ℚ) / L.length ≤
      α + 2 * (B + 1 : ℚ) * δ / (D.upper x - D.lower x) by
        apply (Rat.cast_le (K := ℝ)).mp
        push_cast at hreal ⊢
        exact hreal)

def error (k : ℕ) : ℚ := 1 / (100 * (k : ℚ))

def failure (k : ℕ) : ℚ := error k / 2

def accuracy (k B : ℕ) (w : ℚ) : ℚ := error k * w / (8 * (B + 1 : ℚ))

theorem error_pos {k : ℕ} (hk : 0 < k) : 0 < error k := by
  have hk' : (0 : ℚ) < k := by exact_mod_cast hk
  unfold error
  positivity

theorem failure_pos {k : ℕ} (hk : 0 < k) : 0 < failure k := by
  unfold failure
  exact div_pos (error_pos hk) (by norm_num)

theorem accuracy_pos {k : ℕ} (hk : 0 < k) (B : ℕ) {w : ℚ} (hw : 0 < w) :
    0 < accuracy k B w := by
  unfold accuracy
  exact div_pos (mul_pos (error_pos hk) hw) (by positivity)

theorem comparison_error_le {k : ℕ} (hk : 0 < k) (B : ℕ) {w W : ℚ}
    (hw : 0 < w) (hW : w ≤ W) :
    failure k + 4 * (B + 1 : ℚ) * accuracy k B w / W ≤ error k := by
  calc
    _ ≤ failure k + 4 * (B + 1 : ℚ) * accuracy k B w / w := by
      apply add_le_add le_rfl
      exact div_le_div_of_nonneg_left (by have ha := accuracy_pos hk B hw; positivity) hw hW
    _ = error k := by
      exact (calibration (η := error k) (w := w) (B := (B : ℚ)) hw (by positivity)).1

theorem crossing_error_le {k : ℕ} (hk : 0 < k) (B : ℕ) {w W : ℚ}
    (hw : 0 < w) (hW : w ≤ W) :
    failure k + 2 * (B + 1 : ℚ) * accuracy k B w / W ≤ 3 * error k / 4 := by
  calc
    _ ≤ failure k + 2 * (B + 1 : ℚ) * accuracy k B w / w := by
      apply add_le_add le_rfl
      exact div_le_div_of_nonneg_left (by have ha := accuracy_pos hk B hw; positivity) hw hW
    _ = 3 * error k / 4 := by
      exact (calibration (η := error k) (w := w) (B := (B : ℚ)) hw (by positivity)).2

theorem crossing_error_small {k : ℕ} (hk : 0 < k) : 3 * error k / 4 ≤ 1 / 8 := by
  have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have hη : error k ≤ 1 / 100 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  linarith

/-- The schedule used by both finite tests at fixed certificate parameters. -/
def certificateSchedule (D : System (Fin n) ℚ) (k H B : ℕ) (hk : 0 < k)
    (w : ℚ) (hw : 0 < w) (Q : Finset (Fin n)) : List (Fin n) :=
  calibratedSchedule D k H Q (accuracy k B w) (failure k)
    (accuracy_pos hk B hw) (failure_pos hk)

private theorem no_self_loop (D : System (Fin n) ℚ)
    (horder : ∀ x y, D.edge x y = true → x.val < y.val) :
    ∀ x, D.edge x x = false := by
  intro x
  apply Bool.eq_false_iff.mpr
  exact fun h => Nat.lt_irrefl _ (horder x x h)

theorem certificate_bad_width (D : System (Fin n) ℚ)
    (horder : ∀ x y, D.edge x y = true → x.val < y.val)
    (hwidth : ∀ x, D.lower x ≤ D.upper x) (hunit : ∀ x, D.upper x - D.lower x ≤ 1)
    (rank : Fin n → ℕ) (k H B : ℕ) (hk : 0 < k)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (SortingAdversary.Optimal.GraphBalls.neighbors D.edge x).card ≤ k)
    (w : ℚ) (hw : 0 < w) (Q : Finset (Fin n)) (hQ : Q.card ≤ 2) :
    ((enclose D (alphabet k H) (certificateSchedule D k H B hk w hw Q)).countP
      (badWidth Q (accuracy k B w)) : ℚ) /
      (enclose D (alphabet k H) (certificateSchedule D k H B hk w hw Q)).length ≤ failure k := by
  simpa only [certificateSchedule, calibratedEnclose_eq_enclose] using
    calibratedEnclose_width_probability D horder hwidth hunit rank k H hrank hheight hdegree Q hQ
      (accuracy k B w) (failure k) (accuracy_pos hk B hw) (failure_pos hk)

/-- If either queried coordinate is wide, the actual finite comparison
routine returns an answer. The list estimate is derived, not supplied. -/
theorem comparison_succeeds (D : System (Fin n) ℚ)
    (hD : Normalized D.toReal) (hV : 0 < volume (region D.toReal))
    (horder : ∀ x y, D.edge x y = true → x.val < y.val)
    (hwidth : ∀ x, D.lower x ≤ D.upper x) (hunit : ∀ x, D.upper x - D.lower x ≤ 1)
    (rank : Fin n → ℕ) (k H B : ℕ) (hk : 0 < k)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (SortingAdversary.Optimal.GraphBalls.neighbors D.edge x).card ≤ k)
    (x y : Fin n) (hne : x ≠ y)
    (hBx : ComparableDensity.comparableCount D.toReal x ≤ B)
    (hBy : ComparableDensity.comparableCount D.toReal y ≤ B)
    (w : ℚ) (hw : 0 < w)
    (hwide : w ≤ D.upper x - D.lower x ∨ w ≤ D.upper y - D.lower y) :
    ∃ a, selectAnswer k (comparisonList D (alphabet k H)
      (certificateSchedule D k H B hk w hw {x, y}) x y) = some a := by
  let schedule := certificateSchedule D k H B hk w hw {x, y}
  have hbad := certificate_bad_width D horder hwidth hunit rank k H B hk hrank hheight hdegree
    w hw {x, y} (by simp [hne])
  have hS := EnclosureParameters.alphabet_pos k H
  apply selectAnswer_succeeds
  · have hlen : 0 < (comparisonList D (alphabet k H) schedule x y).length := by
      simp only [comparisonList, List.length_map, enclose_length]
      exact pow_pos hS _
    exact List.ne_nil_of_length_pos hlen
  · rcases hwide with hx | hy
    · have hwx : D.lower x < D.upper x := by linarith
      have hm := comparison_mass D (alphabet k H) hS (no_self_loop D horder) hV hD schedule
        {x, y} x y (by simp) (by simp) hne B hBx hwx (accuracy k B w) (failure k)
        (accuracy_pos hk B hw).le hbad
      have he := comparison_error_le hk B hw hx
      change 1 - error k ≤ _
      linarith
    · have hwy : D.lower y < D.upper y := by linarith
      have hm := comparison_mass D (alphabet k H) hS (no_self_loop D horder) hV hD schedule
        {x, y} y x (by simp) (by simp) hne.symm B hBy hwy (accuracy k B w) (failure k)
        (accuracy_pos hk B hw).le hbad
      have he := comparison_error_le hk B hw hy
      have hm' : 1 - error k ≤ lowerFraction (comparisonList D (alphabet k H) schedule y x) +
          upperFraction (comparisonList D (alphabet k H) schedule y x) := by linarith
      simpa only [error, lowerFraction, upperFraction, comparisonList, separated,
        reverseSeparated, List.countP_map, List.length_map, Function.comp_def, add_comm] using hm'

private theorem threshold_cover (L : List Interval) (c : ℚ) :
    L.length ≤ L.countP (fun I => decide (I.2 < c)) +
      L.countP (fun I => decide (c < I.1)) + crossingCount L c := by
  induction L with
  | nil => simp [crossingCount]
  | cons I L ih =>
    by_cases h₁ : I.2 < c <;> by_cases h₂ : c < I.1 <;>
      simp [crossingCount, h₁, h₂, not_lt.mp, not_le.mpr] at * <;> omega

theorem threshold_mass (D : System (Fin n) ℚ) (S : ℕ) (hS : 0 < S)
    (schedule : List (Fin n)) (x : Fin n) (c : ℚ) :
    1 - (crossingCount ((enclose D S schedule).map (fun I => I x)) c : ℚ) /
        (enclose D S schedule).length ≤
      lowerFraction (thresholdList D S schedule x c) + upperFraction (thresholdList D S schedule x c) := by
  have hn : (0 : ℚ) < (enclose D S schedule).length := by
    rw [enclose_length]
    positivity
  have hc := threshold_cover ((enclose D S schedule).map (fun I => I x)) c
  have hq : ((enclose D S schedule).length : ℚ) ≤
      ((enclose D S schedule).countP (fun I => decide ((I x).2 < c)) : ℚ) +
      ((enclose D S schedule).countP (fun I => decide (c < (I x).1)) : ℚ) +
      (crossingCount ((enclose D S schedule).map (fun I => I x)) c : ℚ) := by
    simpa only [List.length_map, List.countP_map, Function.comp_def, Nat.cast_add] using
      (show (↑((enclose D S schedule).map (fun I => I x)).length : ℚ) ≤
        (((enclose D S schedule).map (fun I => I x)).countP (fun I => decide (I.2 < c)) : ℚ) +
        (((enclose D S schedule).map (fun I => I x)).countP (fun I => decide (c < I.1)) : ℚ) +
        (crossingCount ((enclose D S schedule).map (fun I => I x)) c : ℚ) by exact_mod_cast hc)
  have hd := div_le_div_of_nonneg_right hq hn.le
  rw [div_self hn.ne', add_div, add_div] at hd
  simp only [lowerFraction, upperFraction, thresholdList, List.countP_map,
    List.length_map, Function.comp_def, separated, reverseSeparated]
  linarith

/-- Every fixed-threshold test succeeds when its free coordinate is wide. -/
theorem threshold_succeeds (D : System (Fin n) ℚ)
    (hD : Normalized D.toReal) (hV : 0 < volume (region D.toReal))
    (horder : ∀ x y, D.edge x y = true → x.val < y.val)
    (hwidth : ∀ x, D.lower x ≤ D.upper x) (hunit : ∀ x, D.upper x - D.lower x ≤ 1)
    (rank : Fin n → ℕ) (k H B : ℕ) (hk : 0 < k)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (SortingAdversary.Optimal.GraphBalls.neighbors D.edge x).card ≤ k)
    (x : Fin n) (hB : ComparableDensity.comparableCount D.toReal x ≤ B)
    (w : ℚ) (hw : 0 < w) (hwide : w ≤ D.upper x - D.lower x) (c : ℚ) :
    ∃ a, selectAnswer k (thresholdList D (alphabet k H)
      (certificateSchedule D k H B hk w hw {x}) x c) = some a := by
  let schedule := certificateSchedule D k H B hk w hw {x}
  have hbad := certificate_bad_width D horder hwidth hunit rank k H B hk hrank hheight hdegree
    w hw {x} (by simp)
  have hS := EnclosureParameters.alphabet_pos k H
  have hwx : D.lower x < D.upper x := by linarith
  have hc := crossing_fraction D (alphabet k H) hS (no_self_loop D horder) hV hD schedule
    {x} x (by simp) B hB hwx (accuracy k B w) (failure k) (accuracy_pos hk B hw).le hbad c
  have he := crossing_error_le hk B hw hwide
  have hm := threshold_mass D (alphabet k H) hS schedule x c
  apply selectAnswer_succeeds
  · have hlen : 0 < (thresholdList D (alphabet k H) schedule x c).length := by
      simp only [thresholdList, List.length_map, enclose_length]
      exact pow_pos hS _
    exact List.ne_nil_of_length_pos hlen
  · change 1 - error k ≤ _
    linarith [error_pos hk]

/-- The one-coordinate central-interval routine succeeds on the actual
calibrated list whenever the stored interval reaches the width threshold. -/
theorem central_succeeds (D : System (Fin n) ℚ)
    (hD : Normalized D.toReal) (hV : 0 < volume (region D.toReal))
    (horder : ∀ x y, D.edge x y = true → x.val < y.val)
    (hwidth : ∀ x, D.lower x ≤ D.upper x) (hunit : ∀ x, D.upper x - D.lower x ≤ 1)
    (rank : Fin n → ℕ) (k H B : ℕ) (hk : 0 < k)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (SortingAdversary.Optimal.GraphBalls.neighbors D.edge x).card ≤ k)
    (x : Fin n) (hB : ComparableDensity.comparableCount D.toReal x ≤ B)
    (w : ℚ) (hw : 0 < w) (hwide : w ≤ D.upper x - D.lower x) :
    let L := (enclose D (alphabet k H) (certificateSchedule D k H B hk w hw {x})).map (fun I => I x)
    centralInterval L = some (centralCandidate L) := by
  let schedule := certificateSchedule D k H B hk w hw {x}
  let L := (enclose D (alphabet k H) schedule).map (fun I => I x)
  have hS := EnclosureParameters.alphabet_pos k H
  have hN : 0 < L.length := by
    simp only [L, List.length_map, enclose_length]
    exact pow_pos hS _
  have hfour : 4 ∣ L.length := by
    simpa only [L, List.length_map, schedule, certificateSchedule, calibratedEnclose_eq_enclose] using
      calibratedEnclose_length_dvd_four D k H {x} (by simp) (accuracy k B w) (failure k)
        (accuracy_pos hk B hw) (failure_pos hk)
  have hbad := certificate_bad_width D horder hwidth hunit rank k H B hk hrank hheight hdegree
    w hw {x} (by simp)
  apply centralInterval_succeeds L hN hfour
  · intro I hI
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hI
    exact enclose_valid D _ schedule hwidth entry he x
  · intro c
    have hwx : D.lower x < D.upper x := by linarith
    have hc := crossing_fraction D (alphabet k H) hS (no_self_loop D horder) hV hD schedule
      {x} x (by simp) B hB hwx (accuracy k B w) (failure k) (accuracy_pos hk B hw).le hbad c
    have he := crossing_error_le hk B hw hwide
    have hsmall := crossing_error_small hk
    have hc' : (crossingCount L c : ℚ) / L.length ≤ 1 / 8 := by
      have hlen : L.length = (enclose D (alphabet k H) schedule).length := by
        simp only [L, List.length_map]
      rw [← hlen] at hc
      linarith
    have hn : (0 : ℚ) < L.length := by exact_mod_cast hN
    have hnat : (8 : ℚ) * crossingCount L c ≤ L.length := by
      have h := (div_le_iff₀ hn).mp hc'
      linarith
    exact_mod_cast hnat

end SortingAdversary.Continuous.CertificateSuccess
