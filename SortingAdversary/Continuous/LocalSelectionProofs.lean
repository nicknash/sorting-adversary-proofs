import SortingAdversary.Continuous.LocalSelection
import SortingAdversary.Continuous.EnclosureCoupling

/-!
# Soundness of the executable local answer and central-interval tests

The tests inspect only the rational lists produced by the finite digit
program. These theorems derive their probability guarantees under the actual
uniform feasible-region measure. In particular, their conclusions do not
assume an externally supplied probability certificate.
-/

namespace SortingAdversary.Continuous.LocalSelection

open FiniteAveraging Certificates EnclosureCoupling OrderRegion MeasureTheory Set

variable {n : ℕ}

def comparisonEvent (x y : Fin n) (a : Answer) : Set (Fin n → ℝ) :=
  match a with
  | .less => {X | X x < X y}
  | .greater => {X | X y < X x}

def thresholdEvent (x : Fin n) (c : ℚ) (a : Answer) : Set (Fin n → ℝ) :=
  match a with
  | .less => {X | X x < (c : ℝ)}
  | .greater => {X | (c : ℝ) < X x}

theorem comparisonEvent_measurable (x y : Fin n) (a : Answer) :
    MeasurableSet (comparisonEvent x y a) := by
  cases a <;> exact measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)

theorem thresholdEvent_measurable (x : Fin n) (c : ℚ) (a : Answer) :
    MeasurableSet (thresholdEvent x c a) := by
  cases a
  · exact measurableSet_lt (measurable_pi_apply _) measurable_const
  · exact measurableSet_lt measurable_const (measurable_pi_apply _)

theorem lowerFraction_probability (D : System (Fin n) ℚ) (S : ℕ) (hS : 0 < S)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (schedule : List (Fin n)) (x y : Fin n) :
    ((lowerFraction (comparisonList D S schedule x y) : ℚ) : ℝ) ≤
      (uniformMeasure D.toReal).real (comparisonEvent x y .less) := by
  have h := enclosure_probability_real D S hS hloop hV schedule
    (fun I => separated (I x, I y)) (comparisonEvent x y .less)
    (comparisonEvent_measurable x y .less) (fun I hI X hX =>
      separated_sound (I := (I x, I y)) (hX x) (hX y) hI)
  simpa [lowerFraction, comparisonList, List.countP_map, Function.comp_def] using h

theorem upperFraction_probability (D : System (Fin n) ℚ) (S : ℕ) (hS : 0 < S)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (schedule : List (Fin n)) (x y : Fin n) :
    ((upperFraction (comparisonList D S schedule x y) : ℚ) : ℝ) ≤
      (uniformMeasure D.toReal).real (comparisonEvent x y .greater) := by
  have h := enclosure_probability_real D S hS hloop hV schedule
    (fun I => reverseSeparated (I x, I y)) (comparisonEvent x y .greater)
    (comparisonEvent_measurable x y .greater) (fun I hI X hX =>
      reverseSeparated_sound (I := (I x, I y)) (hX x) (hX y) hI)
  simpa [upperFraction, comparisonList, List.countP_map, Function.comp_def] using h

/-- An actual returned answer retains the printed fraction of feasible volume. -/
theorem selectTwo_probability (D : System (Fin n) ℚ) (k S : ℕ) (hS : 0 < S)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (schedule : List (Fin n)) (x y : Fin n) (a : Answer)
    (h : selectTwo D k S schedule x y = .answer a) :
    1 / 2 - 1 / (100 * (k : ℝ)) ≤
      (uniformMeasure D.toReal).real (comparisonEvent x y a) := by
  have hc := selectTwo_certificate D k S schedule x y a h
  cases a
  · exact (show (1 / 2 - 1 / (100 * (k : ℝ))) ≤
        ((lowerFraction (comparisonList D S schedule x y) : ℚ) : ℝ) by
        dsimp only at hc
        have hh := Rat.cast_le (K := ℝ) |>.mpr hc
        simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_mul,
          Rat.cast_ofNat, Rat.cast_natCast] using hh).trans (lowerFraction_probability D S hS hloop hV schedule x y)
  · exact (show (1 / 2 - 1 / (100 * (k : ℝ))) ≤
        ((upperFraction (comparisonList D S schedule x y) : ℚ) : ℝ) by
        dsimp only at hc
        have hh := Rat.cast_le (K := ℝ) |>.mpr hc
        simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_mul,
          Rat.cast_ofNat, Rat.cast_natCast] using hh).trans (upperFraction_probability D S hS hloop hV schedule x y)

theorem threshold_lowerFraction_probability (D : System (Fin n) ℚ)
    (S : ℕ) (hS : 0 < S) (hloop : ∀ x, D.edge x x = false)
    (hV : 0 < volume (region D.toReal)) (schedule : List (Fin n))
    (x : Fin n) (c : ℚ) :
    ((lowerFraction (thresholdList D S schedule x c) : ℚ) : ℝ) ≤
      (uniformMeasure D.toReal).real (thresholdEvent x c .less) := by
  have h := enclosure_probability_real D S hS hloop hV schedule
    (fun I => separated (I x, (c, c))) (thresholdEvent x c .less)
    (thresholdEvent_measurable x c .less) (fun I hI X hX =>
      separated_sound (I := (I x, (c, c))) (hX x) ⟨le_rfl, le_rfl⟩ hI)
  simpa [lowerFraction, thresholdList, List.countP_map, Function.comp_def] using h

theorem threshold_upperFraction_probability (D : System (Fin n) ℚ)
    (S : ℕ) (hS : 0 < S) (hloop : ∀ x, D.edge x x = false)
    (hV : 0 < volume (region D.toReal)) (schedule : List (Fin n))
    (x : Fin n) (c : ℚ) :
    ((upperFraction (thresholdList D S schedule x c) : ℚ) : ℝ) ≤
      (uniformMeasure D.toReal).real (thresholdEvent x c .greater) := by
  have h := enclosure_probability_real D S hS hloop hV schedule
    (fun I => reverseSeparated (I x, (c, c))) (thresholdEvent x c .greater)
    (thresholdEvent_measurable x c .greater) (fun I hI X hX =>
      reverseSeparated_sound (I := (I x, (c, c))) (hX x) ⟨le_rfl, le_rfl⟩ hI)
  simpa [upperFraction, thresholdList, List.countP_map, Function.comp_def] using h

theorem selectThreshold_probability (D : System (Fin n) ℚ) (k S : ℕ) (hS : 0 < S)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (schedule : List (Fin n)) (x : Fin n) (c : ℚ) (a : Answer)
    (h : selectThreshold D k S schedule x c = .answer a) :
    1 / 2 - 1 / (100 * (k : ℝ)) ≤
      (uniformMeasure D.toReal).real (thresholdEvent x c a) := by
  have hc := selectThreshold_certificate D k S schedule x c a h
  cases a
  · exact (show (1 / 2 - 1 / (100 * (k : ℝ))) ≤
        ((lowerFraction (thresholdList D S schedule x c) : ℚ) : ℝ) by
        dsimp only at hc
        have hh := Rat.cast_le (K := ℝ) |>.mpr hc
        simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_mul,
          Rat.cast_ofNat, Rat.cast_natCast] using hh).trans
          (threshold_lowerFraction_probability D S hS hloop hV schedule x c)
  · exact (show (1 / 2 - 1 / (100 * (k : ℝ))) ≤
        ((upperFraction (thresholdList D S schedule x c) : ℚ) : ℝ) by
        dsimp only at hc
        have hh := Rat.cast_le (K := ℝ) |>.mpr hc
        simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_mul,
          Rat.cast_ofNat, Rat.cast_natCast] using hh).trans
          (threshold_upperFraction_probability D S hS hloop hV schedule x c)

private theorem quarter_le_fraction {N a : ℕ} (hN : 0 < N) (ha : N ≤ 4 * a) :
    (1 / 4 : ℝ) ≤ (a : ℝ) / N := by
  apply (le_div_iff₀ (by exact_mod_cast hN)).mpr
  have h : (N : ℝ) ≤ 4 * (a : ℝ) := by exact_mod_cast ha
  linarith

/-- All three counts returned by the central test are sound quarter-mass
certificates for the actual coordinate distribution. -/
theorem centralInterval_probabilities (D : System (Fin n) ℚ) (S : ℕ) (hS : 0 < S)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (schedule : List (Fin n)) (x : Fin n) (J : Interval)
    (h : centralInterval ((enclose D S schedule).map (fun I => I x)) = some J) :
    (1 / 4 : ℝ) ≤ (uniformMeasure D.toReal).real {X | X x ≤ (J.1 : ℝ)} ∧
    (1 / 4 : ℝ) ≤ (uniformMeasure D.toReal).real
      {X | (J.1 : ℝ) ≤ X x ∧ X x ≤ (J.2 : ℝ)} ∧
    (1 / 4 : ℝ) ≤ (uniformMeasure D.toReal).real {X | (J.2 : ℝ) ≤ X x} := by
  have hc := centralInterval_certificates h
  have hN := centralInterval_positive h
  have hl := enclosure_probability_real D S hS hloop hV schedule
    (fun I => decide ((I x).2 ≤ J.1)) {X | X x ≤ (J.1 : ℝ)}
    (measurableSet_le (measurable_pi_apply x) measurable_const)
    (fun I hI X hX => left_sound (hX x) (of_decide_eq_true hI))
  have hi := enclosure_probability_real D S hS hloop hV schedule
    (fun I => decide (J.1 ≤ (I x).1 ∧ (I x).2 ≤ J.2))
    {X | (J.1 : ℝ) ≤ X x ∧ X x ≤ (J.2 : ℝ)}
    ((measurableSet_le measurable_const (measurable_pi_apply x)).inter
      (measurableSet_le (measurable_pi_apply x) measurable_const))
    (fun I hI X hX => inside_sound (hX x) (of_decide_eq_true hI))
  have hr := enclosure_probability_real D S hS hloop hV schedule
    (fun I => decide (J.2 ≤ (I x).1)) {X | (J.2 : ℝ) ≤ X x}
    (measurableSet_le measurable_const (measurable_pi_apply x))
    (fun I hI X hX => right_sound (hX x) (of_decide_eq_true hI))
  refine ⟨?_, ?_, ?_⟩
  · apply (quarter_le_fraction hN hc.2.1).trans
    simpa [leftCount, List.countP_map, Function.comp_def] using hl
  · apply (quarter_le_fraction hN hc.2.2.1).trans
    simpa [insideCount, List.countP_map, Function.comp_def] using hi
  · apply (quarter_le_fraction hN hc.2.2.2).trans
    simpa [rightCount, List.countP_map, Function.comp_def] using hr

end SortingAdversary.Continuous.LocalSelection
