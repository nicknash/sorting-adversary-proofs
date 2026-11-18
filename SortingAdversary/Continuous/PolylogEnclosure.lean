import SortingAdversary.Continuous.Neighborhood
import SortingAdversary.Continuous.Precision
import SortingAdversary.Continuous.LocalSelectionProofs

/-!
# Running the finite enclosure on short dyadic inputs

The lower trajectory rounds **both** walls down and the upper trajectory rounds
both up. Every digit and every edge is shared with the original calculation.
The error bound is one grid spacing for an entire trajectory, regardless of
the number of updates. Thus the rounded list certifies probabilities for the
original system and inherits its bad-width bound at twice the tolerance.
-/

namespace SortingAdversary.Continuous.PolylogEnclosure

open FiniteAveraging EnclosureCoupling OrderRegion MeasureTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A uniform one-sided perturbation of both walls and the initial state
continues to bound the difference after any shared digit word. -/
theorem fullSteps_le_add (D E : System ι ℚ) (he : D.edge = E.edge) (u : ℚ)
    (hl : ∀ x, D.lower x ≤ E.lower x + u) (hr : ∀ x, D.upper x ≤ E.upper x + u)
    (S : ℕ) (steps : List (ι × Fin S)) (Y Z : ι → ℚ) (h : ∀ x, Y x ≤ Z x + u) :
    ∀ x, fullSteps D S steps Y x ≤ fullSteps E S steps Z x + u := by
  induction steps generalizing Y Z with
  | nil => exact h
  | cons step steps ih =>
    apply ih
    intro w
    obtain ⟨v, j⟩ := step
    by_cases hw : w = v
    · subst w
      simp only [update_self]
      have hL : conditionalLower D v Y ≤ conditionalLower E v Z + u := by
        apply (Finset.fold_max_le _).mpr
        constructor
        · exact (hl v).trans (add_le_add_left (lower_le_conditionalLower E v Z) u)
        · intro a ha
          have ha' : D.edge a v = true := by simpa using ha
          exact (h a).trans (add_le_add_left
            (predecessor_le_conditionalLower E v a Z (he ▸ ha')) u)
      have hU : conditionalUpper D v Y - u ≤ conditionalUpper E v Z := by
        apply (Finset.le_fold_min _).mpr
        constructor
        · have h1 := conditionalUpper_le_upper D v Y
          linarith [hr v]
        · intro a ha
          have ha' : E.edge v a = true := by simpa using ha
          have h1 := conditionalUpper_le_successor D v a Y (he.symm ▸ ha')
          linarith [h a]
      have hd := digit_width_le j (sub_le_iff_le_add'.mpr (h v))
        (sub_le_iff_le_add'.mpr hL) (show conditionalUpper D v Y - conditionalUpper E v Z ≤ u by linarith)
      have hs : (u + ((S : ℚ) - 1 - j.val) * u + j.val * u) / S = u :=
        digit_same j u
      rw [hs] at hd
      linarith
    · simpa [hw] using h w

def mesh (F : ℕ) : ℚ := 1 / (2 : ℚ) ^ F

/-- A computable precision depending only on the prescribed absolute error. -/
def gridBits (δ : ℚ) : ℕ := Nat.clog 2 ⌈4 / δ⌉₊

theorem mesh_gridBits_le {δ : ℚ} (hδ : 0 < δ) : mesh (gridBits δ) ≤ δ / 4 := by
  have hpow : (⌈4 / δ⌉₊ : ℚ) ≤ (2 : ℚ) ^ gridBits δ := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) ⌈4 / δ⌉₊
  have h : 4 / δ ≤ (2 : ℚ) ^ gridBits δ := (Nat.le_ceil _).trans hpow
  have hmul := (div_le_iff₀ hδ).mp h
  unfold mesh
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

def roundDown (F : ℕ) (q : ℚ) : ℚ := (⌊q * (2 : ℚ) ^ F⌋ : ℤ) / (2 : ℚ) ^ F

def roundUp (F : ℕ) (q : ℚ) : ℚ := (⌈q * (2 : ℚ) ^ F⌉ : ℤ) / (2 : ℚ) ^ F

theorem roundDown_bounds (F : ℕ) (q : ℚ) :
    roundDown F q ≤ q ∧ q ≤ roundDown F q + mesh F := by
  have hp : (0 : ℚ) < 2 ^ F := by positivity
  constructor
  · exact (div_le_iff₀ hp).mpr (Int.floor_le _)
  · unfold roundDown mesh
    rw [← add_div, le_div_iff₀ hp]
    exact (Int.lt_floor_add_one _).le

theorem roundUp_bounds (F : ℕ) (q : ℚ) :
    q ≤ roundUp F q ∧ roundUp F q ≤ q + mesh F := by
  have hp : (0 : ℚ) < 2 ^ F := by positivity
  constructor
  · exact (le_div_iff₀ hp).mpr (Int.le_ceil _)
  · unfold roundUp mesh
    rw [div_le_iff₀ hp, add_mul, one_div_mul_cancel hp.ne']
    exact (Int.ceil_lt_add_one _).le

def mapWalls (f : ℚ → ℚ) (D : System ι ℚ) : System ι ℚ where
  lower x := f (D.lower x)
  upper x := f (D.upper x)
  edge := D.edge

/-- Execute the two endpoint calculations with exactly the same digit word. -/
def roundedEntry (D : System ι ℚ) (F S : ℕ) (schedule : List ι)
    (digits : Fin schedule.length → Fin S) (x : ι) : ℚ × ℚ :=
  ((endpointEntry (mapWalls (roundDown F) D) S schedule digits x).1,
   (endpointEntry (mapWalls (roundUp F) D) S schedule digits x).2)

def roundedEnclose (D : System ι ℚ) (F S : ℕ) (schedule : List ι) : List (ι → ℚ × ℚ) :=
  (words S schedule.length).map (roundedEntry D F S schedule)

/-- For each entry the rounded lower endpoint moves down by at most one mesh
and the upper endpoint moves up by at most one mesh. -/
theorem roundedEntry_bounds (D : System ι ℚ) (F S : ℕ) (schedule : List ι)
    (digits : Fin schedule.length → Fin S) (x : ι) :
    let I := endpointEntry D S schedule digits x
    let J := roundedEntry D F S schedule digits x
    (J.1 ≤ I.1 ∧ I.1 ≤ J.1 + mesh F) ∧ (I.2 ≤ J.2 ∧ J.2 ≤ I.2 + mesh F) := by
  let L := mapWalls (roundDown F) D
  let U := mapWalls (roundUp F) D
  let steps := assignedSteps S schedule digits
  have l0 (q : ℚ) := (roundDown_bounds F q).1
  have l1 (q : ℚ) := (roundDown_bounds F q).2
  have u0 (q : ℚ) := (roundUp_bounds F q).1
  have u1 (q : ℚ) := (roundUp_bounds F q).2
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simpa only [roundedEntry, endpointEntry, L, steps, add_zero] using fullSteps_le_add L D rfl 0
      (fun w => by simpa only [L, mapWalls, add_zero] using l0 (D.lower w))
      (fun w => by simpa only [L, mapWalls, add_zero] using l0 (D.upper w)) S steps L.lower D.lower
      (fun w => by simpa only [L, mapWalls, add_zero] using l0 (D.lower w)) x
  · exact fullSteps_le_add D L rfl (mesh F) (fun w => l1 _) (fun w => l1 _)
      S steps D.lower L.lower (fun w => l1 _) x
  · simpa only [roundedEntry, endpointEntry, U, steps, add_zero] using fullSteps_le_add D U rfl 0
      (fun w => by simpa only [U, mapWalls, add_zero] using u0 (D.lower w))
      (fun w => by simpa only [U, mapWalls, add_zero] using u0 (D.upper w)) S steps D.upper U.upper
      (fun w => by simpa only [U, mapWalls, add_zero] using u0 (D.upper w)) x
  · exact fullSteps_le_add U D rfl (mesh F) (fun w => u1 _) (fun w => u1 _)
      S steps U.upper D.upper (fun w => u1 _) x

/-- The necessary fractional precision depends only on the input mesh,
the number of scheduled local updates and the digit alphabet. -/
theorem roundedEntry_grid (D : System ι ℚ) (F s : ℕ) (schedule : List ι)
    (digits : Fin schedule.length → Fin (2 ^ s)) (x : ι) :
    let J := roundedEntry D F (2 ^ s) schedule digits x
    OnDyadicGrid (F + schedule.length * s) J.1 ∧ OnDyadicGrid (F + schedule.length * s) J.2 := by
  have lo (q : ℚ) : OnDyadicGrid F (roundDown F q) := ⟨_, rfl⟩
  have hi (q : ℚ) : OnDyadicGrid F (roundUp F q) := ⟨_, rfl⟩
  let L := mapWalls (roundDown F) D
  let U := mapWalls (roundUp F) D
  let steps := assignedSteps (2 ^ s) schedule digits
  have len : steps.length = schedule.length := by simp [steps, assignedSteps]
  constructor
  · simpa only [len, steps, L, roundedEntry, endpointEntry] using fullSteps_onDyadicGrid L F s steps L.lower
      (fun w => lo _) (fun w => lo _) (fun w => lo _) x
  · simpa only [len, steps, U, roundedEntry, endpointEntry] using fullSteps_onDyadicGrid U F s steps U.upper
      (fun w => hi _) (fun w => hi _) (fun w => hi _) x

/-- The upper end of every widened interval still exceeds the original
lower wall; its lower end still precedes the upper wall. The quarter-mass
certificate therefore places both ends of its central candidate in the interior. -/
theorem roundedCentral_intervalInterior (D : System ι ℚ) (F S : ℕ) (schedule : List ι) (x : ι)
    (hw : ∀ v, D.lower v < D.upper v) (hlo : D.WeaklyFeasible D.lower)
    (hup : D.WeaklyFeasible D.upper) {J : Certificates.Interval}
    (hc : Certificates.centralInterval ((roundedEnclose D F S schedule).map (fun I => I x)) =
      some J) : D.lower x < J.1 ∧ J.2 < D.upper x := by
  exact Precision.centralInterval_interior (l := D.lower x) (r := D.upper x) (hL := by
    intro I hI
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hI
    obtain ⟨digits, _, rfl⟩ := List.mem_map.mp he
    have hb := roundedEntry_bounds D F S schedule digits x
    exact ⟨(endpointEntry_right_gt_lower D _ schedule digits hup hw x).trans_le hb.2.1,
      hb.1.1.trans_lt (endpointEntry_left_lt_upper D _ schedule digits hlo hw x)⟩) hc

/-- A successful central test returns an interior anchor on a short grid
even if the original system has much longer endpoints. -/
theorem roundedCentral_grid (D : System ι ℚ) (F s : ℕ) (schedule : List ι) (x : ι)
    (hw : ∀ v, D.lower v < D.upper v) (hlo : D.WeaklyFeasible D.lower)
    (hup : D.WeaklyFeasible D.upper) (h0 : 0 ≤ D.lower x) (h1 : D.upper x ≤ 1)
    {J : Certificates.Interval}
    (hc : Certificates.centralInterval ((roundedEnclose D F (2 ^ s) schedule).map (fun I => I x)) =
      some J) :
    D.lower x < Certificates.roundUp J ∧ Certificates.roundUp J < D.upper x ∧
      OnDyadicGrid (F + schedule.length * s) (Certificates.roundUp J) := by
  have hinner := roundedCentral_intervalInterior D F _ schedule x hw hlo hup hc
  have hwidth := (Certificates.centralInterval_inside hc).1
  have hmem := Certificates.roundUp_mem hwidth
  refine ⟨hinner.1.trans_le hmem.1, hmem.2.trans hinner.2, ?_⟩
  apply Precision.roundUp_preserves_grid _ (h0.trans_lt hinner.1) (hinner.2.trans_le h1) hwidth
  apply Precision.centralInterval_onGrid _ _ hc
  intro I hI
  obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hI
  obtain ⟨digits, _, rfl⟩ := List.mem_map.mp he
  exact roundedEntry_grid D F s schedule digits x

private theorem roundedEnclose_count_eq (D : System ι ℚ) (F S : ℕ) (schedule : List ι)
    (cert : (ι → ℚ × ℚ) → Bool) :
    (roundedEnclose D F S schedule).countP cert =
      (Finset.univ.filter fun digits => cert (roundedEntry D F S schedule digits)).card := by
  classical
  have hall : (words S schedule.length).toFinset = Finset.univ := by
    ext digits
    simp [mem_words digits]
  have hc := (words_nodup S schedule.length).card_eq_countP
    (P := fun digits => cert (roundedEntry D F S schedule digits))
  rw [hall] at hc
  simpa [roundedEnclose, List.countP_map, Function.comp_def] using hc.symm

@[simp] theorem roundedEnclose_length (D : System ι ℚ) (F S : ℕ) (schedule : List ι) :
    (roundedEnclose D F S schedule).length = S ^ schedule.length := by simp [roundedEnclose]

/-- Counts certified by the rounded list bound mass under the original
continuous law, for the same class of predicates used by the mass tests. -/
theorem roundedEnclose_probability (D : System ι ℚ) (F S : ℕ) (hS : 0 < S)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (schedule : List ι) (cert : (ι → ℚ × ℚ) → Bool)
    (E : Set (ι → ℝ)) (hE : MeasurableSet E)
    (hsound : ∀ I, cert I = true → ∀ X : ι → ℝ,
      (∀ x, ((I x).1 : ℝ) ≤ X x ∧ X x ≤ ((I x).2 : ℝ)) → X ∈ E) :
    ((roundedEnclose D F S schedule).countP cert : ℝ) / (roundedEnclose D F S schedule).length ≤
      (uniformMeasure D.toReal).real E := by
  have := isProbabilityMeasure_uniformMeasure D.toReal hV
  have h := sound_word_count D.toReal S hS hloop hV schedule
    (fun digits => cert (roundedEntry D F S schedule digits)) E hE (by
      intro digits hc X hX
      apply hsound _ hc
      intro x
      have hb := roundedEntry_bounds D F S schedule digits x
      have he := rational_endpointEntry_encloses D S schedule digits hX x
      exact ⟨(Rat.cast_le.mpr hb.1.1).trans he.1, he.2.trans (Rat.cast_le.mpr hb.2.1)⟩)
  have hh := ENNReal.toReal_mono (measure_ne_top (uniformMeasure D.toReal) E) h
  simpa only [roundedEnclose_count_eq, roundedEnclose_length, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_pow, Nat.cast_pow, Measure.real_def] using hh

section Selection

open Certificates LocalSelection Set

/-- The same counting argument handles two free coordinates and a free
coordinate compared with a fixed anchor. -/
private theorem selected_mass {n : ℕ} (D : System (Fin n) ℚ) (F k S : ℕ) (hS : 0 < S)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (schedule : List (Fin n)) (project : (Fin n → ℚ × ℚ) → ComparisonIntervals)
    (u v : (Fin n → ℝ) → ℝ) (hu : Measurable u) (hv : Measurable v)
    (hm : ∀ I (X : Fin n → ℝ),
      (∀ x, ((I x).1 : ℝ) ≤ X x ∧ X x ≤ ((I x).2 : ℝ)) →
      (((project I).1.1 : ℝ) ≤ u X ∧ u X ≤ ((project I).1.2 : ℝ)) ∧
      (((project I).2.1 : ℝ) ≤ v X ∧ v X ≤ ((project I).2.2 : ℝ)))
    (a : Answer) (h : selectAnswer k ((roundedEnclose D F S schedule).map project) = some a) :
    1 / 2 - 1 / (100 * (k : ℝ)) ≤ (uniformMeasure D.toReal).real
      (match a with | .less => {X | u X < v X} | .greater => {X | v X < u X}) := by
  have hc := selectAnswer_certificate k _ a h
  cases a with
  | less =>
    have lower := roundedEnclose_probability D F S hS hloop hV schedule
      (fun I => separated (project I)) {X | u X < v X} (measurableSet_lt hu hv)
      (fun I hi X hX => separated_sound (hm I X hX).1 (hm I X hX).2 hi)
    apply le_trans _ lower
    simpa [lowerFraction, List.countP_map, Function.comp_def] using (Rat.cast_le (K := ℝ)).mpr hc
  | greater =>
    have upper := roundedEnclose_probability D F S hS hloop hV schedule
      (fun I => reverseSeparated (project I)) {X | v X < u X} (measurableSet_lt hv hu)
      (fun I hi X hX => reverseSeparated_sound (hm I X hX).1 (hm I X hX).2 hi)
    apply le_trans _ upper
    simpa [upperFraction, List.countP_map, Function.comp_def] using (Rat.cast_le (K := ℝ)).mpr hc

theorem roundedTwo_probability {n : ℕ} (D : System (Fin n) ℚ) (F k S : ℕ) (hS : 0 < S)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (schedule : List (Fin n)) (x y : Fin n) (a : Answer)
    (h : selectAnswer k ((roundedEnclose D F S schedule).map (fun I => (I x, I y))) = some a) :
    1 / 2 - 1 / (100 * (k : ℝ)) ≤ (uniformMeasure D.toReal).real (comparisonEvent x y a) := by
  have result := selected_mass D F k S hS hloop hV schedule _ _ _
    (measurable_pi_apply x) (measurable_pi_apply y) (fun I X hX => ⟨hX x, hX y⟩) a h
  cases a <;> simpa [comparisonEvent] using result

theorem roundedThreshold_probability {n : ℕ} (D : System (Fin n) ℚ) (F k S : ℕ) (hS : 0 < S)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (schedule : List (Fin n)) (x : Fin n) (c : ℚ) (a : Answer)
    (h : selectAnswer k ((roundedEnclose D F S schedule).map (fun I => (I x, (c,c)))) = some a) :
    1 / 2 - 1 / (100 * (k : ℝ)) ≤ (uniformMeasure D.toReal).real (thresholdEvent x c a) := by
  have result := selected_mass D F k S hS hloop hV schedule _ _ _
    (measurable_pi_apply x) (measurable_const (a := (c : ℝ))) (fun I X hX => ⟨hX x, le_rfl, le_rfl⟩) a h
  cases a <;> simpa [thresholdEvent] using result

private theorem quarter_le_fraction {N a : ℕ} (hN : 0 < N) (ha : N ≤ 4 * a) :
    (1 / 4 : ℝ) ≤ (a : ℝ) / N := by
  apply (le_div_iff₀ (by exact_mod_cast hN)).mpr
  have h : (N : ℝ) ≤ 4 * (a : ℝ) := by exact_mod_cast ha
  linarith

/-- All three counts returned by the central test are sound quarter-mass
certificates for the actual coordinate distribution. -/
theorem roundedCentral_probabilities {n : ℕ} (D : System (Fin n) ℚ) (F S : ℕ) (hS : 0 < S)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (schedule : List (Fin n)) (x : Fin n) (J : Interval)
    (h : centralInterval ((roundedEnclose D F S schedule).map (fun I => I x)) = some J) :
    (1 / 4 : ℝ) ≤ (uniformMeasure D.toReal).real {X | X x ≤ (J.1 : ℝ)} ∧
    (1 / 4 : ℝ) ≤ (uniformMeasure D.toReal).real
      {X | (J.1 : ℝ) ≤ X x ∧ X x ≤ (J.2 : ℝ)} ∧
    (1 / 4 : ℝ) ≤ (uniformMeasure D.toReal).real {X | (J.2 : ℝ) ≤ X x} := by
  have hc := centralInterval_certificates h
  have hN := centralInterval_positive h
  have hl := roundedEnclose_probability D F S hS hloop hV schedule
    (fun I => decide ((I x).2 ≤ J.1)) {X | X x ≤ (J.1 : ℝ)}
    (measurableSet_le (measurable_pi_apply x) measurable_const)
    (fun I hI X hX => left_sound (hX x) (of_decide_eq_true hI))
  have hi := roundedEnclose_probability D F S hS hloop hV schedule
    (fun I => decide (J.1 ≤ (I x).1 ∧ (I x).2 ≤ J.2))
    {X | (J.1 : ℝ) ≤ X x ∧ X x ≤ (J.2 : ℝ)}
    ((measurableSet_le measurable_const (measurable_pi_apply x)).inter
      (measurableSet_le (measurable_pi_apply x) measurable_const))
    (fun I hI X hX => inside_sound (hX x) (of_decide_eq_true hI))
  have hr := roundedEnclose_probability D F S hS hloop hV schedule
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

end Selection

/-- A wide rounded entry had an exact width above half the requested
tolerance. The comparison is word by word, preserving multiplicities. -/
theorem roundedEnclose_badWidth_le {n : ℕ} (D : System (Fin n) ℚ) (F S : ℕ)
    (schedule : List (Fin n)) (Q : Finset (Fin n)) (δ : ℚ) (hu : mesh F ≤ δ / 4) :
    (roundedEnclose D F S schedule).countP (badWidth Q δ) ≤
      (enclose D S schedule).countP (badWidth Q (δ / 2)) := by
  rw [roundedEnclose_count_eq, enclose_count_eq]
  apply Finset.card_le_card
  intro digits hd
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, badWidth, decide_eq_true_eq] at hd ⊢
  obtain ⟨x, hx, hwide⟩ := hd
  refine ⟨x, hx, ?_⟩
  have hb := roundedEntry_bounds D F S schedule digits x
  dsimp only at hb
  linarith [hb.1.2, hb.2.2]

/-- Calibrate the original algorithm at half width; the same failure
probability bound now holds for the list actually computed on short inputs. -/
theorem roundedEnclose_width_probability {n : ℕ} (D : System (Fin n) ℚ)
    (horder : ∀ x y, D.edge x y = true → x.val < y.val)
    (hwidth : ∀ x, D.lower x ≤ D.upper x) (hunit : ∀ x, D.upper x - D.lower x ≤ 1)
    (rank : Fin n → ℕ) (d H : ℕ) (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (SortingAdversary.Optimal.GraphBalls.neighbors D.edge x).card ≤ d)
    (Q : Finset (Fin n)) (hQ : Q.card ≤ 2) (δ α : ℚ) (hδ : 0 < δ) (hα : 0 < α)
    (F : ℕ) (hu : mesh F ≤ δ / 4) :
    let S := EnclosureParameters.alphabet d H
    let schedule := calibratedSchedule D d H Q (δ / 2) α (by positivity) hα
    let L := roundedEnclose D F S schedule
    (L.countP (badWidth Q δ) : ℚ) / L.length ≤ α := by
  let S := EnclosureParameters.alphabet d H
  let schedule := calibratedSchedule D d H Q (δ / 2) α (by positivity) hα
  have hc := roundedEnclose_badWidth_le D F S schedule Q δ hu
  have hp := calibratedEnclose_width_probability D horder hwidth hunit rank d H hrank
    hheight hdegree Q hQ (δ / 2) α (by positivity) hα
  rw [calibratedEnclose_eq_enclose] at hp
  change ((enclose D S schedule).countP _ : ℚ) / (enclose D S schedule).length ≤ α at hp
  change ((roundedEnclose D F S schedule).countP _ : ℚ) / (roundedEnclose D F S schedule).length ≤ α
  rw [roundedEnclose_length]
  rw [enclose_length] at hp
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)).trans hp

open InducedEnclosure EnclosureParameters CertificateSuccess

omit [Fintype ι] [DecidableEq ι] in
private theorem mapWalls_induced {κ : Type*} (f : ℚ → ℚ) (D : System ι ℚ) (e : κ ↪ ι) :
    mapWalls f (induced D e) = induced (mapWalls f D) e := rfl

/-- Rounding commutes with restriction to an induced system. Reindexing the
same digit word therefore gives the very same pair of endpoint trajectories. -/
theorem roundedEntry_induced {κ : Type*} [Fintype κ] [DecidableEq κ]
    (D : System ι ℚ) (e : κ ↪ ι) (F S : ℕ) (schedule : List κ)
    (hc : ∀ x ∈ schedule, ClosedAt D e x) (digits : Fin schedule.length → Fin S) :
    roundedEntry (induced D e) F S schedule digits =
      roundedEntry D F S (schedule.map e) (mapDigits schedule e digits) ∘ e := by
  funext x
  unfold roundedEntry
  simp only [mapWalls_induced, Function.comp_apply]
  rw [endpointEntry_induced (mapWalls (roundDown F) D) e S schedule hc digits,
    endpointEntry_induced (mapWalls (roundUp F) D) e S schedule hc digits]
  rfl

theorem roundedEnclose_induced {κ : Type*} [Fintype κ] [DecidableEq κ]
    (D : System ι ℚ) (e : κ ↪ ι) (F S : ℕ) (schedule : List κ)
    (hc : ∀ x ∈ schedule, ClosedAt D e x) :
    roundedEnclose (induced D e) F S schedule =
      (roundedEnclose D F S (schedule.map e)).map (fun I => I ∘ e) := by
  unfold roundedEnclose
  rw [← words_mapDigits S schedule e]
  simp only [List.map_map]
  apply List.map_congr_left
  intro digits _
  exact roundedEntry_induced D e F S schedule hc digits

section Neighborhood

variable {n : ℕ} (D : System (Fin n) ℚ) (F k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
  (Q : Finset (Fin n))

/-- The runtime rounds only the input walls of the retained neighborhood.
Halving the width threshold here halves the enclosure tolerance because the
certificate accuracy is linear in that threshold. -/
def localList :=
  roundedEnclose (Neighborhood.system D k H hk (w / 2) (by positivity) Q) F (alphabet k H)
    (Neighborhood.schedule D k H hk (w / 2) (by positivity) Q)

theorem localList_full :
    let e := Neighborhood.embedding D k H hk (w / 2) (by positivity) Q
    let schedule := Neighborhood.schedule D k H hk (w / 2) (by positivity) Q
    localList D F k H hk w hw Q = (roundedEnclose D F (alphabet k H) (schedule.map e)).map
      (fun I => I ∘ e) :=
  roundedEnclose_induced D _ F _ _ (Neighborhood.schedule_closed D k H hk (w / 2) (by positivity) Q)

/-- Soundness of a predicate computed entirely on the induced graph under
the uniform feasible law of the full graph. -/
theorem localList_probability
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (cert : (Fin (Neighborhood.labels D k H hk (w / 2) (by positivity) Q).card → ℚ × ℚ) → Bool)
    (E : Set (Fin n → ℝ)) (hE : MeasurableSet E)
    (hsound : ∀ I, cert I = true → ∀ X : Fin n → ℝ,
      (∀ x, let y := Neighborhood.embedding D k H hk (w / 2) (by positivity) Q x
            ((I x).1 : ℝ) ≤ X y ∧ X y ≤ ((I x).2 : ℝ)) → X ∈ E) :
    ((localList D F k H hk w hw Q).countP cert : ℝ) / (localList D F k H hk w hw Q).length ≤
      (uniformMeasure D.toReal).real E := by
  let e := Neighborhood.embedding D k H hk (w / 2) (by positivity) Q
  let schedule := Neighborhood.schedule D k H hk (w / 2) (by positivity) Q
  have mass := roundedEnclose_probability D F (alphabet k H) (EnclosureParameters.alphabet_pos k H)
    hloop hV (schedule.map e) (fun I => cert (I ∘ e)) E hE
    (fun I hi X hX => hsound (I ∘ e) hi X (fun x => hX (e x)))
  rw [localList_full]
  simpa only [List.countP_map, List.length_map, Function.comp_def] using mass

theorem accuracy_half : accuracy k (neighborhoodBound k H) (w / 2) =
    accuracy k (neighborhoodBound k H) w / 2 := by unfold accuracy; ring

/-- The width estimate for the returned local list. Endpoint arithmetic and
calibration both run in the induced system at half the target accuracy. -/
theorem localList_width_probability (hwidth : ∀ x, D.lower x ≤ D.upper x)
    (hunit : ∀ x, D.upper x - D.lower x ≤ 1) (rank : Fin n → ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y) (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (SortingAdversary.Optimal.GraphBalls.neighbors D.edge x).card ≤ k)
    (hQ : Q.card ≤ 2) (hu : mesh F ≤ accuracy k (neighborhoodBound k H) w / 4) :
    let q := Neighborhood.queries D k H hk (w / 2) (by positivity) Q
    let L := localList D F k H hk w hw Q
    (L.countP (badWidth q (accuracy k (neighborhoodBound k H) w)) : ℚ) / L.length ≤ failure k := by
  let E := Neighborhood.system D k H hk (w / 2) (by positivity) Q
  let e := Neighborhood.embedding D k H hk (w / 2) (by positivity) Q
  let q := Neighborhood.queries D k H hk (w / 2) (by positivity) Q
  have certified := roundedEnclose_width_probability E
    (Neighborhood.ordered D k H hk _ _ Q rank hrank) (fun x => hwidth (e x))
    (fun x => hunit (e x)) (fun x => rank (e x)) k H (fun x y h => hrank _ _ h)
    (fun x => hheight _) (Neighborhood.degree D k H hk _ _ Q hdegree) q
    ((Neighborhood.queries_card D k H hk _ _ Q).trans hQ) _ _ (accuracy_pos hk _ hw)
    (failure_pos hk) F hu
  simpa only [localList, Neighborhood.schedule, certificateSchedule, accuracy_half] using certified

end Neighborhood

end SortingAdversary.Continuous.PolylogEnclosure
