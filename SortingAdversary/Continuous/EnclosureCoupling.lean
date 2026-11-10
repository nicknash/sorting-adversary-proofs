import SortingAdversary.Continuous.RationalSemantics
import SortingAdversary.Continuous.Stationarity
import SortingAdversary.Continuous.CertificateProbability

/-!
# The actual finite-list certificates bound continuous probabilities

For every local digit word, start with a uniform feasible assignment and run
the same finite schedule.  Averaging these pushforwards leaves the uniform law
unchanged.  The rational endpoint calculation encloses each real trajectory.
Consequently the fraction of words certifying an event is a lower bound on
its probability under the uniform order-region law.

This constructs the finite-averaging argument from the actual update program;
no stationarity, uniform-entry coupling, or soundness oracle is a hypothesis
of the final enclosure theorem.
-/

namespace SortingAdversary.Continuous.EnclosureCoupling

open FiniteAveraging OrderRegion Stationarity MeasureTheory Set
open scoped BigOperators ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def runWord (D : System ι ℝ) (S : ℕ) (schedule : List ι)
    (digits : Fin schedule.length → Fin S) (X : ι → ℝ) : ι → ℝ :=
  fullSteps D S (assignedSteps S schedule digits) X

theorem runWord_cons (D : System ι ℝ) (S : ℕ) (x : ι) (xs : List ι)
    (digits : Fin (x :: xs).length → Fin S) (X : ι → ℝ) :
    runWord D S (x :: xs) digits X =
      runWord D S xs (Fin.tail digits) (update D S (digits 0) x X) := by
  simp only [runWord, assignedSteps_cons, fullSteps, List.foldl_cons]

theorem continuous_fullSteps (D : System ι ℝ) (S : ℕ) (steps : List (ι × Fin S)) :
    Continuous (fullSteps D S steps) := by
  induction steps with
  | nil => exact continuous_id
  | cons step steps ih =>
      exact ih.comp (continuous_update D S step.2 step.1)

theorem continuous_runWord (D : System ι ℝ) (S : ℕ) (schedule : List ι)
    (digits : Fin schedule.length → Fin S) : Continuous (runWord D S schedule digits) :=
  continuous_fullSteps D S _

noncomputable def wordAverage (D : System ι ℝ) (S : ℕ) (schedule : List ι)
    (μ : Measure (ι → ℝ)) : Measure (ι → ℝ) :=
  ((S : ℝ≥0∞)⁻¹) ^ schedule.length •
    ∑ digits : Fin schedule.length → Fin S, μ.map (runWord D S schedule digits)

theorem wordAverage_nil (D : System ι ℝ) (S : ℕ) (μ : Measure (ι → ℝ)) :
    wordAverage D S [] μ = μ := by
  letI : Unique (Fin 0 → Fin S) :=
    ⟨⟨Fin.elim0⟩, fun f => funext (fun i => Fin.elim0 i)⟩
  simp only [wordAverage, List.length_nil, pow_zero, one_smul, Fintype.sum_unique]
  have he (digits : Fin 0 → Fin S) : runWord D S [] digits = id := by
    funext X
    simp [runWord, assignedSteps, fullSteps]
  rw [he, Measure.map_id]

/-- Splitting off the first independent digit gives exactly the one-update
finite mixture, followed by the remaining schedule. -/
theorem wordAverage_cons (D : System ι ℝ) (S : ℕ) (x : ι) (xs : List ι)
    (μ : Measure (ι → ℝ)) :
    wordAverage D S (x :: xs) μ = wordAverage D S xs (branchAverage D S x μ) := by
  have hsum : (∑ digits : Fin (x :: xs).length → Fin S,
      μ.map (runWord D S (x :: xs) digits)) =
      ∑ j : Fin S, ∑ digits : Fin xs.length → Fin S,
        μ.map (runWord D S xs digits ∘ update D S j x) := by
    let e := Fin.consEquiv (fun _ : Fin (xs.length + 1) => Fin S)
    calc
      _ = ∑ p : Fin S × (Fin xs.length → Fin S),
          μ.map (runWord D S (x :: xs) (Fin.cons p.1 p.2)) := by
            apply Fintype.sum_equiv e.symm
            intro digits
            congr 1
            funext X
            simp [e, Fin.consEquiv, Fin.cons_self_tail]
      _ = _ := ?_
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro digits hd
    congr 1
    funext X
    simp [e, runWord_cons, Function.comp_def]
  unfold wordAverage
  rw [hsum]
  simp_rw [branchAverage, Measure.map_smul,
    Measure.map_finset_sum' (continuous_runWord D S xs _).measurable.aemeasurable,
    Measure.map_map (continuous_runWord D S xs _).measurable
      (continuous_update D S _ x).measurable]
  rw [← Finset.smul_sum, smul_smul, List.length_cons, pow_succ, Finset.sum_comm]

/-- Uniform feasible-region measure is stationary for the complete finite
word enumeration of any local schedule. -/
theorem wordAverage_stationary (D : System ι ℝ) (S : ℕ) (hS : 0 < S)
    (hloop : ∀ x, D.edge x x = false) (schedule : List ι) :
    wordAverage D S schedule (uniformMeasure D) = uniformMeasure D := by
  induction schedule with
  | nil => exact wordAverage_nil D S _
  | cons x xs ih =>
      rw [wordAverage_cons, update_uniform_stationary D x (hloop x) S hS, ih]

theorem wordAverage_apply (D : System ι ℝ) (S : ℕ) (schedule : List ι)
    (μ : Measure (ι → ℝ)) (E : Set (ι → ℝ)) (hE : MeasurableSet E) :
    wordAverage D S schedule μ E = ((S : ℝ≥0∞)⁻¹) ^ schedule.length *
      ∑ digits : Fin schedule.length → Fin S,
        μ ((runWord D S schedule digits) ⁻¹' E) := by
  simp only [wordAverage, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro digits hd
  exact Measure.map_apply (continuous_runWord D S schedule digits).measurable hE

/-- Counting sound words gives a lower bound under the genuine uniform law.
The required soundness concerns the displayed deterministic trajectory. -/
theorem sound_word_count (D : System ι ℝ) (S : ℕ) (hS : 0 < S)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D))
    (schedule : List ι) (cert : (Fin schedule.length → Fin S) → Bool)
    (E : Set (ι → ℝ)) (hE : MeasurableSet E)
    (hsound : ∀ digits, cert digits = true → ∀ X, D.StrictlyFeasible X →
      runWord D S schedule digits X ∈ E) :
    ((Finset.univ.filter fun digits => cert digits).card : ℝ≥0∞) /
      (S : ℝ≥0∞) ^ schedule.length ≤ uniformMeasure D E := by
  haveI := isProbabilityMeasure_uniformMeasure D hV
  have hword (digits : Fin schedule.length → Fin S) :
      (if cert digits then (1 : ℝ≥0∞) else 0) ≤
        uniformMeasure D ((runWord D S schedule digits) ⁻¹' E) := by
    by_cases hc : cert digits = true
    · simp only [hc, if_true]
      have hm : uniformMeasure D univ ≤
          uniformMeasure D ((runWord D S schedule digits) ⁻¹' E) := by
        apply measure_mono_ae
        filter_upwards [uniformMeasure_ae_feasible D] with X hX
        intro hmem
        exact hsound digits hc X hX
      simpa using hm
    · simp [hc]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun digits _ => hword digits)
  have hc : (∑ digits : Fin schedule.length → Fin S,
      if cert digits then (1 : ℝ≥0∞) else 0) =
      ((Finset.univ.filter fun digits => cert digits).card : ℝ≥0∞) := by
    simp [← Finset.sum_filter]
  rw [hc] at hsum
  have hmul := mul_le_mul_right hsum (((S : ℝ≥0∞)⁻¹) ^ schedule.length)
  rw [← wordAverage_apply D S schedule _ E hE,
    wordAverage_stationary D S hS hloop schedule] at hmul
  simpa only [div_eq_mul_inv, ENNReal.inv_pow, mul_comm] using hmul

theorem enclose_count_eq (D : System ι ℚ) (S : ℕ) (schedule : List ι)
    (cert : (ι → ℚ × ℚ) → Bool) :
    (enclose D S schedule).countP cert =
      (Finset.univ.filter fun digits : Fin schedule.length → Fin S =>
        cert (endpointEntry D S schedule digits)).card := by
  classical
  have hall : (words S schedule.length).toFinset = Finset.univ := by
    ext digits
    simp [mem_words digits]
  have hc := (words_nodup S schedule.length).card_eq_countP
    (P := fun digits => cert (endpointEntry D S schedule digits))
  rw [hall] at hc
  simpa [enclose, List.countP_map, Function.comp_def] using hc.symm

/-- An interval predicate sound for every enclosed real vector gives a
certified probability using precisely the rational list and its multiplicity. -/
theorem enclosure_probability (D : System ι ℚ) (S : ℕ) (hS : 0 < S)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (schedule : List ι) (cert : (ι → ℚ × ℚ) → Bool)
    (E : Set (ι → ℝ)) (hE : MeasurableSet E)
    (hsound : ∀ I, cert I = true → ∀ X : ι → ℝ,
      (∀ x, ((I x).1 : ℝ) ≤ X x ∧ X x ≤ ((I x).2 : ℝ)) → X ∈ E) :
    ((enclose D S schedule).countP cert : ℝ≥0∞) / (enclose D S schedule).length ≤
      uniformMeasure D.toReal E := by
  have h := sound_word_count D.toReal S hS hloop hV schedule
    (fun digits => cert (endpointEntry D S schedule digits)) E hE ?_
  · simpa only [enclose_count_eq, enclose_length, Nat.cast_pow] using h
  · intro digits hcert X hX
    apply hsound _ hcert _
    exact rational_endpointEntry_encloses D S schedule digits hX

/-- The same certificate bound in real arithmetic, as used by the executable
rational tests and by the logarithmic volume accounting. -/
theorem enclosure_probability_real (D : System ι ℚ) (S : ℕ) (hS : 0 < S)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (schedule : List ι) (cert : (ι → ℚ × ℚ) → Bool)
    (E : Set (ι → ℝ)) (hE : MeasurableSet E)
    (hsound : ∀ I, cert I = true → ∀ X : ι → ℝ,
      (∀ x, ((I x).1 : ℝ) ≤ X x ∧ X x ≤ ((I x).2 : ℝ)) → X ∈ E) :
    ((enclose D S schedule).countP cert : ℝ) / (enclose D S schedule).length ≤
      (uniformMeasure D.toReal).real E := by
  haveI := isProbabilityMeasure_uniformMeasure D.toReal hV
  have h := ENNReal.toReal_mono (measure_ne_top (uniformMeasure D.toReal) E)
    (enclosure_probability D S hS hloop hV schedule cert E hE hsound)
  simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast, Measure.real_def] using h

end SortingAdversary.Continuous.EnclosureCoupling
