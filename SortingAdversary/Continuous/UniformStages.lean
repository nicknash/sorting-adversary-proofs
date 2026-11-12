import SortingAdversary.Continuous.ParameterBounds
import SortingAdversary.Continuous.ArbitraryLabels
import SortingAdversary.Continuous.Rates
import SortingAdversary.Optimal.CappedStageScan

/-!
# A concrete bounded choice of the continuous parameter

The exact rational calibration is materialized only after a fixed arithmetic
envelope passes the capped evaluator. This is a conservative implementation
of the manuscript's slowly increasing parameter schedule: all rejected work
is bounded, every fixed stage is eventually admitted, and an admitted stage's
actual finite enumeration has at most `n` entries. No parameter-generation
time or eventual-admission assertion is supplied as an assumption.
-/

namespace SortingAdversary.Continuous.UniformStages

open EnclosureParameters ParameterBounds ArbitraryLabels
open SortingAdversary.Optimal CappedArithmetic
open Filter
open scoped Topology

def degree (j : ℕ) : ℕ := 2 ^ (j + 5)

def failureDen (k : ℕ) : ℕ := 200 * k

def accuracyDen (k : ℕ) : ℕ :=
  800 * k * (neighborhoodBound k (pathHeight k) + 1) *
    2 ^ (2 * k * neighborhoodBound k (pathHeight k))

theorem failureDen_pos {k : ℕ} (hk : 0 < k) : 0 < failureDen k := by
  unfold failureDen
  positivity

theorem accuracyDen_pos {k : ℕ} (hk : 0 < k) : 0 < accuracyDen k := by
  unfold accuracyDen
  positivity

theorem failure_eq (k : ℕ) : CertificateSuccess.failure k = 1 / (failureDen k : ℚ) := by
  unfold CertificateSuccess.failure CertificateSuccess.error failureDen
  push_cast
  ring

theorem accuracy_eq (k : ℕ) :
    CertificateSuccess.accuracy k (neighborhoodBound k (pathHeight k))
      (widthThreshold k (pathHeight k)) = 1 / (accuracyDen k : ℚ) := by
  by_cases hk : k = 0
  · simp [hk, CertificateSuccess.accuracy, CertificateSuccess.error, accuracyDen]
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have hB : (neighborhoodBound k (pathHeight k) : ℚ) + 1 ≠ 0 := by positivity
  unfold CertificateSuccess.accuracy CertificateSuccess.error widthThreshold accuracyDen
  push_cast
  field_simp
  ring

/-- The exact word-count budget used by the runtime certificate calibration. -/
def enumerationBudget (k : ℕ) (hk : 0 < k) : ℕ :=
  enumerationBound k (pathHeight k)
    (CertificateSuccess.accuracy k (neighborhoodBound k (pathHeight k))
      (widthThreshold k (pathHeight k))) (CertificateSuccess.failure k)
    (CertificateSuccess.accuracy_pos hk _ (widthThreshold_pos k (pathHeight k)))
    (CertificateSuccess.failure_pos hk)

theorem enumerationBudget_le (k : ℕ) (hk : 0 < k) :
    enumerationBudget k hk ≤ enumerationEnvelope k (pathHeight k) (failureDen k) (accuracyDen k) := by
  unfold enumerationBudget
  simp_rw [accuracy_eq, failure_eq]
  exact enumerationBound_le_envelope k (pathHeight k) (failureDen k) (accuracyDen k)
    (failureDen_pos hk) (accuracyDen_pos hk) _ _

theorem enumerationBudget_ge_four (k : ℕ) (hk : 0 < k) : 4 ≤ enumerationBudget k hk := by
  let δ := CertificateSuccess.accuracy k (neighborhoodBound k (pathHeight k))
    (widthThreshold k (pathHeight k))
  let α := CertificateSuccess.failure k
  have hδ : 0 < δ := CertificateSuccess.accuracy_pos hk _ (widthThreshold_pos k (pathHeight k))
  have hα : 0 < α := CertificateSuccess.failure_pos hk
  have ht := sweepCount_pos k (pathHeight k) δ α hδ hα
  have hb : 0 < retainedBound k (pathHeight k) δ α hδ hα := by
    unfold retainedBound
    positivity
  have hfour : 4 ≤ alphabet k (pathHeight k) :=
    Nat.le_of_dvd (alphabet_pos _ _) (four_dvd_alphabet _ _)
  apply hfour.trans
  change alphabet k (pathHeight k) ≤
    alphabet k (pathHeight k) ^ (retainedBound k (pathHeight k) δ α hδ hα *
      sweepCount k (pathHeight k) δ α hδ hα)
  simpa only [pow_one] using Nat.pow_le_pow_right (alphabet_pos k (pathHeight k))
    (show 1 ≤ retainedBound k (pathHeight k) δ α hδ hα *
      sweepCount k (pathHeight k) δ α hδ hα from Nat.mul_pos hb ht)

theorem enumerationBudget_log_ge_two (k : ℕ) (hk : 0 < k) :
    2 ≤ Nat.log 2 (enumerationBudget k hk) := by
  have hlog : Nat.log 2 4 = 2 := by decide
  simpa only [hlog] using (Nat.log_mono_right (b := 2) (enumerationBudget_ge_four k hk))

namespace Recipe

def degree : Expr := .pow (.lit 2) (.add .input (.lit 5))
def height : Expr := .pow (.lit 2) (.add degree (.lit 1))
def comparable : Expr := .pow (.add degree (.lit 1)) (.add height (.lit 1))
def failure : Expr := .mul (.lit 200) degree
def accuracy : Expr :=
  .mul (.mul (.mul (.lit 800) degree) (.add comparable (.lit 1)))
    (.pow (.lit 2) (.mul (.mul (.lit 2) degree) comparable))
def alphabetExponent : Expr := .mul (.lit 4) (.pow comparable (.lit 2))
def alphabet : Expr := .pow (.lit 2) alphabetExponent
def moment : Expr := .mul (.mul (.lit 4) comparable) (.pow alphabet height)
def sweeps : Expr := .mul (.mul (.lit 2) failure) (.pow accuracy moment)
def retained : Expr := .mul (.lit 2)
  (.pow (.add degree (.lit 1)) (.add (.mul height sweeps) (.lit 2)))
def budget : Expr := .pow alphabet (.mul retained sweeps)

theorem degree_value (j : ℕ) : degree.value j = UniformStages.degree j := rfl

theorem budget_value (j : ℕ) : budget.value j =
    enumerationEnvelope (UniformStages.degree j) (pathHeight (UniformStages.degree j))
      (failureDen (UniformStages.degree j)) (accuracyDen (UniformStages.degree j)) := rfl

private theorem need_mul_left (a b : Expr) (j : ℕ) : a.need j ≤ (Expr.mul a b).need j :=
  le_max_left _ _

private theorem need_mul_right (a b : Expr) (j : ℕ) : b.need j ≤ (Expr.mul a b).need j :=
  (le_max_left _ _).trans (le_max_right _ _)

private theorem need_pow_left (a b : Expr) (j : ℕ) : a.need j ≤ (Expr.pow a b).need j :=
  le_max_left _ _

private theorem need_pow_right (a b : Expr) (j : ℕ) : b.need j ≤ (Expr.pow a b).need j :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem sweeps_need (j : ℕ) : sweeps.need j ≤ budget.need j :=
  (need_mul_right retained sweeps j).trans (need_pow_right alphabet (.mul retained sweeps) j)

theorem moment_need (j : ℕ) : moment.need j ≤ budget.need j :=
  (need_pow_right accuracy moment j).trans
    ((need_mul_right (.mul (.lit 2) failure) (.pow accuracy moment) j).trans (sweeps_need j))

theorem alphabet_need (j : ℕ) : alphabet.need j ≤ budget.need j := need_pow_left _ _ _

theorem exponent_need (j : ℕ) : alphabetExponent.need j ≤ budget.need j :=
  (need_pow_right (.lit 2) alphabetExponent j).trans (alphabet_need j)

theorem accuracy_need (j : ℕ) : accuracy.need j ≤ budget.need j :=
  (need_pow_left accuracy moment j).trans
    ((need_mul_right (.mul (.lit 2) failure) (.pow accuracy moment) j).trans (sweeps_need j))

theorem failure_need (j : ℕ) : failure.need j ≤ budget.need j :=
  (need_mul_right (.lit 2) failure j).trans
    ((need_mul_left (.mul (.lit 2) failure) (.pow accuracy moment) j).trans (sweeps_need j))

theorem height_need (j : ℕ) : height.need j ≤ budget.need j :=
  (need_pow_right alphabet height j).trans
    ((need_mul_right (.mul (.lit 4) comparable) (.pow alphabet height) j).trans (moment_need j))

theorem comparable_need (j : ℕ) : comparable.need j ≤ budget.need j :=
  (need_mul_right (.lit 4) comparable j).trans
    ((need_mul_left (.mul (.lit 4) comparable) (.pow alphabet height) j).trans (moment_need j))

theorem degree_need (j : ℕ) : degree.need j ≤ budget.need j :=
  (need_mul_right (.lit 200) degree j).trans (failure_need j)

theorem retained_need (j : ℕ) : retained.need j ≤ budget.need j :=
  (need_mul_left retained sweeps j).trans (need_pow_right alphabet (.mul retained sweeps) j)

end Recipe

def selectedStage (n : ℕ) : ℕ := CappedStageScan.stage Recipe.budget n

/-- `none` selects the fixed-label fallback; every `some` value is at least 64. -/
def selected (n : ℕ) : Option ℕ :=
  if selectedStage n = 0 then none else some (degree (selectedStage n))

theorem degree_pos (j : ℕ) : 0 < degree j := by unfold degree; positivity

theorem degree_ge_sixtyFour (j : ℕ) (hj : 0 < j) : 64 ≤ degree j := by
  have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 6 ≤ j + 5 by omega)
  exact hh

theorem selected_some {n k : ℕ} (h : selected n = some k) :
    k = degree (selectedStage n) ∧ 64 ≤ k := by
  unfold selected at h
  split at h
  · contradiction
  · rename_i hj
    cases h
    exact ⟨rfl, degree_ge_sixtyFour _ (Nat.pos_of_ne_zero hj)⟩

theorem selected_enumerationBudget (n : ℕ) (hj : 0 < selectedStage n) :
    enumerationBudget (degree (selectedStage n)) (degree_pos _) ≤ n := by
  have hcap := CappedStageScan.stage_need Recipe.budget n hj
  calc
    enumerationBudget (degree (selectedStage n)) (degree_pos _) ≤
        enumerationEnvelope (degree (selectedStage n)) (pathHeight (degree (selectedStage n)))
          (failureDen (degree (selectedStage n))) (accuracyDen (degree (selectedStage n))) :=
      enumerationBudget_le _ _
    _ = Recipe.budget.value (selectedStage n) := (Recipe.budget_value _).symm
    _ ≤ Recipe.budget.need (selectedStage n) := Recipe.budget.value_le_need _
    _ ≤ Optimal.Parameters.logCap n := hcap
    _ ≤ n := Optimal.Parameters.logCap_le_input n

theorem selected_budget {n k : ℕ} (h : selected n = some k) (hk : 0 < k) :
    enumerationBudget k hk ≤ n := by
  have hh := (selected_some h).1
  have hj : 0 < selectedStage n := by
    by_contra hn
    have hz : selectedStage n = 0 := by omega
    simp [selected, hz] at h
  subst k
  exact selected_enumerationBudget n hj

/-- All materialized integer parameters and both rational search bounds fit
the same input-dependent cap. This controls searches, not only their outputs. -/
theorem admitted_scalar_bounds (j cap : ℕ) (hcap : Recipe.budget.need j ≤ cap) :
    degree j ≤ cap ∧ pathHeight (degree j) ≤ cap ∧
    neighborhoodBound (degree j) (pathHeight (degree j)) ≤ cap ∧
    alphabetExponent (degree j) (pathHeight (degree j)) ≤ cap ∧
    alphabet (degree j) (pathHeight (degree j)) ≤ cap ∧
    momentPower (degree j) (pathHeight (degree j)) ≤ cap ∧
    failureDen (degree j) ≤ cap ∧ accuracyDen (degree j) ≤ cap ∧
    sweepEnvelope (degree j) (pathHeight (degree j))
      (failureDen (degree j)) (accuracyDen (degree j)) ≤ cap := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Recipe.degree.value_le_need j).trans ((Recipe.degree_need j).trans hcap)
  · exact (Recipe.height.value_le_need j).trans ((Recipe.height_need j).trans hcap)
  · exact (Recipe.comparable.value_le_need j).trans ((Recipe.comparable_need j).trans hcap)
  · exact (alphabetExponent_le _ _).trans
      ((Recipe.alphabetExponent.value_le_need j).trans ((Recipe.exponent_need j).trans hcap))
  · exact (alphabet_le _ _).trans
      ((Recipe.alphabet.value_le_need j).trans ((Recipe.alphabet_need j).trans hcap))
  · exact (momentPower_le_envelope _ _).trans
      ((Recipe.moment.value_le_need j).trans ((Recipe.moment_need j).trans hcap))
  · exact (Recipe.failure.value_le_need j).trans ((Recipe.failure_need j).trans hcap)
  · exact (Recipe.accuracy.value_le_need j).trans ((Recipe.accuracy_need j).trans hcap)
  · exact (Recipe.sweeps.value_le_need j).trans ((Recipe.sweeps_need j).trans hcap)

theorem admitted_sweepCount (j cap : ℕ) (hcap : Recipe.budget.need j ≤ cap) :
    sweepCount (degree j) (pathHeight (degree j))
      (CertificateSuccess.accuracy (degree j) (neighborhoodBound (degree j) (pathHeight (degree j)))
        (widthThreshold (degree j) (pathHeight (degree j))))
      (CertificateSuccess.failure (degree j))
      (CertificateSuccess.accuracy_pos (degree_pos j) _ (widthThreshold_pos _ _))
      (CertificateSuccess.failure_pos (degree_pos j)) ≤ cap := by
  simp_rw [accuracy_eq, failure_eq]
  apply (sweepCount_le_envelope _ _ _ _ (failureDen_pos (degree_pos j))
    (accuracyDen_pos (degree_pos j)) _ _).trans
  exact (Recipe.sweeps.value_le_need j).trans ((Recipe.sweeps_need j).trans hcap)

theorem selected_stage_tendsto : Tendsto selectedStage atTop atTop :=
  CappedStageScan.stage_tendsto Recipe.budget

theorem selected_parameter_tendsto : Tendsto (fun n => degree (selectedStage n)) atTop atTop := by
  apply Filter.tendsto_atTop_mono (fun n => ?_) selected_stage_tendsto
  exact (Nat.le_add_right _ 5).trans (Nat.lt_two_pow_self.le)

theorem eventually_selected : ∀ᶠ n in atTop, selected n ≠ none := by
  have hh := (tendsto_atTop.1 selected_stage_tendsto) 1
  filter_upwards [hh] with n hn
  simp [selected, show selectedStage n ≠ 0 by omega]

/-- This bound includes every rejected stage and every capped power call. -/
theorem selection_work (n : ℕ) :
    (CappedStageScan.select Recipe.budget n).work ≤
      n * (Recipe.budget.nodes * (5 * (n + 1) + 2) + 1) :=
  CappedStageScan.selected_work_polynomial Recipe.budget n

/-- All intermediate magnitudes of the actual bounded selector have a
fixed polynomial bound independent of the eventually selected parameter. -/
theorem selection_peak (n : ℕ) :
    (CappedStageScan.select Recipe.budget n).peak ≤
      (n + Recipe.budget.literalMax + 1) ^ 2 := by
  apply (CappedStageScan.selected_peak Recipe.budget n _ le_rfl).trans
  exact Nat.pow_le_pow_left (by have := Optimal.Parameters.logCap_le_input n; omega) 2

theorem selected_overhead_tendsto :
    Tendsto (fun n => prefixOverhead (degree (selectedStage n))) atTop (𝓝 0) :=
  Continuous.selected_overhead_tendsto _ selected_parameter_tendsto

theorem selected_error_tendsto :
    Tendsto (fun n => prefixOverhead (degree (selectedStage n)) /
      (1 + prefixOverhead (degree (selectedStage n)))) atTop (𝓝 0) :=
  Continuous.selected_error_tendsto _ selected_parameter_tendsto

end SortingAdversary.Continuous.UniformStages
