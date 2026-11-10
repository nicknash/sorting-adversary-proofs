import SortingAdversary.Continuous.EnclosureDistribution
import SortingAdversary.Continuous.EnclosureParameters

/-!
# Calibrated width guarantee for the executable enclosure list

The finite list is the algorithm's actual enumeration. Its bad-width fraction
is bounded by transferring the full-sweep moment estimate through exact finite
dependence and the explicit marginalization identity. The final theorem uses
the computable parameters, rather than assuming their success.
-/

namespace SortingAdversary.Continuous.FiniteAveraging

open SortingAdversary.Optimal.FiniteProbability
open SortingAdversary.Optimal.GraphBalls
open scoped BigOperators

theorem countP_eq_sum_indicator {α : Type*} (L : List α) (P : α → Bool) :
    (L.countP P : ℚ) = (L.map (fun a => if P a then (1 : ℚ) else 0)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    cases h : P a <;> simp [List.countP_cons, h, ih, add_comm]

/-- Probability is independent of the decision procedure for its event. -/
theorem probability_congr_event {Ω : Type*} [Fintype Ω]
    {P Q : Ω → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ ω, P ω ↔ Q ω) : probability P = probability Q := by
  apply mean_congr
  intro ω
  by_cases hp : P ω
  · simp [indicator, hp, (h ω).mp hp]
  · have hq : ¬ Q ω := fun hq => hp ((h ω).mpr hq)
    simp [indicator, hp, hq]

variable {n S : ℕ}

/-- The retained interior is swept in its inherited topological order. -/
def localSchedule (F : Finset (Fin n)) (t : ℕ) : List (Fin n) :=
  repeatSchedule ((List.finRange n).filter fun x => x ∈ F) t

def localEnclose (D : System (Fin n) ℚ) (S : ℕ) (F : Finset (Fin n))
    (t : ℕ) : List (Fin n → ℚ × ℚ) := enclose D S (localSchedule F t)

@[simp] theorem localEnclose_length (D : System (Fin n) ℚ) (S : ℕ)
    (F : Finset (Fin n)) (t : ℕ) :
    (localEnclose D S F t).length = S ^ (F.card * t) := by
  simp only [localEnclose, enclose_length, localSchedule, repeatSchedule_length]
  congr 2
  have hall : ((List.finRange n).filter fun x => x ∈ F).toFinset = F := by
    ext x
    simp
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _), hall]

def badWidth (Q : Finset (Fin n)) (δ : ℚ) (entry : Fin n → ℚ × ℚ) : Bool :=
  decide (∃ v ∈ Q, δ < (entry v).2 - (entry v).1)

section Distribution

variable [NeZero S]

theorem localEnclose_probability_eq_history (D : System (Fin n) ℚ)
    (F : Finset (Fin n)) (t : ℕ) (P : ((Fin n → ℚ) × (Fin n → ℚ)) → Prop)
    [DecidablePred P] :
    ((localEnclose D S F t).countP (fun entry => decide (P (entryState entry))) : ℚ) /
        (localEnclose D S F t).length =
      probability (fun history : SweepHistory n S t =>
        P (iterateMaskedSweep D F D.lower t history, iterateMaskedSweep D F D.upper t history)) := by
  rw [countP_eq_sum_indicator]
  unfold probability indicator
  simpa only [localEnclose, localSchedule, decide_eq_true_eq] using
    enclose_average_eq_masked_history (S := S) D F t (fun state => if P state then 1 else 0)

/-- The actual list fraction with a wide queried coordinate is small. -/
theorem localEnclose_width_probability (D : System (Fin n) ℚ)
    (horder : ∀ x y, D.edge x y = true → x.val < y.val)
    (hwidth : ∀ x, D.lower x ≤ D.upper x) (hunit : ∀ x, D.upper x - D.lower x ≤ 1)
    (rank : Fin n → ℕ) (H p M : ℕ) (hp : 0 < p) (hM : 0 < M)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hanc : ∀ v, (graphRegion D v rank H hrank hheight).ancestors.card ≤ M)
    (hdep : ∀ v, (graphRegion D v rank H hrank hheight).dependencies.card ≤ M)
    (hS : 4 * M ^ 2 ≤ S)
    (hpower : (1 - (1 / (S : ℚ)) ^ H) ^ p ≤ 1 / (4 * (M : ℚ)))
    (F Q : Finset (Fin n)) (t : ℕ)
    (hF : ∀ v ∈ Q, ball D.edge v (H * t) ⊆ F) (δ : ℚ) (hδ : 0 < δ) :
    ((localEnclose D S F t).countP (badWidth Q δ) : ℚ) /
        (localEnclose D S F t).length ≤
      Q.card * ((1 / 2 : ℚ) ^ t / δ ^ p) := by
  classical
  have he := localEnclose_probability_eq_history (S := S) D F t
    (fun state => ∃ v ∈ Q, δ < state.2 v - state.1 v)
  change _ = probability _ at he
  have hmean : probability (fun history : SweepHistory n S t =>
      ∃ v ∈ Q, δ < iterateMaskedSweep D F D.upper t history v -
        iterateMaskedSweep D F D.lower t history v) =
      probability (fun history : SweepHistory n S t =>
      ∃ v ∈ Q, δ < iterateSweep D D.upper t history v - iterateSweep D D.lower t history v) := by
    apply mean_congr
    intro history
    simp only [indicator]
    congr 1
    apply propext
    constructor <;> rintro ⟨v, hv, hw⟩ <;> refine ⟨v, hv, ?_⟩
    · simpa only [iterateSweep_eq_masked D horder rank H hrank hheight F D.upper t history v (hF v hv),
        iterateSweep_eq_masked D horder rank H hrank hheight F D.lower t history v (hF v hv)] using hw
    · simpa only [iterateSweep_eq_masked D horder rank H hrank hheight F D.upper t history v (hF v hv),
        iterateSweep_eq_masked D horder rank H hrank hheight F D.lower t history v (hF v hv)] using hw
  change _ = _ at he
  rw [show badWidth Q δ = (fun entry => decide
      (∃ v ∈ Q, δ < (entryState entry).2 v - (entryState entry).1 v)) from rfl, he, hmean]
  have hUnion : probability (fun history : SweepHistory n S t =>
      ∃ v ∈ Q, δ < iterateSweep D D.upper t history v - iterateSweep D D.lower t history v) ≤
      ∑ v ∈ Q, probability (fun history : SweepHistory n S t =>
        δ < iterateSweep D D.upper t history v - iterateSweep D D.lower t history v) := by
    unfold probability
    rw [← mean_sum]
    apply mean_mono
    intro history
    by_cases hb : ∃ v ∈ Q,
        δ < iterateSweep D D.upper t history v - iterateSweep D D.lower t history v
    · obtain ⟨v, hv, hw⟩ := hb
      simp only [indicator, if_pos (show ∃ v ∈ Q,
        δ < iterateSweep D D.upper t history v - iterateSweep D D.lower t history v from ⟨v, hv, hw⟩)]
      have hs := Finset.single_le_sum (s := Q) (f := fun w =>
        if δ < iterateSweep D D.upper t history w - iterateSweep D D.lower t history w
          then (1 : ℚ) else 0) (fun _ _ => by split <;> norm_num) hv
      simpa only [if_pos hw] using hs
    · simp only [indicator, if_neg hb]
      exact Finset.sum_nonneg (fun _ _ => by split <;> norm_num)
  apply hUnion.trans
  calc
    _ ≤ ∑ _v ∈ Q, ((1 / 2 : ℚ) ^ t / δ ^ p) := by
      apply Finset.sum_le_sum
      intro v _
      exact iterateSweep_width_probability D horder D.lower D.upper hwidth hunit H p M hp hM
        (fun v => graphRegion D v rank H hrank hheight) hanc hdep hS hpower t v δ hδ
    _ = Q.card * ((1 / 2 : ℚ) ^ t / δ ^ p) := by simp
    _ ≤ Q.card * ((1 / 2 : ℚ) ^ t / δ ^ p) := le_rfl

end Distribution

open EnclosureParameters

/-- Exactly the vertices whose distance from some query is less than
`radius = H*t+1`; the adjacent boundary is kept frozen. -/
def queryInterior (D : System (Fin n) ℚ) (Q : Finset (Fin n)) (H t : ℕ) : Finset (Fin n) :=
  Q.biUnion fun v => ball D.edge v (H * t)

theorem queryInterior_contains (D : System (Fin n) ℚ) (Q : Finset (Fin n)) (H t : ℕ)
    (v : Fin n) (hv : v ∈ Q) : ball D.edge v (H * t) ⊆ queryInterior D Q H t := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨v, hv, hx⟩

theorem queryInterior_card (D : System (Fin n) ℚ) (Q : Finset (Fin n)) (d H t : ℕ)
    (hdegree : ∀ x, (neighbors D.edge x).card ≤ d) :
    (queryInterior D Q H t).card ≤ Q.card * (d + 1) ^ (H * t) := by
  calc
    _ ≤ ∑ v ∈ Q, (ball D.edge v (H * t)).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ Q, (d + 1) ^ (H * t) :=
      Finset.sum_le_sum (fun v _ => ball_card_le D.edge d hdegree v _)
    _ = _ := by simp

/-- The paper's fully calibrated finite enumeration, with rational accuracy
and failure targets. Every searched inequality is decidable. -/
def calibratedEnclose (D : System (Fin n) ℚ) (d H : ℕ) (Q : Finset (Fin n))
    (δ α : ℚ) (hδ : 0 < δ) (hα : 0 < α) : List (Fin n → ℚ × ℚ) :=
  let t := sweepCount d H δ α hδ hα
  localEnclose D (alphabet d H) (queryInterior D Q H t) t

def calibratedSchedule (D : System (Fin n) ℚ) (d H : ℕ) (Q : Finset (Fin n))
    (δ α : ℚ) (hδ : 0 < δ) (hα : 0 < α) : List (Fin n) :=
  let t := sweepCount d H δ α hδ hα
  localSchedule (queryInterior D Q H t) t

theorem calibratedEnclose_eq_enclose (D : System (Fin n) ℚ) (d H : ℕ) (Q : Finset (Fin n))
    (δ α : ℚ) (hδ : 0 < δ) (hα : 0 < α) :
    calibratedEnclose D d H Q δ α hδ hα =
      enclose D (alphabet d H) (calibratedSchedule D d H Q δ α hδ hα) := rfl

/-- Operational local enclosure theorem. The actual returned list has at
most an `α` fraction of entries with a queried width greater than `δ`.
The graph, interval and query hypotheses are the paper's finite invariants;
no probability estimate or success certificate is supplied as a premise. -/
theorem calibratedEnclose_width_probability (D : System (Fin n) ℚ)
    (horder : ∀ x y, D.edge x y = true → x.val < y.val)
    (hwidth : ∀ x, D.lower x ≤ D.upper x) (hunit : ∀ x, D.upper x - D.lower x ≤ 1)
    (rank : Fin n → ℕ) (d H : ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (neighbors D.edge x).card ≤ d)
    (Q : Finset (Fin n)) (hQ : Q.card ≤ 2)
    (δ α : ℚ) (hδ : 0 < δ) (hα : 0 < α) :
    ((calibratedEnclose D d H Q δ α hδ hα).countP (badWidth Q δ) : ℚ) /
        (calibratedEnclose D d H Q δ α hδ hα).length ≤ α := by
  letI : NeZero (alphabet d H) := ⟨(EnclosureParameters.alphabet_pos d H).ne'⟩
  let t := sweepCount d H δ α hδ hα
  let F := queryInterior D Q H t
  have h := localEnclose_width_probability (S := alphabet d H) D horder hwidth hunit
    rank H (momentPower d H) (neighborhoodBound d H) (momentPower_pos d H)
    (neighborhoodBound_pos d H) hrank hheight
    (fun v => graphRegion_ancestors_card D v rank H d hrank hheight hdegree)
    (fun v => graphRegion_dependencies_card D v rank H d hrank hheight hdegree)
    (alphabet_large d H) (momentPower_spec d H) F Q t
    (fun v hv => queryInterior_contains D Q H t v hv) δ hδ
  change _ ≤ _ at h
  change ((localEnclose D (alphabet d H) F t).countP (badWidth Q δ) : ℚ) /
    (localEnclose D (alphabet d H) F t).length ≤ α
  calc
    _ ≤ (Q.card : ℚ) * ((1 / 2 : ℚ) ^ t / δ ^ momentPower d H) := h
    _ ≤ 2 * ((1 / 2 : ℚ) ^ t / δ ^ momentPower d H) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hQ) (by positivity)
    _ = (2 * (1 / 2 : ℚ) ^ t) / δ ^ momentPower d H := by ring
    _ ≤ α := by
      apply (div_le_iff₀ (pow_pos hδ _)).mpr
      have hs := sweepCount_spec d H δ α hδ hα
      change (1 / 2 : ℚ) ^ t ≤ α * δ ^ momentPower d H / 2 at hs
      linarith

theorem calibratedEnclose_nonempty (D : System (Fin n) ℚ) (d H : ℕ)
    (Q : Finset (Fin n)) (δ α : ℚ) (hδ : 0 < δ) (hα : 0 < α) :
    calibratedEnclose D d H Q δ α hδ hα ≠ [] := by
  intro h
  have hp : 0 < (calibratedEnclose D d H Q δ α hδ hα).length := by
    simp only [calibratedEnclose, localEnclose_length]
    exact pow_pos (EnclosureParameters.alphabet_pos d H) _
  simpa [h] using hp

theorem calibratedEnclose_length_dvd_four (D : System (Fin n) ℚ) (d H : ℕ)
    (Q : Finset (Fin n)) (hQ : Q.Nonempty) (δ α : ℚ) (hδ : 0 < δ) (hα : 0 < α) :
    4 ∣ (calibratedEnclose D d H Q δ α hδ hα).length := by
  simp only [calibratedEnclose, localEnclose_length]
  apply (four_dvd_alphabet d H).pow
  apply Nat.mul_ne_zero
  · apply Nat.ne_of_gt
    apply Finset.card_pos.mpr
    obtain ⟨v, hv⟩ := hQ
    exact ⟨v, queryInterior_contains D Q H _ v hv (center_mem_ball D.edge v _)⟩
  · exact (sweepCount_pos d H δ α hδ hα).ne'

theorem calibratedEnclose_length_le (D : System (Fin n) ℚ) (d H : ℕ)
    (Q : Finset (Fin n)) (hQ : Q.card ≤ 2)
    (hdegree : ∀ x, (neighbors D.edge x).card ≤ d)
    (δ α : ℚ) (hδ : 0 < δ) (hα : 0 < α) :
    (calibratedEnclose D d H Q δ α hδ hα).length ≤ enumerationBound d H δ α hδ hα := by
  simp only [calibratedEnclose, localEnclose_length, enumerationBound]
  apply Nat.pow_le_pow_right (EnclosureParameters.alphabet_pos d H)
  apply Nat.mul_le_mul_right
  calc
    _ ≤ Q.card * (d + 1) ^ (H * sweepCount d H δ α hδ hα) :=
      queryInterior_card D Q d H _ hdegree
    _ ≤ 2 * (d + 1) ^ (H * sweepCount d H δ α hδ hα) := Nat.mul_le_mul_right _ hQ
    _ ≤ retainedBound d H δ α hδ hα := by
      unfold retainedBound radius
      exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) (by omega))

end SortingAdversary.Continuous.FiniteAveraging
