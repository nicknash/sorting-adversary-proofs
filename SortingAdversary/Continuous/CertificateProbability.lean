import SortingAdversary.Continuous.Certificates
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Card

/-!
# Probability meaning of the finite interval certificates

A uniform entry may be coupled to continuously distributed positions. The
positions need not be functions of the entry, and no independence between the
entry and the positions is assumed. Pointwise (or almost-everywhere) enclosure
is precisely what turns a finite count into a lower probability bound.

This file proves that conversion using an actual measure. Constructing the
uniform feasible-region coupling for the full adversary is a separate theorem.
-/

namespace SortingAdversary.Continuous.Certificates

open MeasureTheory Set
open scoped BigOperators ENNReal

section UniformEntry

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- A sound event on a uniform finite entry has the expected counting lower
bound, even when its soundness is only almost everywhere. -/
theorem uniform_entry_bound (μ : Measure Ω) (entry : Ω → ι)
    (hfinite : ∀ i, MeasurableSet (entry ⁻¹' {i}))
    (huniform : ∀ i, μ (entry ⁻¹' {i}) = (Fintype.card ι : ℝ≥0∞)⁻¹)
    (s : Finset ι) (event : Set Ω)
    (hsound : ∀ᵐ ω ∂μ, entry ω ∈ s → ω ∈ event) :
    (s.card : ℝ≥0∞) / Fintype.card ι ≤ μ event := by
  have hmass : μ (entry ⁻¹' (s : Set ι)) =
      (s.card : ℝ≥0∞) / Fintype.card ι := by
    rw [← sum_measure_preimage_singleton s (fun i _ => hfinite i)]
    simp only [huniform, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  rw [← hmass]
  exact measure_mono_ae hsound

theorem separated_probability_bound (μ : Measure Ω) (entry : Ω → ι)
    (hfinite : ∀ i, MeasurableSet (entry ⁻¹' {i}))
    (huniform : ∀ i, μ (entry ⁻¹' {i}) = (Fintype.card ι : ℝ≥0∞)⁻¹)
    (intervals : ι → ComparisonIntervals) (x y : Ω → ℝ)
    (henclose : ∀ᵐ ω ∂μ, (intervals (entry ω)).1.Contains (x ω) ∧
      (intervals (entry ω)).2.Contains (y ω)) :
    ((Finset.univ.filter (fun i => separated (intervals i))).card : ℝ≥0∞) /
      Fintype.card ι ≤ μ {ω | x ω < y ω} := by
  apply uniform_entry_bound μ entry hfinite huniform
  filter_upwards [henclose] with ω hω hi
  exact separated_sound hω.1 hω.2 (Finset.mem_filter.mp hi).2

theorem reverseSeparated_probability_bound (μ : Measure Ω) (entry : Ω → ι)
    (hfinite : ∀ i, MeasurableSet (entry ⁻¹' {i}))
    (huniform : ∀ i, μ (entry ⁻¹' {i}) = (Fintype.card ι : ℝ≥0∞)⁻¹)
    (intervals : ι → ComparisonIntervals) (x y : Ω → ℝ)
    (henclose : ∀ᵐ ω ∂μ, (intervals (entry ω)).1.Contains (x ω) ∧
      (intervals (entry ω)).2.Contains (y ω)) :
    ((Finset.univ.filter (fun i => reverseSeparated (intervals i))).card : ℝ≥0∞) /
      Fintype.card ι ≤ μ {ω | y ω < x ω} := by
  apply uniform_entry_bound μ entry hfinite huniform
  filter_upwards [henclose] with ω hω hi
  exact reverseSeparated_sound hω.1 hω.2 (Finset.mem_filter.mp hi).2

end UniformEntry

/-- The index count preserves list multiplicity: equal interval values remain
different entries. This is why repetitions in `Enclose` must not be removed. -/
theorem index_count_eq_countP {α : Type*} (L : List α) (p : α → Bool) :
    (Finset.univ.filter (fun i : Fin L.length => p (L.get i))).card = L.countP p := by
  classical
  have hall : (List.finRange L.length).toFinset = Finset.univ := by
    ext i
    simp
  have hc := (List.nodup_finRange L.length).card_eq_countP
    (P := fun i => p (L.get i))
  rw [hall] at hc
  have hm : (List.finRange L.length).map L.get = L := by
    rw [← List.ofFn_eq_map, List.ofFn_get]
  have hcount := congrArg (List.countP p) hm
  simp only [List.countP_map, Function.comp_def] at hcount
  calc
    _ = (List.finRange L.length).countP (fun i => p (L.get i)) := by simpa using hc
    _ = L.countP p := hcount

/-- Direct interpretation of the exact list count used by `selectAnswer`. -/
theorem list_lower_probability_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (L : List ComparisonIntervals) (entry : Ω → Fin L.length)
    (hfinite : ∀ i, MeasurableSet (entry ⁻¹' {i}))
    (huniform : ∀ i, μ (entry ⁻¹' {i}) = (L.length : ℝ≥0∞)⁻¹)
    (x y : Ω → ℝ)
    (henclose : ∀ᵐ ω ∂μ, (L.get (entry ω)).1.Contains (x ω) ∧
      (L.get (entry ω)).2.Contains (y ω)) :
    (L.countP separated : ℝ≥0∞) / L.length ≤ μ {ω | x ω < y ω} := by
  have h := separated_probability_bound μ entry hfinite
    (by simpa using huniform) L.get x y henclose
  simpa only [index_count_eq_countP, Fintype.card_fin] using h

end SortingAdversary.Continuous.Certificates
