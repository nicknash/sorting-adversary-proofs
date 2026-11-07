import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact finite probability for the auxiliary local coupling

Every expectation in this file is a finite rational average.  Product sample
spaces give actual independent randomness, rather than an independence axiom.
The large common clock palette is used only by the proof of the local oracle.
-/

namespace SortingAdversary.Optimal.FiniteProbability

open scoped BigOperators

/-- Uniform expectation on an explicit finite sample space. -/
def mean {Ω : Type*} [Fintype Ω] (f : Ω → ℚ) : ℚ :=
  (∑ ω, f ω) / Fintype.card Ω

section Mean
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

private theorem card_pos : (0 : ℚ) < Fintype.card Ω := by
  exact_mod_cast Fintype.card_pos

theorem mean_nonneg {f : Ω → ℚ} (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ mean f :=
  div_nonneg (Finset.sum_nonneg fun ω _ => hf ω) card_pos.le

theorem mean_mono {f g : Ω → ℚ} (h : ∀ ω, f ω ≤ g ω) : mean f ≤ mean g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => h ω) card_pos.le

@[simp] theorem mean_const (c : ℚ) : mean (fun _ : Ω => c) = c := by
  unfold mean
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c (ne_of_gt (card_pos (Ω := Ω)))

omit [Nonempty Ω] in
theorem mean_add (f g : Ω → ℚ) : mean (fun ω => f ω + g ω) = mean f + mean g := by
  simp [mean, Finset.sum_add_distrib, add_div]

omit [Nonempty Ω] in
theorem mean_sub (f g : Ω → ℚ) : mean (fun ω => f ω - g ω) = mean f - mean g := by
  simp [mean, Finset.sum_sub_distrib, sub_div]

omit [Nonempty Ω] in
theorem mean_mul_const (f : Ω → ℚ) (c : ℚ) : mean (fun ω => f ω * c) = mean f * c := by
  unfold mean
  rw [← Finset.sum_mul]
  ring

omit [Nonempty Ω] in
theorem mean_const_mul (c : ℚ) (f : Ω → ℚ) : mean (fun ω => c * f ω) = c * mean f := by
  simp_rw [mul_comm c]
  rw [mean_mul_const, mul_comm]

omit [Nonempty Ω] in
theorem mean_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℚ) :
    mean (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, mean (f i) := by
  unfold mean
  rw [Finset.sum_comm, Finset.sum_div]

/-- Indicator functions take rational values zero and one. -/
def indicator (P : Ω → Prop) [DecidablePred P] (ω : Ω) : ℚ := if P ω then 1 else 0

omit [Fintype Ω] [Nonempty Ω] in
@[simp] theorem indicator_nonneg (P : Ω → Prop) [DecidablePred P] (ω : Ω) :
    0 ≤ indicator P ω := by simp [indicator]; split <;> norm_num

omit [Fintype Ω] [Nonempty Ω] in
theorem indicator_le_one (P : Ω → Prop) [DecidablePred P] (ω : Ω) :
    indicator P ω ≤ 1 := by unfold indicator; split <;> norm_num

/-- Probability as a rational relative cardinality. -/
def probability (P : Ω → Prop) [DecidablePred P] : ℚ := mean (indicator P)

theorem probability_nonneg (P : Ω → Prop) [DecidablePred P] : 0 ≤ probability P :=
  mean_nonneg (indicator_nonneg P)

theorem probability_le_one (P : Ω → Prop) [DecidablePred P] : probability P ≤ 1 := by
  exact (mean_mono (indicator_le_one P)).trans_eq (mean_const 1)

omit [Nonempty Ω] in
theorem probability_eq_card (P : Ω → Prop) [DecidablePred P] :
    probability P = ((Finset.univ.filter P).card : ℚ) / Fintype.card Ω := by
  simp [probability, mean, indicator]

/-- A union bound over an actual finite family of events. -/
theorem probability_exists_le_sum {ι : Type*} (s : Finset ι)
    (P : ι → Ω → Prop) [∀ i, DecidablePred (P i)] :
    probability (fun ω => ∃ i ∈ s, P i ω) ≤ ∑ i ∈ s, probability (P i) := by
  classical
  unfold probability
  rw [← mean_sum]
  apply mean_mono
  intro ω
  by_cases h : ∃ i ∈ s, P i ω
  · obtain ⟨i, hi, hPi⟩ := h
    simp only [indicator, if_pos (show ∃ i ∈ s, P i ω from ⟨i, hi, hPi⟩)]
    have hle := Finset.single_le_sum (fun j (_ : j ∈ s) =>
      show (0 : ℚ) ≤ if P j ω then 1 else 0 by split <;> norm_num) hi
    simpa [hPi] using hle
  · simp only [indicator, if_neg h]
    exact Finset.sum_nonneg fun i _ => indicator_nonneg (P i) ω

/-- Markov's inequality proved directly by comparing finite summands. -/
theorem probability_le_mean_div {f : Ω → ℚ} (hf : ∀ ω, 0 ≤ f ω)
    {a : ℚ} (ha : 0 < a) : probability (fun ω => a < f ω) ≤ mean f / a := by
  apply (le_div_iff₀ ha).mpr
  unfold probability
  rw [← mean_mul_const]
  apply mean_mono
  intro ω
  unfold indicator
  split_ifs with h
  · simpa using h.le
  · simpa using hf ω

/-- A bounded variable has a small mean if it is uniformly small off a rare
bad event. This is the only probability decomposition needed for clock minima. -/
theorem mean_le_bad_probability_add {f : Ω → ℚ} (P : Ω → Prop) [DecidablePred P]
    {c : ℚ} (hc : 0 ≤ c) (hf1 : ∀ ω, f ω ≤ 1)
    (hgood : ∀ ω, ¬ P ω → f ω ≤ c) : mean f ≤ probability P + c := by
  unfold probability
  rw [← mean_const (Ω := Ω) c, ← mean_add]
  apply mean_mono
  intro ω
  by_cases hP : P ω
  · simp [indicator, hP]
    linarith [hf1 ω]
  · simpa [indicator, hP] using hgood ω hP

/-- Absolute values commute with averaging in the usual one-sided direction. -/
theorem abs_mean_le (f : Ω → ℚ) : |mean f| ≤ mean (fun ω => |f ω|) := by
  unfold mean
  rw [abs_div, abs_of_pos (card_pos (Ω := Ω))]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) card_pos.le

theorem probability_mono {P Q : Ω → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ ω, P ω → Q ω) : probability P ≤ probability Q := by
  apply mean_mono
  intro ω
  unfold indicator
  split_ifs with hP hQ
  · exact le_refl _
  · exact False.elim (hQ (h ω hP))
  · norm_num
  · exact le_refl _

/-- A coupling bounds the difference of event probabilities by its actual
disagreement probability. No condition on the dependence between events is used. -/
theorem probability_difference_le_disagreement (P Q : Ω → Prop)
    [DecidablePred P] [DecidablePred Q] :
    |probability P - probability Q| ≤ probability (fun ω => ¬ (P ω ↔ Q ω)) := by
  unfold probability
  rw [← mean_sub]
  apply (abs_mean_le _).trans
  apply mean_mono
  intro ω
  by_cases hP : P ω <;> by_cases hQ : Q ω <;> simp [indicator, hP, hQ]

/-- A union bound for two events, convenient for bad-clock and near-tie events. -/
theorem probability_or_le (P Q : Ω → Prop) [DecidablePred P] [DecidablePred Q] :
    probability (fun ω => P ω ∨ Q ω) ≤ probability P + probability Q := by
  unfold probability
  rw [← mean_add]
  apply mean_mono
  intro ω
  by_cases hP : P ω <;> by_cases hQ : Q ω <;> norm_num [indicator, hP, hQ]

/-- The deterministic implication underlying comparison locality. If neither
coordinate is badly coupled, a sign disagreement forces a near tie in the
first system, even when the two coordinates are statistically dependent. -/
theorem comparison_disagreement_near_tie {x y x' y' a b : ℚ}
    (hx : |x - x'| ≤ a) (hy : |y - y'| ≤ b)
    (h : ¬ ((x ≤ y) ↔ (x' ≤ y'))) : |x - y| ≤ a + b := by
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  apply abs_le.mpr
  by_cases hxy : x ≤ y
  · have hxy' : y' < x' := lt_of_not_ge (fun hh => h ⟨fun _ => hh, fun _ => hxy⟩)
    constructor <;> linarith
  · have hxy' : x' ≤ y' := by
      by_contra hh
      exact h ⟨fun hbad => False.elim (hxy hbad), fun hbad => False.elim (hh hbad)⟩
    constructor <;> linarith

/-- Explicit comparison error from a supplied finite coupling. This theorem
uses the actual joint events and does not assume a local/full error estimate. -/
theorem comparison_probability_error (x y x' y' : Ω → ℚ) (a b : ℚ) :
    |probability (fun ω => x ω ≤ y ω) - probability (fun ω => x' ω ≤ y' ω)| ≤
      probability (fun ω => a < |x ω - x' ω|) +
      probability (fun ω => b < |y ω - y' ω|) +
      probability (fun ω => |x ω - y ω| ≤ a + b) := by
  apply (probability_difference_le_disagreement _ _).trans
  have hle := probability_mono (P := fun ω => ¬ ((x ω ≤ y ω) ↔ (x' ω ≤ y' ω)))
    (Q := fun ω => (a < |x ω - x' ω| ∨ b < |y ω - y' ω|) ∨ |x ω - y ω| ≤ a + b)
    (fun ω h => by
      by_cases hx : a < |x ω - x' ω|
      · exact Or.inl (Or.inl hx)
      by_cases hy : b < |y ω - y' ω|
      · exact Or.inl (Or.inr hy)
      exact Or.inr (comparison_disagreement_near_tie (le_of_not_gt hx) (le_of_not_gt hy) h))
  apply hle.trans
  apply (probability_or_le _ _).trans
  exact add_le_add (probability_or_le
    (fun ω => a < |x ω - x' ω|) (fun ω => b < |y ω - y' ω|)) le_rfl

end Mean

section Products
variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] [Nonempty Ω] [Nonempty Γ]

omit [Nonempty Ω] [Nonempty Γ] in
/-- Fubini for finite uniform averages. -/
theorem mean_product (f : Ω × Γ → ℚ) :
    mean f = mean (fun ω => mean (fun γ => f (ω, γ))) := by
  unfold mean
  rw [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type, ← Finset.sum_div, div_div]
  ring

omit [Nonempty Ω] [Nonempty Γ] in
/-- Independent factors multiply because the underlying samples form a
Cartesian product. -/
theorem mean_independent_mul (f : Ω → ℚ) (g : Γ → ℚ) :
    mean (fun p : Ω × Γ => f p.1 * g p.2) = mean f * mean g := by
  rw [mean_product]
  simp only [mean_const_mul, mean_mul_const]

end Products


/-- Relabelling a finite uniform sample space preserves every expectation. -/
theorem mean_equiv {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] (e : Ω ≃ Γ) (f : Γ → ℚ) :
    mean (fun ω => f (e ω)) = mean f := by
  unfold mean
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- Finite expectations commute on a product sample space. -/
theorem mean_comm {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] (f : Ω → Γ → ℚ) :
    mean (fun ω => mean (f ω)) = mean (fun γ => mean (fun ω => f ω γ)) := by
  unfold mean
  rw [← Finset.sum_div, ← Finset.sum_div, div_div, div_div, Finset.sum_comm, mul_comm]

/-- Pointwise equality is enough to identify finite expectations. -/
theorem mean_congr {Ω : Type*} [Fintype Ω] {f g : Ω → ℚ} (h : ∀ ω, f ω = g ω) :
    mean f = mean g := congrArg mean (funext h)

/-- A finite mean does not depend on the chosen enumeration instance. -/
theorem mean_congr_fintype {Ω : Type*} (I J : Fintype Ω) {f g : Ω → ℚ}
    (h : ∀ ω, f ω = g ω) : @mean Ω I f = @mean Ω J g := by
  cases Subsingleton.elim I J
  exact congrArg (@mean Ω I) (funext h)

/-- A single coordinate of a uniform finite product is itself uniform. -/
theorem mean_pi_apply {ι Γ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Γ] [Nonempty Γ] (i : ι) (f : Γ → ℚ) :
    mean (fun ω : ι → Γ => f (ω i)) = mean f := by
  let e := Equiv.piSplitAt i (fun _ : ι => Γ)
  have he : mean (fun ω : ι → Γ => f (ω i)) =
      mean (fun p : Γ × (∀ j : { j : ι // j ≠ i }, Γ) => f p.1) := by
    exact mean_equiv e (fun p => f p.1)
  rw [he, mean_product]
  simp

/-- An elementary replacement for the exponential high-moment estimate. -/
theorem one_sub_pow_le_inv_one_add_mul {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (s : ℕ) :
    (1 - x) ^ s ≤ (1 + s * x)⁻¹ := by
  have hden : 0 < 1 + (s : ℚ) * x := by positivity
  rw [← one_div]
  apply (le_div_iff₀ hden).mpr
  clear hden
  induction s with
  | zero => simp
  | succ s ih =>
    have hpow : 0 ≤ (1 - x) ^ s := pow_nonneg (sub_nonneg.mpr hx1) _
    have hsn : 0 ≤ (s : ℚ) * x ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hfactor :
        (1 - x) * (1 + ((s : ℚ) + 1) * x) ≤ 1 + (s : ℚ) * x := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hfactor hpow
    rw [pow_succ, Nat.cast_succ]
    nlinarith

end SortingAdversary.Optimal.FiniteProbability
