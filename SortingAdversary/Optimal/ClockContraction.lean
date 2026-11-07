import SortingAdversary.Optimal.LocalCoupling
import SortingAdversary.Optimal.FiniteProbability
import Mathlib.Data.Fin.Rev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Fold

/-!
# High-moment contraction from actual finite common clocks

This is the clock estimate in the manuscript. Uniform clocks have a finite
alphabet divisible by every conditional interval width. Their arithmetic is
exact; a Cartesian product gives fresh independent clocks at each vertex.
-/

namespace SortingAdversary.Optimal.ClockContraction

open LocalCoupling FiniteProbability
open scoped BigOperators

/-- The reflected grid has no rounding loss in its small-tail probability:
its values are `1/Q,...,1`, with zero excluded. -/
theorem clock_small_probability {Q : ℕ} (hQ : 0 < Q) (a : ℚ) (ha : 0 ≤ a) :
    probability (fun r : Fin Q => 1 - gridClock r < a) ≤ a := by
  let : NeZero Q := ⟨hQ.ne'⟩
  let T : Finset (Fin Q) := Finset.univ.filter (fun r => 1 - gridClock r < a)
  have hQ' : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hbound (r : ↥T) : (Fin.rev r.val).val < ⌊a * Q⌋₊ := by
    have hr : 1 - (r.val.val : ℚ) / Q < a := (Finset.mem_filter.mp r.property).2
    have hmul : (Q : ℚ) - r.val.val < a * Q := by
      have := (div_lt_iff₀ hQ').mp (show ((Q : ℚ) - r.val.val) / Q < a by
        calc
          _ = 1 - (r.val.val : ℚ) / Q := by field_simp
          _ < a := hr)
      exact this
    have hrev : (Fin.rev r.val).val + 1 + r.val.val = Q := by
      simp only [Fin.rev]
      have := r.val.isLt
      omega
    have hrev' : ((Fin.rev r.val).val : ℚ) + 1 < a * Q := by
      have hh : ((Fin.rev r.val).val : ℚ) + 1 + r.val.val = Q := by exact_mod_cast hrev
      linarith
    exact Nat.lt_of_succ_le (Nat.le_floor (by exact_mod_cast hrev'.le))
  let e : ↥T → Fin ⌊a * Q⌋₊ := fun r => ⟨(Fin.rev r.val).val, hbound r⟩
  have he : Function.Injective e := by
    intro r s h
    apply Subtype.ext
    apply Fin.rev_injective
    apply Fin.ext
    exact congrArg (fun x : Fin ⌊a * Q⌋₊ => x.val) h
  have hc : T.card ≤ ⌊a * Q⌋₊ := by
    simpa using Fintype.card_le_of_injective e he
  rw [probability_eq_card, Fintype.card_fin]
  change (T.card : ℚ) / Q ≤ a
  apply (div_le_iff₀ hQ').mpr
  exact (show (T.card : ℚ) ≤ ⌊a * Q⌋₊ by exact_mod_cast hc).trans
    (Nat.floor_le (mul_nonneg ha hQ'.le))

/-- Minimum reflected clock over a finite ancestor set; an empty set has
minimum one. This convention also covers a vertex adjacent only to walls. -/
def minClock {ι : Type*} {Q : ℕ} (C : Finset ι) (r : ι → Fin Q) : ℚ :=
  C.fold min 1 (fun v => 1 - gridClock (r v))

section ClockMinimum
variable {ι : Type*} [DecidableEq ι] {Q : ℕ}

theorem minClock_ge (C : Finset ι) (r : ι → Fin Q) (a : ℚ) (ha : a ≤ 1)
    (h : ∀ v ∈ C, a ≤ 1 - gridClock (r v)) : a ≤ minClock C r := by
  induction C using Finset.induction_on with
  | empty => simpa [minClock] using ha
  | @insert v C hv ih =>
    simp only [minClock, Finset.fold_insert_idem] at *
    exact le_min (h v (Finset.mem_insert_self _ _))
      (ih (fun x hx => h x (Finset.mem_insert_of_mem hx)))

theorem minClock_nonneg (C : Finset ι) (r : ι → Fin Q) : 0 ≤ minClock C r :=
  minClock_ge C r 0 zero_le_one (fun v _ => sub_nonneg.mpr (gridClock_mem (r v)).2.le)

theorem minClock_le_one (C : Finset ι) (r : ι → Fin Q) : minClock C r ≤ 1 := by
  induction C using Finset.induction_on with
  | empty => simp [minClock]
  | @insert v C hv ih =>
    simpa only [minClock, Finset.fold_insert_idem] using (min_le_right _ _).trans ih

theorem minClock_le_member (C : Finset ι) (r : ι → Fin Q) {v : ι} (hv : v ∈ C) :
    minClock C r ≤ 1 - gridClock (r v) := by
  induction C using Finset.induction_on with
  | empty => simp at hv
  | @insert x C hx ih =>
    simp only [minClock, Finset.fold_insert_idem]
    rcases Finset.mem_insert.mp hv with h | h
    · subst x; exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih h)

end ClockMinimum

section FiniteClocks
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : ℕ} [NeZero Q]

/-- A union bound over the actual product-clock space. -/
theorem bad_clock_probability (C : Finset ι) (a : ℚ) (ha : 0 ≤ a) :
    probability (fun r : ι → Fin Q => ∃ v ∈ C, 1 - gridClock (r v) < a) ≤ C.card * a := by
  apply (probability_exists_le_sum C _).trans
  calc
    (∑ v ∈ C, probability (fun r : ι → Fin Q => 1 - gridClock (r v) < a))
      = ∑ _v ∈ C, probability (fun r : Fin Q => 1 - gridClock r < a) := by
        apply Finset.sum_congr rfl
        intro v _
        exact mean_pi_apply v (indicator (fun r : Fin Q => 1 - gridClock r < a))
    _ ≤ ∑ _v ∈ C, a := Finset.sum_le_sum (fun _ _ => clock_small_probability (NeZero.pos Q) a ha)
    _ = C.card * a := by simp

/-- The full quantitative high-moment estimate. Both the exceptional-clock
probability and the good-clock contraction are proved from the finite samples. -/
theorem minClock_moment (C : Finset ι) (a : ℚ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (H s : ℕ) :
    mean (fun r : ι → Fin Q => (1 - minClock C r ^ H) ^ s) ≤
      C.card * a + (1 + s * a ^ H)⁻¹ := by
  let P : (ι → Fin Q) → Prop := fun r => ∃ v ∈ C, 1 - gridClock (r v) < a
  have hpow0 : 0 ≤ (1 - a ^ H) ^ s :=
    pow_nonneg (sub_nonneg.mpr (pow_le_one₀ ha0 ha1)) _
  have hfirst := mean_le_bad_probability_add P hpow0
    (f := fun r : ι → Fin Q => (1 - minClock C r ^ H) ^ s)
    (fun r => pow_le_one₀
      (sub_nonneg.mpr (pow_le_one₀ (minClock_nonneg C r) (minClock_le_one C r)))
      (by have := pow_nonneg (minClock_nonneg C r) H; linarith))
    (fun r hgood => by
      have hmin : a ≤ minClock C r := minClock_ge C r a ha1 (fun v hv => by
        exact le_of_not_gt (fun hh => hgood ⟨v, hv, hh⟩))
      have hbase : 1 - minClock C r ^ H ≤ 1 - a ^ H :=
        sub_le_sub_left (pow_le_pow_left₀ ha0 hmin _) _
      exact pow_le_pow_left₀
        (sub_nonneg.mpr (pow_le_one₀ (minClock_nonneg C r) (minClock_le_one C r))) hbase s)
  exact hfirst.trans (add_le_add (bad_clock_probability C a ha0)
    (one_sub_pow_le_inv_one_add_mul (pow_nonneg ha0 _) (pow_le_one₀ ha0 ha1) s))

/-- The manuscript's integer parameter inequalities force a contraction
strictly stronger than one half. -/
theorem minClock_moment_contraction (C : Finset ι) (M H s : ℕ) (hM : 0 < M)
    (hC : C.card ≤ M) (a : ℚ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hsmall : (M : ℚ) ^ 2 * a ≤ 1 / 8)
    (hlarge : 8 * (M : ℚ) ≤ s * a ^ H) :
    (M : ℚ) * mean (fun r : ι → Fin Q => (1 - minClock C r ^ H) ^ s) ≤ 1 / 2 := by
  have hM0 : (0 : ℚ) < M := by exact_mod_cast hM
  have hcard : (C.card : ℚ) ≤ M := by exact_mod_cast hC
  have hmean := minClock_moment (Q := Q) C a ha0 ha1 H s
  have hden : 0 < 1 + (s : ℚ) * a ^ H := by positivity
  have hfrac : (M : ℚ) * (1 + s * a ^ H)⁻¹ ≤ 1 / 8 := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hca : (M : ℚ) * C.card * a ≤ (M : ℚ) ^ 2 * a := by
    have hh := mul_le_mul_of_nonneg_left hcard (mul_nonneg hM0.le ha0)
    nlinarith
  nlinarith

end FiniteClocks
end SortingAdversary.Optimal.ClockContraction
