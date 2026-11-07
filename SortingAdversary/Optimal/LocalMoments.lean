import SortingAdversary.Optimal.SystematicCoupling

/-!
# Actual local moment contraction

The refresh process and its common clocks are explicit finite functions.
Independence below is obtained by taking their Cartesian product with the
old-state sample space. No coupling or mixing conclusion is a hypothesis.
-/

namespace SortingAdversary.Optimal.LocalMoments

open WeakMaps LocalCoupling ClockContraction FiniteProbability SystematicCoupling
open scoped BigOperators

section Maximum
variable {ι : Type*}

/-- A nonnegative maximum, including the empty dependency set. -/
def maxOn (N : Finset ι) (f : ι → ℚ) : ℚ := N.fold max 0 f

theorem maxOn_nonneg (N : Finset ι) (f : ι → ℚ) : 0 ≤ maxOn N f :=
  (Finset.le_fold_max 0).mpr (Or.inl le_rfl)

theorem le_maxOn (N : Finset ι) (f : ι → ℚ) {x : ι} (hx : x ∈ N) : f x ≤ maxOn N f :=
  (Finset.le_fold_max (f x)).mpr (Or.inr ⟨x, hx, le_rfl⟩)

theorem maxOn_le (N : Finset ι) (f : ι → ℚ) {B : ℚ} (hB : 0 ≤ B)
    (hf : ∀ x ∈ N, f x ≤ B) : maxOn N f ≤ B :=
  (Finset.fold_max_le B).mpr ⟨hB, hf⟩

variable [DecidableEq ι]

theorem maxOn_attained (N : Finset ι) (f : ι → ℚ) :
    maxOn N f = 0 ∨ ∃ x ∈ N, maxOn N f = f x := by
  induction N using Finset.induction_on with
  | empty => simp [maxOn]
  | @insert x N hx ih =>
    simp only [maxOn, Finset.fold_insert_idem]
    rcases max_choice (f x) (maxOn N f) with h | h
    · exact Or.inr ⟨x, Finset.mem_insert_self _ _, h⟩
    · rcases ih with ih | ⟨y, hy, ih⟩
      · exact Or.inl (h.trans ih)
      · exact Or.inr ⟨y, Finset.mem_insert_of_mem hy, h.trans ih⟩

/-- Taking a positive power of a shifted maximum costs at most the sum of
coordinate powers. This removes any need to follow an optimizing path. -/
theorem shifted_max_power_le_sum (N : Finset ι) (f : ι → ℚ) (c : ℚ) (hc : 0 ≤ c)
    (s : ℕ) (hs : 0 < s) :
    (max (maxOn N f - c) 0) ^ s ≤ ∑ x ∈ N, (max (f x - c) 0) ^ s := by
  rcases maxOn_attained N f with h | ⟨x, hx, h⟩
  · rw [h, zero_sub, max_eq_right (neg_nonpos.mpr hc), zero_pow hs.ne']
    exact Finset.sum_nonneg (fun x _ => pow_nonneg (le_max_right _ _) _)
  · rw [h]
    exact Finset.single_le_sum (f := fun y => (max (f y - c) 0) ^ s)
      (fun y _ => pow_nonneg (le_max_right _ _) _) hx

end Maximum

variable {n K Q : ℕ}

/-- Pointwise high-moment contraction for one actual common-clock sweep. -/
theorem local_sweep_power (S T : WeakSystem (Fin n) (K + 1))
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (r : Fin n → Fin Q) (f : State S) (g : State T) (v : Fin n) (H M j s : ℕ)
    (hs : 0 < s) (region : Region S T v H M) :
    (max (discrepancy (sweep S r f) (sweep T r g) v - (H : ℚ) * (j + 1)) 0) ^ s ≤
      (∑ x ∈ region.dependencies, (max (discrepancy f g x - (H : ℚ) * j) 0) ^ s) *
        (1 - minClock region.ancestors r ^ H) ^ s := by
  let B := maxOn region.dependencies (discrepancy f g)
  let c := 1 - minClock region.ancestors r ^ H
  have hc0 : 0 ≤ c := sub_nonneg.mpr (pow_le_one₀
    (minClock_nonneg _ _) (minClock_le_one _ _))
  have hc1 : c ≤ 1 := by have := pow_nonneg (minClock_nonneg region.ancestors r) H; linarith
  have hstep := local_sweep_contraction S T horder r f g v H M region B
    (maxOn_nonneg _ _) (fun x hx => le_maxOn _ _ hx)
  have hshift := shifted_discrepancy hc0 hc1 (Nat.cast_nonneg H) (Nat.cast_nonneg j) hstep
  have hp := pow_le_pow_left₀ (le_max_right _ _) hshift s
  rw [mul_pow] at hp
  have hsum := shifted_max_power_le_sum region.dependencies (discrepancy f g)
    ((H : ℚ) * j) (by positivity) s hs
  have hmul := mul_le_mul_of_nonneg_left hsum (pow_nonneg hc0 s)
  change _ ≤ _ * c ^ s
  nlinarith

section Moment
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] [NeZero Q]

/-- A genuine one-step expectation bound. Old states can have any dependence;
fresh clocks are independent by construction of the product sample space. -/
theorem local_sweep_moment (S T : WeakSystem (Fin n) (K + 1))
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (f : Ω → State S) (g : Ω → State T) (v : Fin n) (H M j s : ℕ)
    (hs : 0 < s) (hM : 0 < M) (region : Region S T v H M)
    (a W : ℚ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hW : 0 ≤ W)
    (hsmall : (M : ℚ) ^ 2 * a ≤ 1 / 8) (hlarge : 8 * (M : ℚ) ≤ s * a ^ H)
    (hmoment : ∀ x ∈ region.dependencies,
      mean (fun ω => (max (discrepancy (f ω) (g ω) x - (H : ℚ) * j) 0) ^ s) ≤ W) :
    mean (fun p : Ω × (Fin n → Fin Q) =>
      (max (discrepancy (sweep S p.2 (f p.1)) (sweep T p.2 (g p.1)) v -
        (H : ℚ) * (j + 1)) 0) ^ s) ≤ W / 2 := by
  let F : Ω → ℚ := fun ω =>
    ∑ x ∈ region.dependencies, (max (discrepancy (f ω) (g ω) x - (H : ℚ) * j) 0) ^ s
  let G : (Fin n → Fin Q) → ℚ := fun r => (1 - minClock region.ancestors r ^ H) ^ s
  have hF : mean F ≤ (M : ℚ) * W := by
    unfold F
    rw [mean_sum]
    calc
      _ ≤ ∑ _x ∈ region.dependencies, W := Finset.sum_le_sum (fun x hx => hmoment x hx)
      _ = (region.dependencies.card : ℚ) * W := by simp
      _ ≤ (M : ℚ) * W := mul_le_mul_of_nonneg_right (by exact_mod_cast region.dependencies_card) hW
  have hG0 : 0 ≤ mean G := mean_nonneg (fun r => pow_nonneg (sub_nonneg.mpr
    (pow_le_one₀ (minClock_nonneg _ _) (minClock_le_one _ _))) _)
  have hG := minClock_moment_contraction (Q := Q) region.ancestors M H s hM
    region.ancestors_card a ha0 ha1 hsmall hlarge
  have hpoint := mean_mono (fun p : Ω × (Fin n → Fin Q) =>
    local_sweep_power S T horder p.2 (f p.1) (g p.1) v H M j s hs region)
  change _ ≤ mean (fun p : Ω × (Fin n → Fin Q) => F p.1 * G p.2) at hpoint
  rw [mean_independent_mul] at hpoint
  have hmul := mul_le_mul_of_nonneg_right hF hG0
  have hcontract := mul_le_mul_of_nonneg_left hG hW
  change (M : ℚ) * mean G ≤ 1 / 2 at hG
  nlinarith

end Moment
end SortingAdversary.Optimal.LocalMoments
