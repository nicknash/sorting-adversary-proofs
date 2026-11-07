import SortingAdversary.Optimal.WeakMaps
import SortingAdversary.Optimal.Terminal
import SortingAdversary.Optimal.Accounting

/-!
# Initial and terminal counts of actual weak-map systems

The root starts with all colour assignments, giving `n^n` maps. At termination,
the free labels in each pool have a known order and every other label is pinned.
This file connects those concrete finite systems to the logarithmic accounting
bounds, including the product over pools and pools with no free labels.

All logarithms are natural logarithms, as in `Optimal.Accounting`.
-/

namespace SortingAdversary.Optimal.Endpoints

open scoped BigOperators
open WeakMaps WeakMaps.WeakSystem

/-- An unconstrained nonempty palette, written with size `K+1` to avoid an
arbitrary inhabitant or a partial choice of its two endpoints. -/
def initialSystem (α : Type*) (K : ℕ) : WeakSystem α (K + 1) where
  edge := fun _ _ => false
  lower := fun _ => 0
  upper := fun _ => Fin.last K

@[simp] theorem valid_initialSystem {α : Type*} (K : ℕ) (f : ColorMap α (K + 1)) :
    (initialSystem α K).Valid f := by
  constructor
  · intro x
    exact ⟨Fin.zero_le _, Fin.le_last _⟩
  · intro x y h
    simp [initialSystem] at h

theorem maps_initialSystem {α : Type*} [Fintype α] [DecidableEq α] (K : ℕ) :
    (initialSystem α K).maps = Finset.univ := by
  ext f
  simp

theorem count_initialSystem {α : Type*} [Fintype α] [DecidableEq α] (K : ℕ) :
    (initialSystem α K).count = (K + 1) ^ Fintype.card α := by
  simp [count, maps_initialSystem]

/-- The concrete initial root count is `n^n`, with `n=N+1`. -/
theorem root_initial_count (N : ℕ) :
    (initialSystem (Fin (N + 1)) N).count = (N + 1) ^ (N + 1) := by
  simp [count_initialSystem]

theorem root_initial_log_count (N : ℕ) :
    Real.log ((initialSystem (Fin (N + 1)) N).count : ℝ) =
      ((N + 1 : ℕ) : ℝ) * Real.log ((N + 1 : ℕ) : ℝ) := by
  rw [root_initial_count, Nat.cast_pow, Real.log_pow]

/-- A terminal pool's *actual* count, rather than an assumed terminal number,
has the stars-and-bars logarithmic upper bound. The free-label enumeration need
not be injective: redundant enumeration can only weaken this upper bound. -/
theorem terminal_log_count {α : Type*} [Fintype α] [DecidableEq α] {K r : ℕ}
    (S : WeakSystem α K) (enumerate : Fin r → α) (pin : α → Fin K)
    (hK : 1 ≤ K) (hcount : 0 < S.count)
    (hordered : ∀ f, S.Valid f → Monotone (fun i => f (enumerate i)))
    (hpins : ∀ f, S.Valid f → ∀ x, x ∉ Set.range enumerate → f x = pin x) :
    Real.log (S.count : ℝ) ≤
      (r : ℝ) * (1 + Real.log (1 + (K : ℝ) / r)) := by
  have hcard := Terminal.card_le_choose_of_fixed_pins S.maps enumerate pin
    (fun f hf => hordered f ((mem_maps S f).mp hf))
    (fun f hf => hpins f ((mem_maps S f).mp hf))
  have hpositive : (0 : ℝ) < S.count := by exact_mod_cast hcount
  have hlog : Real.log (S.count : ℝ) ≤ Real.log ((K + r - 1).choose r : ℝ) := by
    apply Real.log_le_log hpositive
    exact_mod_cast hcard
  exact hlog.trans (Accounting.log_weak_sequence_count_le K r hK)

/-- Combining the concrete terminal counts over all pools costs only the
total number of free labels and total palette size. Empty free-label lists are
handled without a positive-weight assumption on every pool. -/
theorem terminal_product_log_count
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → Type*) [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    (K r : ι → ℕ) (S : ∀ v, WeakSystem (α v) (K v))
    (enumerate : ∀ v, Fin (r v) → α v) (pin : ∀ v, α v → Fin (K v))
    (hK : ∀ v, 1 ≤ K v) (hcount : ∀ v, 0 < (S v).count)
    (hordered : ∀ v f, (S v).Valid f → Monotone (fun i => f (enumerate v i)))
    (hpins : ∀ v f, (S v).Valid f →
      ∀ x, x ∉ Set.range (enumerate v) → f x = pin v x) :
    Real.log (∏ v, ((S v).count : ℝ)) ≤
      (∑ v, (r v : ℝ)) *
        (1 + Real.log (1 + (∑ v, (K v : ℝ)) / (∑ v, (r v : ℝ)))) := by
  classical
  let positive : Finset ι := Finset.univ.filter (fun v => 0 < r v)
  have hfree (v : ι) (hv : v ∈ positive) : (0 : ℝ) < r v := by
    exact_mod_cast (Finset.mem_filter.mp hv).2
  have hpal (v : ι) (_hv : v ∈ positive) : (0 : ℝ) ≤ K v := Nat.cast_nonneg _
  have hr_sum : (∑ v ∈ positive, (r v : ℝ)) = ∑ v, (r v : ℝ) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro v _hv hvnot
    have hrzero : r v = 0 := by
      have hnot : ¬ 0 < r v := by simpa [positive] using hvnot
      omega
    simp [hrzero]
  have hK_sum : (∑ v ∈ positive, (K v : ℝ)) ≤ ∑ v, (K v : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun v _hv _hvn => Nat.cast_nonneg _)
  have hterm_sum :
      (∑ v ∈ positive, (r v : ℝ) * (1 + Real.log (1 + (K v : ℝ) / r v))) =
      ∑ v, (r v : ℝ) * (1 + Real.log (1 + (K v : ℝ) / r v)) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro v _hv hvnot
    have hrzero : r v = 0 := by
      have hnot : ¬ 0 < r v := by simpa [positive] using hvnot
      omega
    simp [hrzero]
  have hmean := Accounting.terminal_entropy_average positive
    (fun v => (r v : ℝ)) (fun v => (K v : ℝ)) hfree hpal
  rw [hr_sum, hterm_sum] at hmean
  have hn : (0 : ℝ) ≤ ∑ v, (r v : ℝ) :=
    Finset.sum_nonneg (fun v _ => Nat.cast_nonneg _)
  have hsmall : (0 : ℝ) ≤ ∑ v ∈ positive, (K v : ℝ) :=
    Finset.sum_nonneg (fun v _ => Nat.cast_nonneg _)
  have harg : 0 < 1 + (∑ v ∈ positive, (K v : ℝ)) / (∑ v, (r v : ℝ)) := by
    have := div_nonneg hsmall hn
    linarith
  have hlog := Real.log_le_log harg
    (add_le_add le_rfl (div_le_div_of_nonneg_right hK_sum hn))
  calc
    Real.log (∏ v, ((S v).count : ℝ)) = ∑ v, Real.log ((S v).count : ℝ) := by
      apply Real.log_prod
      intro v _hv
      exact (show (0 : ℝ) < (S v).count by exact_mod_cast hcount v).ne'
    _ ≤ ∑ v, (r v : ℝ) * (1 + Real.log (1 + (K v : ℝ) / r v)) :=
      Finset.sum_le_sum (fun v _ =>
        terminal_log_count (S v) (enumerate v) (pin v)
          (hK v) (hcount v) (hordered v) (hpins v))
    _ ≤ _ := hmean.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hlog) hn)

end SortingAdversary.Optimal.Endpoints
