import SortingAdversary.Optimal.LocalMoments

/-!
# Iterated explicit finite coupling

Each sweep receives a new Cartesian factor of common clocks. Iteration gives
geometric decay of the actual shifted discrepancy moment, and then a tail
probability bound. The schedule premises are finite graph inclusions between
successively smaller interiors, as used for truncated balls in the manuscript.
-/

namespace SortingAdversary.Optimal.CouplingHistory

open WeakMaps LocalCoupling ClockContraction FiniteProbability SystematicCoupling LocalMoments

/-- The initial samples and one independent clock vector for each sweep. -/
def History (Ω : Type*) (n Q : ℕ) : ℕ → Type _
  | 0 => Ω
  | t + 1 => History Ω n Q t × (Fin n → Fin Q)

instance historyFintype {Ω : Type*} [Fintype Ω] {n Q : ℕ} (t : ℕ) : Fintype (History Ω n Q t) := by
  induction t with
  | zero => exact inferInstanceAs (Fintype Ω)
  | succ t ih =>
    letI := ih
    exact inferInstanceAs (Fintype (History Ω n Q t × (Fin n → Fin Q)))

instance historyNonempty {Ω : Type*} [Nonempty Ω] {n Q : ℕ} [NeZero Q] (t : ℕ) :
    Nonempty (History Ω n Q t) := by
  induction t with
  | zero => exact inferInstanceAs (Nonempty Ω)
  | succ t ih =>
    let := ih
    exact inferInstanceAs (Nonempty (History Ω n Q t × (Fin n → Fin Q)))

variable {n K Q : ℕ} {Ω : Type*}

/-- Apply the actual systematic sweep at each stage of a sample history. -/
def trajectory (S : WeakSystem (Fin n) (K + 1)) (f : Ω → State S) :
    (t : ℕ) → History Ω n Q t → State S
  | 0, ω => f ω
  | t + 1, p => sweep S p.2 (trajectory S f t p.1)

/-- Finite graph witnesses for every interior mark at every step. -/
structure Schedule (S T : WeakSystem (Fin n) (K + 1)) (H M : ℕ) where
  interior : ℕ → Finset (Fin n)
  region : ∀ j v, v ∈ interior (j + 1) → Region S T v H M
  dependencies_inside : ∀ j v hv,
    (region j v hv).dependencies ⊆ interior j

/-- Every two finite-palette coordinates differ by at most the palette span. -/
theorem discrepancy_le_palette (S T : WeakSystem (Fin n) (K + 1))
    (f : State S) (g : State T) (v : Fin n) : discrepancy f g v ≤ K := by
  unfold discrepancy
  have hf : ((f.val v).val : ℚ) ≤ K := by exact_mod_cast (Nat.le_of_lt_succ (f.val v).isLt)
  have hg : ((g.val v).val : ℚ) ≤ K := by exact_mod_cast (Nat.le_of_lt_succ (g.val v).isLt)
  have hf0 : (0 : ℚ) ≤ (f.val v).val := Nat.cast_nonneg _
  have hg0 : (0 : ℚ) ≤ (g.val v).val := Nat.cast_nonneg _
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Inclusive width of the original unary interval, in rational arithmetic. -/
def windowWidth (S : WeakSystem (Fin n) (K + 1)) (v : Fin n) : ℚ :=
  ((S.upper v).val : ℚ) - (S.lower v).val + 1

/-- Common retained walls bound the discrepancy by their span, irrespective of
where that interval sits in the global palette. -/
theorem discrepancy_le_common_span (S T : WeakSystem (Fin n) (K + 1))
    (f : State S) (g : State T) (v : Fin n)
    (hl : S.lower v = T.lower v) (hu : S.upper v = T.upper v) :
    discrepancy f g v ≤ ((S.upper v).val : ℚ) - (S.lower v).val := by
  have hflo : ((S.lower v).val : ℚ) ≤ (f.val v).val := by exact_mod_cast (f.property.1 v).1
  have hfhi : ((f.val v).val : ℚ) ≤ (S.upper v).val := by exact_mod_cast (f.property.1 v).2
  have hglo : ((S.lower v).val : ℚ) ≤ (g.val v).val := by
    rw [hl]; exact_mod_cast (g.property.1 v).1
  have hghi : ((g.val v).val : ℚ) ≤ (S.upper v).val := by
    rw [hu]; exact_mod_cast (g.property.1 v).2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem discrepancy_le_common_width (S T : WeakSystem (Fin n) (K + 1))
    (f : State S) (g : State T) (v : Fin n)
    (hl : S.lower v = T.lower v) (hu : S.upper v = T.upper v) :
    discrepancy f g v ≤ windowWidth S v := by
  have h := discrepancy_le_common_span S T f g v hl hu
  unfold windowWidth
  linarith

theorem windowWidth_pos (S : WeakSystem (Fin n) (K + 1)) (f : State S) (v : Fin n) :
    0 < windowWidth S v := by
  have h : ((S.lower v).val : ℚ) ≤ (S.upper v).val := by
    exact_mod_cast (f.property.1 v).1.trans (f.property.1 v).2
  unfold windowWidth
  linarith

section Moments
variable [Fintype Ω] [Nonempty Ω] [NeZero Q]

/-- Geometric moment decay from a bound on actual initial discrepancies only
in the largest interior. This permits a different width bound for each marked
component, independently of palette offsets and unrelated components. -/
theorem trajectory_moment_of_initial_bound (S T : WeakSystem (Fin n) (K + 1))
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (f : Ω → State S) (g : Ω → State T) (H M s : ℕ) (hs : 0 < s) (hM : 0 < M)
    (schedule : Schedule S T H M) (a : ℚ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hsmall : (M : ℚ) ^ 2 * a ≤ 1 / 8) (hlarge : 8 * (M : ℚ) ≤ s * a ^ H)
    (B : ℚ) (hB : 0 ≤ B)
    (hinit : ∀ v ∈ schedule.interior 0, ∀ ω, discrepancy (f ω) (g ω) v ≤ B)
    (t : ℕ) (v : Fin n) (hv : v ∈ schedule.interior t) :
    mean (fun ω : History Ω n Q t =>
      (max (discrepancy (trajectory S f t ω) (trajectory T g t ω) v - (H : ℚ) * t) 0) ^ s) ≤
      B ^ s / 2 ^ t := by
  induction t generalizing v with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, sub_zero, pow_zero, div_one]
    simp only [trajectory, max_eq_left (discrepancy_nonneg _ _ _)]
    exact (mean_mono (fun ω : Ω =>
      pow_le_pow_left₀ (discrepancy_nonneg (f ω) (g ω) v)
        (hinit v hv ω) s)).trans_eq (mean_const _)
  | succ t ih =>
    have h := local_sweep_moment (Q := Q) S T horder
      (trajectory (Q := Q) S f t) (trajectory (Q := Q) T g t) v H M t s hs hM
      (schedule.region t v hv) a (B ^ s / 2 ^ t) ha0 ha1 (by positivity) hsmall hlarge
      (fun x hx => ih x (schedule.dependencies_inside t v hv hx))
    have heq : B ^ s / 2 ^ t / 2 = B ^ s / 2 ^ (t + 1) := by
      rw [div_div, pow_succ]
    calc
      _ = mean (fun p : History Ω n Q t × (Fin n → Fin Q) =>
          (max (discrepancy (sweep S p.2 (trajectory S f t p.1))
            (sweep T p.2 (trajectory T g t p.1)) v - (H : ℚ) * (t + 1)) 0) ^ s) := by
        apply mean_congr_fintype
        intro ω
        simp only [trajectory, Nat.cast_succ]
      _ ≤ B ^ s / 2 ^ (t + 1) := by simpa only [heq] using h


/-- Component-sensitive tail estimate from the proved initial-bound moment
theorem and finite Markov inequality. -/
theorem trajectory_tail_of_initial_bound (S T : WeakSystem (Fin n) (K + 1))
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (f : Ω → State S) (g : Ω → State T) (H M s : ℕ) (hs : 0 < s) (hM : 0 < M)
    (schedule : Schedule S T H M) (a : ℚ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hsmall : (M : ℚ) ^ 2 * a ≤ 1 / 8) (hlarge : 8 * (M : ℚ) ≤ s * a ^ H)
    (B : ℚ) (hB : 0 ≤ B)
    (hinit : ∀ v ∈ schedule.interior 0, ∀ ω, discrepancy (f ω) (g ω) v ≤ B)
    (t : ℕ) (v : Fin n) (hv : v ∈ schedule.interior t) (e : ℚ) (he : 0 < e) :
    probability (fun ω : History Ω n Q t =>
      (H : ℚ) * t + e < discrepancy (trajectory S f t ω) (trajectory T g t ω) v) ≤
      (B / e) ^ s / 2 ^ t := by
  let D : History Ω n Q t → ℚ := fun ω =>
    discrepancy (trajectory S f t ω) (trajectory T g t ω) v
  have hepow : 0 < e ^ s := pow_pos he _
  have hevent := probability_mono
    (P := fun ω => (H : ℚ) * t + e < D ω)
    (Q := fun ω => e ^ s < (max (D ω - (H : ℚ) * t) 0) ^ s)
    (fun ω h => by
      have hgap : e < max (D ω - (H : ℚ) * t) 0 := by
        apply lt_of_lt_of_le _ (le_max_left _ _)
        linarith
      exact pow_lt_pow_left₀ hgap he.le hs.ne')
  have hmarkov := probability_le_mean_div
    (fun ω => pow_nonneg (le_max_right (D ω - (H : ℚ) * t) 0) s) hepow
  have hm := trajectory_moment_of_initial_bound (Q := Q) S T horder f g H M s hs hM schedule a
    ha0 ha1 hsmall hlarge B hB hinit t v hv
  change mean (fun ω => (max (D ω - (H : ℚ) * t) 0) ^ s) ≤ _ at hm
  calc
    _ ≤ probability (fun ω => e ^ s < (max (D ω - (H : ℚ) * t) 0) ^ s) := hevent
    _ ≤ mean (fun ω => (max (D ω - (H : ℚ) * t) 0) ^ s) / e ^ s := hmarkov
    _ ≤ (B ^ s / 2 ^ t) / e ^ s := div_le_div_of_nonneg_right hm hepow.le
    _ = (B / e) ^ s / 2 ^ t := by rw [div_pow]; ring

/-- Geometric moment decay for constructed histories. The initial bound is
proved from the finite palette itself, rather than assumed for initial samples. -/
theorem trajectory_moment (S T : WeakSystem (Fin n) (K + 1))
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (f : Ω → State S) (g : Ω → State T) (H M s : ℕ) (hs : 0 < s) (hM : 0 < M)
    (schedule : Schedule S T H M) (a : ℚ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hsmall : (M : ℚ) ^ 2 * a ≤ 1 / 8) (hlarge : 8 * (M : ℚ) ≤ s * a ^ H)
    (t : ℕ) (v : Fin n) (hv : v ∈ schedule.interior t) :
    mean (fun ω : History Ω n Q t =>
      (max (discrepancy (trajectory S f t ω) (trajectory T g t ω) v - (H : ℚ) * t) 0) ^ s) ≤
      (K : ℚ) ^ s / 2 ^ t := by
  exact trajectory_moment_of_initial_bound S T horder f g H M s hs hM schedule a
    ha0 ha1 hsmall hlarge K (Nat.cast_nonneg _) (fun v _ ω =>
      discrepancy_le_palette S T (f ω) (g ω) v) t v hv

/-- Tail estimate from the proved moment bound and finite Markov inequality. -/
theorem trajectory_tail (S T : WeakSystem (Fin n) (K + 1))
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (f : Ω → State S) (g : Ω → State T) (H M s : ℕ) (hs : 0 < s) (hM : 0 < M)
    (schedule : Schedule S T H M) (a : ℚ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hsmall : (M : ℚ) ^ 2 * a ≤ 1 / 8) (hlarge : 8 * (M : ℚ) ≤ s * a ^ H)
    (t : ℕ) (v : Fin n) (hv : v ∈ schedule.interior t) (e : ℚ) (he : 0 < e) :
    probability (fun ω : History Ω n Q t =>
      (H : ℚ) * t + e < discrepancy (trajectory S f t ω) (trajectory T g t ω) v) ≤
      ((K : ℚ) / e) ^ s / 2 ^ t := by
  exact trajectory_tail_of_initial_bound S T horder f g H M s hs hM schedule a
    ha0 ha1 hsmall hlarge K (Nat.cast_nonneg _) (fun v _ ω =>
      discrepancy_le_palette S T (f ω) (g ω) v) t v hv e he

end Moments
end SortingAdversary.Optimal.CouplingHistory
