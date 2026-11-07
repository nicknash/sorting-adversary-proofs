import SortingAdversary.Optimal.TruncatedLaw
import SortingAdversary.Optimal.FiniteInsertion
import SortingAdversary.Optimal.MarginalCalibration

/-!
# Actual finite coupling for cumulative probability queries

The existing marginal CDF is identified with the event in the same uniform
finite law used by the coupling. A fixed threshold contributes no coupling
error of its own. The remaining near-threshold term is the proved integer
insertion probability, integrated by the final accuracy theorem.
-/

namespace SortingAdversary.Optimal.CDFCoupling

open WeakMaps LocalChoice FiniteProbability SystematicCoupling CouplingHistory
open LocalError LocalCoupling ClockStationarity TruncatedLaw BallSchedule

variable {n K Q : ℕ}

/-- The existing exclusive CDF is the corresponding event probability. -/
theorem cdf_eq_probability {α : Type*} [Fintype α] [DecidableEq α]
    (S : WeakSystem α (K + 1)) (x : α) (cut : ℕ) :
    MarginalCalibration.cdf S x cut = probability (fun f : Feasible S => (f.val x).val < cut) := by
  rw [MarginalCalibration.cdf_eq_card]
  exact (TruncatedLaw.probability_eq_count S (fun f => (f x).val < cut)).symm

/-- Inclusive thresholds are exclusive CDF queries at the following integer. -/
theorem cdf_succ_eq_probability {α : Type*} [Fintype α] [DecidableEq α]
    (S : WeakSystem α (K + 1)) (x : α) (c : ℕ) :
    MarginalCalibration.cdf S x (c + 1) =
      probability (fun f : Feasible S => ((f.val x).val : ℚ) ≤ c) := by
  rw [cdf_eq_probability]
  simp only [Nat.lt_succ_iff, Nat.cast_le]

theorem cdf_congr {α : Type*} [Fintype α] [DecidableEq α]
    {S T : WeakSystem α (K + 1)} (h : ∀ f, S.Valid f ↔ T.Valid f) (x : α) (cut : ℕ) :
    MarginalCalibration.cdf S x cut = MarginalCalibration.cdf T x cut := by
  rw [cdf_eq_probability, cdf_eq_probability]
  exact probability_congr_valid h (fun f => (f x).val < cut)

/-- The common-carrier truncated CDF equals the actual small induced CDF. -/
theorem cdf_truncate (S : WeakSystem (Fin n) (K + 1)) (B : Finset (Fin n))
    (hS : 0 < S.count) (x : ↥B) (cut : ℕ) :
    MarginalCalibration.cdf (truncate S B) x.val cut = MarginalCalibration.cdf (induced S B) x cut := by
  rw [cdf_eq_probability, cdf_eq_probability]
  exact probability_truncate S B hS (fun f => (f x).val < cut)

/-- A fixed threshold has no discrepancy term of its own. -/
theorem threshold_probability_error {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X X' : Ω → ℚ) (c a : ℚ) :
    |probability (fun ω => X ω ≤ c) - probability (fun ω => X' ω ≤ c)| ≤
      probability (fun ω => a < |X ω - X' ω|) + probability (fun ω => |X ω - c| ≤ a) := by
  have h := comparison_probability_error X (fun _ => c) X' (fun _ => c) a 0
  have hz : probability (fun _ : Ω => 0 < |c - c|) = 0 := by
    change mean (fun _ : Ω => if 0 < |c - c| then 1 else 0) = 0
    simp only [sub_self, abs_zero, lt_self_iff_false, if_false, mean_const]
  rw [hz] at h
  simpa only [add_zero] using h

/-- One marked schedule suffices for a fixed-threshold CDF query. The same
actual independent histories and proved uniform marginals are used. -/
theorem threshold_error_of_width_schedule (S T : WeakSystem (Fin n) (K + 1))
    (hS : 0 < S.count) (hT : 0 < T.count)
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (H M s : ℕ) (hs : 0 < s) (hM : 0 < M) (schedule : Schedule S T H M)
    (a : ℚ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hsmall : (M : ℚ) ^ 2 * a ≤ 1 / 8) (hlarge : 8 * (M : ℚ) ≤ s * a ^ H)
    (B : ℚ) (hB : 0 ≤ B)
    (hl : ∀ v, S.lower v = T.lower v) (hu : ∀ v, S.upper v = T.upper v)
    (hwidth : ∀ v ∈ schedule.interior 0, windowWidth S v ≤ B)
    (t : ℕ) (x : Fin n) (hx : x ∈ schedule.interior t)
    (e : ℚ) (he : 0 < e) (c : ℕ) :
    |probability (fun f : State S => ((f.val x).val : ℚ) ≤ c) -
        probability (fun f : State T => ((f.val x).val : ℚ) ≤ c)| ≤
      (B / e) ^ s / 2 ^ t + FiniteInsertion.thresholdNearProbability S x c ((H : ℚ) * t + e) := by
  let Q := (K + 1).factorial
  let : NeZero Q := ⟨Nat.factorial_ne_zero _⟩
  let : Nonempty (State S) := by
    obtain ⟨f, hf⟩ := S.count_pos_iff.mp hS
    exact ⟨⟨f, hf⟩⟩
  let : Nonempty (State T) := by
    obtain ⟨f, hf⟩ := T.count_pos_iff.mp hT
    exact ⟨⟨f, hf⟩⟩
  let Ω := State S × State T
  let f : Ω → State S := Prod.fst
  let g : Ω → State T := Prod.snd
  let F := trajectory (Q := Q) S f t
  let G := trajectory (Q := Q) T g t
  have hF : UniformLaw S F := trajectory_uniform S f (initial_uniform_left S T)
    (fun v z => conditionalWidth_dvd_factorial S v z) t
  have hG : UniformLaw T G := trajectory_uniform T g (initial_uniform_right S T)
    (fun v z => conditionalWidth_dvd_factorial T v z) t
  have hxt := trajectory_tail_of_initial_bound (Q := Q) S T horder f g H M s hs hM schedule a
    ha0 ha1 hsmall hlarge B hB (fun v hv ω =>
      (discrepancy_le_common_width S T (f ω) (g ω) v (hl v) (hu v)).trans (hwidth v hv))
    t x hx e he
  let X : History Ω n Q t → ℚ := fun ω => ((F ω).val x).val
  let X' : History Ω n Q t → ℚ := fun ω => ((G ω).val x).val
  have hcmp := threshold_probability_error X X' c ((H : ℚ) * t + e)
  have hleft : probability (fun ω => X ω ≤ c) = probability (fun z : State S => ((z.val x).val : ℚ) ≤ c) :=
    probability_uniform S F hF (fun z => ((z x).val : ℚ) ≤ c)
  have hright : probability (fun ω => X' ω ≤ c) = probability (fun z : State T => ((z.val x).val : ℚ) ≤ c) :=
    probability_uniform T G hG (fun z => ((z x).val : ℚ) ≤ c)
  have hnear : probability (fun ω => |X ω - c| ≤ (H : ℚ) * t + e) =
      FiniteInsertion.thresholdNearProbability S x c ((H : ℚ) * t + e) :=
    probability_uniform S F hF (fun z => |((z x).val : ℚ) - c| ≤ (H : ℚ) * t + e)
  change probability (fun ω => (H : ℚ) * t + e < |X ω - X' ω|) ≤ _ at hxt
  have hLeq :
      |probability (fun z : State S => ((z.val x).val : ℚ) ≤ c) -
        probability (fun z : State T => ((z.val x).val : ℚ) ≤ c)| =
      |probability (fun ω => X ω ≤ c) - probability (fun ω => X' ω ≤ c)| :=
    congrArg abs (congrArg₂ (fun a b : ℚ => a - b) hleft.symm hright.symm)
  have hReq :
      probability (fun ω => (H : ℚ) * t + e < |X ω - X' ω|) +
        probability (fun ω => |X ω - c| ≤ (H : ℚ) * t + e) =
      probability (fun ω => (H : ℚ) * t + e < |X ω - X' ω|) +
        FiniteInsertion.thresholdNearProbability S x c ((H : ℚ) * t + e) :=
    congrArg (fun q : ℚ => probability (fun ω => (H : ℚ) * t + e < |X ω - X' ω|) + q) hnear
  have hfinal := (hcmp.trans_eq hReq).trans
    (add_le_add hxt (le_refl (FiniteInsertion.thresholdNearProbability S x c ((H : ℚ) * t + e))))
  exact hLeq.trans_le hfinal

theorem cdf_error_of_width_schedule (S T : WeakSystem (Fin n) (K + 1))
    (hS : 0 < S.count) (hT : 0 < T.count)
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (H M s : ℕ) (hs : 0 < s) (hM : 0 < M) (schedule : Schedule S T H M)
    (a : ℚ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hsmall : (M : ℚ) ^ 2 * a ≤ 1 / 8) (hlarge : 8 * (M : ℚ) ≤ s * a ^ H)
    (B : ℚ) (hB : 0 ≤ B)
    (hl : ∀ v, S.lower v = T.lower v) (hu : ∀ v, S.upper v = T.upper v)
    (hwidth : ∀ v ∈ schedule.interior 0, windowWidth S v ≤ B)
    (t : ℕ) (x : Fin n) (hx : x ∈ schedule.interior t)
    (e : ℚ) (he : 0 < e) (c : ℕ) :
    |MarginalCalibration.cdf S x (c + 1) - MarginalCalibration.cdf T x (c + 1)| ≤
      (B / e) ^ s / 2 ^ t + FiniteInsertion.thresholdNearProbability S x c ((H : ℚ) * t + e) := by
  rw [cdf_succ_eq_probability, cdf_succ_eq_probability]
  exact threshold_error_of_width_schedule S T hS hT horder H M s hs hM schedule a
    ha0 ha1 hsmall hlarge B hB hl hu hwidth t x hx e he c

/-- Fixed-threshold error for the actual radius-`Ht` ball with propagated walls. -/
theorem cdf_error_ball (S : WeakSystem (Fin n) (K + 1)) (hS : 0 < S.count)
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (rank : Fin n → ℕ) (H d : ℕ)
    (hstrict : ∀ x y, GraphBalls.Arc S.edge x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ v, (GraphBalls.neighbors S.edge v).card ≤ d)
    (s : ℕ) (hs : 0 < s) (a : ℚ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hsmall : (((d + 1) ^ (H + 1) : ℕ) : ℚ) ^ 2 * a ≤ 1 / 8)
    (hlarge : 8 * (((d + 1) ^ (H + 1) : ℕ) : ℚ) ≤ s * a ^ H)
    (t : ℕ) (x : Fin n) (R : ℚ) (hR : 0 ≤ R)
    (hwidth : ∀ v, GraphBalls.Connected S.edge x v → windowWidth S v ≤ R * windowWidth S x)
    (e : ℚ) (he : 0 < e) (c : ℕ) :
    |MarginalCalibration.cdf S x (c + 1) -
        MarginalCalibration.cdf (truncate S (GraphBalls.ball S.edge x (H * t))) x (c + 1)| ≤
      (R * windowWidth S x / e) ^ s / 2 ^ t +
        FiniteInsertion.thresholdNearProbability S x c ((H : ℚ) * t + e) := by
  let B := GraphBalls.ball S.edge x (H * t)
  obtain ⟨f, hf⟩ := S.count_pos_iff.mp hS
  exact cdf_error_of_width_schedule S (truncate S B) hS (truncate_count_pos S B hS)
    horder H ((d + 1) ^ (H + 1)) s hs (pow_pos (Nat.succ_pos d) _)
    (BallSchedule.schedule S B rank H d hstrict hheight hdegree x t (Finset.Subset.refl _))
    a ha0 ha1 hsmall hlarge (R * windowWidth S x)
    (mul_nonneg hR (windowWidth_pos S ⟨f, hf⟩ x).le) (fun _ => rfl) (fun _ => rfl)
    (initial_width_bound S x H t R hwidth) t x
    (mark_mem_schedule S B rank H d hstrict hheight hdegree x t (Finset.Subset.refl _)) e he c

end SortingAdversary.Optimal.CDFCoupling
