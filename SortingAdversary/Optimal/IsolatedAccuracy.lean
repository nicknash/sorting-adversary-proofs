import SortingAdversary.Optimal.LocalAccuracy
import SortingAdversary.Optimal.CDFAccuracy
import SortingAdversary.Optimal.IsolatedCoupling

/-!
# Local accuracy with arbitrary-width isolated labels

Only nonisolated marks need the large-width threshold. Isolated marks agree
exactly after one common-clock sweep; both isolated comparison laws and CDFs
are exact. This preserves the manuscript's exemption from unnecessary pins.
-/

namespace SortingAdversary.Optimal.IsolatedAccuracy

open WeakMaps LocalChoice GraphBalls BallSchedule CouplingHistory
open LocalParameters NumericalGeometry SparseClosure TruncatedLaw LocalAccuracy
open IsolatedCoupling CDFCoupling

variable {n K : ℕ}

/-- Comparison probabilities for two isolated labels are exact, with no width
or geometric assumptions on the rest of the system. -/
theorem comparison_exact (S : WeakSystem (Fin n) (K + 1)) (hS : 0 < S.count)
    (H d : ℕ) (R ε : ℚ) (x y : Fin n)
    (hx : Isolated S.edge x) (hy : Isolated S.edge y) :
    localWeakProbability S H d R ε x y = weakProbability S x y := by
  let P := propagateSystem S
  let B := LocalAccuracy.queryBall S H d R ε x y
  let T := truncate P B
  have hP : 0 < P.count := by simpa [P] using hS
  have hT : 0 < T.count := truncate_count_pos P B hP
  have heq : weakProbability P x y = weakProbability T x y := by
    rw [weakProbability_eq_probability, weakProbability_eq_probability]
    exact pair_event_eq P T hP hT x y hx (isolated_truncate P B x hx)
      hy (isolated_truncate P B y hy) rfl rfl rfl rfl (· ≤ ·)
  calc
    _ = weakProbability T x y := localWeakProbability_eq_truncate S hS H d R ε x y
    _ = weakProbability P x y := heq.symm
    _ = _ := weakProbability_congr (propagateSystem_valid S) x y

/-- An isolated CDF is exact for every natural threshold, even for a one-color
or otherwise narrow original interval. -/
theorem cdf_exact (S : WeakSystem (Fin n) (K + 1)) (hS : 0 < S.count)
    (H d : ℕ) (R ε : ℚ) (x : Fin n) (hx : Isolated S.edge x) (cut : ℕ) :
    CDFAccuracy.localCDF S H d R ε x cut = MarginalCalibration.cdf S x cut := by
  let P := propagateSystem S
  let B := CDFAccuracy.queryBall S H d R ε x
  let T := truncate P B
  have hP : 0 < P.count := by simpa [P] using hS
  have hT : 0 < T.count := truncate_count_pos P B hP
  have heq : MarginalCalibration.cdf P x cut = MarginalCalibration.cdf T x cut := by
    rw [cdf_eq_probability, cdf_eq_probability]
    exact pair_event_eq P T hP hT x x hx (isolated_truncate P B x hx)
      hx (isolated_truncate P B x hx) rfl rfl rfl rfl (fun a _ => a.val < cut)
  calc
    _ = MarginalCalibration.cdf T x cut :=
      (cdf_truncate P B hP ⟨x, CDFAccuracy.mark_mem_queryBall S H d R ε x⟩ cut).symm
    _ = MarginalCalibration.cdf P x cut := heq.symm
    _ = _ := cdf_congr (propagateSystem_valid S) x cut

/-- In a mixed query only the nonisolated mark `x` needs the width-ratio and
minimum-width assumptions. Both weak comparison directions have small error. -/
theorem comparison_accuracy_mixed (S : WeakSystem (Fin n) (K + 1)) (hS : 0 < S.count)
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (rank : Fin n → ℕ) (H d : ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d)
    (R ε : ℚ) (hR : 0 ≤ R) (hε : 0 < ε) (x y : Fin n) (hxy : y ≠ x)
    (hwidth : ∀ v, Connected S.edge x v →
      windowWidth (propagateSystem S) v ≤ R * windowWidth (propagateSystem S) x)
    (hmin : (minimumWidth H (influenceSize H d) R ε : ℚ) ≤ windowWidth (propagateSystem S) x)
    (hy : Isolated S.edge y) :
    (|localWeakProbability S H d R ε x y - weakProbability S x y| ≤ ε) ∧
    (|localWeakProbability S H d R ε y x - weakProbability S y x| ≤ ε) := by
  let M := influenceSize H d
  let t := sweepCount H M R ε
  let P := propagateSystem S
  let B := LocalAccuracy.queryBall S H d R ε x y
  let T := truncate P B
  let W := windowWidth P x
  let u := relativeTolerance M ε
  let e := u * W / 2
  let z := (H : ℚ) * t + e
  have hP : 0 < P.count := by simpa [P] using hS
  have hT : 0 < T.count := truncate_count_pos P B hP
  obtain ⟨f, hf⟩ := P.count_pos_iff.mp hP
  have hW : 0 < W := windowWidth_pos P ⟨f, hf⟩ x
  have hu : 0 < u := relativeTolerance_pos M hε
  have hM : 0 < M := pow_pos (Nat.succ_pos d) _
  have he : 0 < e := halfTolerance_pos M hε hW
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have ha := clockThreshold_bounds hM
  have hxB : ball P.edge x (H * t) ⊆ B := Finset.subset_union_left
  have hcmp := comparison_error_one_isolated P T hP hT horder H M (momentOrder H M)
    (momentOrder_pos H hM) hM (BallSchedule.schedule P B rank H d hstrict hheight hdegree x t hxB)
    (clockThreshold M) ha.1 ha.2 (clockThreshold_small hM) (momentOrder_large H hM)
    (R * W) (mul_nonneg hR hW.le) (fun _ => rfl) (fun _ => rfl)
    (initial_width_bound P x H t R hwidth) t (sweepCount_pos H M R ε hε) x y
    (mark_mem_schedule P B rank H d hstrict hheight hdegree x t hxB)
    hy (isolated_truncate P B y hy) e he
  have htail := width_tail H M R ε W hR hε hW
  have hsize := minimumWidth_spec H M R ε W hε hmin
  have hzmax : z ≤ 2 * u * W := by
    have hsmall : 2 * (H : ℚ) * t ≤ u * W := hsize.1
    dsimp [z, e]
    nlinarith [mul_pos hu hW]
  have hnear := (near_bound_propagated S hS rank H d hstrict hheight hdegree hxy z hz).trans
    (near_term M ε W z hε hW hsize.2 hzmax)
  have hb : (R * W / e) ^ momentOrder H M / 2 ^ t + LocalError.nearProbability P x y z ≤ ε := by
    exact (add_le_add htail hnear).trans (by linarith)
  have hforward := hcmp.1.trans hb
  have hreverse := hcmp.2.trans hb
  have hfullF : weakProbability P x y = weakProbability S x y :=
    weakProbability_congr (propagateSystem_valid S) x y
  have hfullR : weakProbability P y x = weakProbability S y x :=
    weakProbability_congr (propagateSystem_valid S) y x
  have hlocalF : weakProbability T x y = localWeakProbability S H d R ε x y :=
    (localWeakProbability_eq_truncate S hS H d R ε x y).symm
  have hlocalR : weakProbability T y x = localWeakProbability S H d R ε y x := by
    rw [localWeakProbability_eq_truncate S hS H d R ε y x, LocalAccuracy.queryBall_comm S H d R ε y x]
  rw [hfullF, hlocalF, abs_sub_comm] at hforward
  rw [hfullR, hlocalR, abs_sub_comm] at hreverse
  exact ⟨hforward, hreverse⟩

/-- A mark is either isolated, or its touched component has the promised scale
ratio and its own interval is sufficiently wide. -/
def MarkCondition (S : WeakSystem (Fin n) (K + 1)) (H d : ℕ) (R ε : ℚ) (x : Fin n) : Prop :=
  Isolated S.edge x ∨
    ((∀ v, Connected S.edge x v →
      windowWidth (propagateSystem S) v ≤ R * windowWidth (propagateSystem S) x) ∧
      (minimumWidth H (influenceSize H d) R ε : ℚ) ≤ windowWidth (propagateSystem S) x)

/-- The manuscript's local comparison guarantee including every isolated and
mixed-width case. No minimum-width condition is imposed on isolated labels. -/
theorem comparison_accuracy_with_isolated (S : WeakSystem (Fin n) (K + 1)) (hS : 0 < S.count)
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (rank : Fin n → ℕ) (H d : ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d)
    (R ε : ℚ) (hR : 0 ≤ R) (hε : 0 < ε) (x y : Fin n) (hxy : y ≠ x)
    (hx : MarkCondition S H d R ε x) (hy : MarkCondition S H d R ε y) :
    |localWeakProbability S H d R ε x y - weakProbability S x y| ≤ ε := by
  rcases hx with hx | ⟨hxratio, hxmin⟩
  · rcases hy with hy | ⟨hyratio, hymin⟩
    · rw [comparison_exact S hS H d R ε x y hx hy, sub_self, abs_zero]
      exact hε.le
    · exact (comparison_accuracy_mixed S hS horder rank H d hstrict hheight hdegree
        R ε hR hε y x hxy.symm hyratio hymin hx).2
  · rcases hy with hy | ⟨hyratio, hymin⟩
    · exact (comparison_accuracy_mixed S hS horder rank H d hstrict hheight hdegree
        R ε hR hε x y hxy hxratio hxmin hy).1
    · exact LocalAccuracy.comparison_accuracy S hS horder rank H d hstrict hheight hdegree
        R ε hR hε x y hxy hxratio hyratio hxmin hymin

/-- The matching cumulative guarantee includes isolated labels of any width. -/
theorem cdf_accuracy_with_isolated (S : WeakSystem (Fin n) (K + 1)) (hS : 0 < S.count)
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (rank : Fin n → ℕ) (H d : ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d)
    (R ε : ℚ) (hR : 0 ≤ R) (hε : 0 < ε) (x : Fin n)
    (hx : MarkCondition S H d R ε x) (cut : ℕ) :
    |CDFAccuracy.localCDF S H d R ε x cut - MarginalCalibration.cdf S x cut| ≤ ε := by
  rcases hx with hx | ⟨hratio, hmin⟩
  · rw [cdf_exact S hS H d R ε x hx cut, sub_self, abs_zero]
    exact hε.le
  · exact CDFAccuracy.cdf_accuracy S hS horder rank H d hstrict hheight hdegree
      R ε hR hε x hratio hmin cut

end SortingAdversary.Optimal.IsolatedAccuracy
