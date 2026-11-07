import SortingAdversary.Optimal.LocalAccuracy
import SortingAdversary.Optimal.CDFCoupling

/-!
# Complete CDF accuracy of the induced sparse-ball law

All numerical constants are the same explicit constants as for comparisons.
The threshold can be any natural number, including outside the palette.
-/

namespace SortingAdversary.Optimal.CDFAccuracy

open WeakMaps GraphBalls BallSchedule CouplingHistory LocalParameters NumericalGeometry
open SparseClosure TruncatedLaw LocalAccuracy CDFCoupling

variable {n K : ℕ}

def queryBall (S : WeakSystem (Fin n) (K + 1)) (H d : ℕ) (R ε : ℚ) (x : Fin n) : Finset (Fin n) :=
  ball S.edge x (H * sweepCount H (influenceSize H d) R ε)

theorem mark_mem_queryBall (S : WeakSystem (Fin n) (K + 1)) (H d : ℕ) (R ε : ℚ) (x : Fin n) :
    x ∈ queryBall S H d R ε x := center_mem_ball S.edge x _

/-- Exact local CDF on one induced ball with the original propagated walls. -/
def localCDF (S : WeakSystem (Fin n) (K + 1)) (H d : ℕ) (R ε : ℚ) (x : Fin n) (cut : ℕ) : ℚ :=
  MarginalCalibration.cdf (LocalChoice.induced (propagateSystem S) (queryBall S H d R ε x))
    ⟨x, mark_mem_queryBall S H d R ε x⟩ cut

theorem queryBall_card (S : WeakSystem (Fin n) (K + 1)) (H d : ℕ) (R ε : ℚ)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d) (x : Fin n) :
    (queryBall S H d R ε x).card ≤ (d + 1) ^ (H * sweepCount H (influenceSize H d) R ε) :=
  ball_card_le S.edge d hdegree x _

/-- Full CDF accuracy, with no assumed mixing or near-threshold conclusion. -/
theorem cdf_accuracy (S : WeakSystem (Fin n) (K + 1)) (hS : 0 < S.count)
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (rank : Fin n → ℕ) (H d : ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d)
    (R ε : ℚ) (hR : 0 ≤ R) (hε : 0 < ε) (x : Fin n)
    (hwidth : ∀ v, Connected S.edge x v →
      windowWidth (propagateSystem S) v ≤ R * windowWidth (propagateSystem S) x)
    (hmin : (minimumWidth H (influenceSize H d) R ε : ℚ) ≤ windowWidth (propagateSystem S) x)
    (cut : ℕ) : |localCDF S H d R ε x cut - MarginalCalibration.cdf S x cut| ≤ ε := by
  cases cut with
  | zero =>
    simpa [localCDF, MarginalCalibration.cdf, DiscreteCalibration.cdf] using hε.le
  | succ c =>
    let M := influenceSize H d
    let t := sweepCount H M R ε
    let P := propagateSystem S
    let B := queryBall S H d R ε x
    let W := windowWidth P x
    let u := relativeTolerance M ε
    let e := u * W / 2
    let z := (H : ℚ) * t + e
    have hP : 0 < P.count := by simpa [P] using hS
    obtain ⟨f, hf⟩ := P.count_pos_iff.mp hP
    have hW : 0 < W := windowWidth_pos P ⟨f, hf⟩ x
    have hu : 0 < u := relativeTolerance_pos M hε
    have hM : 0 < M := pow_pos (Nat.succ_pos d) _
    have he : 0 < e := halfTolerance_pos M hε hW
    have hz : 0 ≤ z := by dsimp [z]; positivity
    have ha := clockThreshold_bounds hM
    have hcmp := cdf_error_ball P hP horder rank H d hstrict hheight hdegree
      (momentOrder H M) (momentOrder_pos H hM) (clockThreshold M) ha.1 ha.2
      (clockThreshold_small hM) (momentOrder_large H hM) t x R hR hwidth e he c
    have htail := width_tail H M R ε W hR hε hW
    have hsize := minimumWidth_spec H M R ε W hε hmin
    have hzmax : z ≤ 2 * u * W := by
      have hsmall : 2 * (H : ℚ) * t ≤ u * W := hsize.1
      dsimp [z, e]
      nlinarith [mul_pos hu hW]
    have hnear := (threshold_near_bound_propagated S hS rank H d hstrict hheight hdegree x c z hz).trans
      (near_term M ε W z hε hW hsize.2 hzmax)
    have herror : |MarginalCalibration.cdf P x (c + 1) -
        MarginalCalibration.cdf (truncate P B) x (c + 1)| ≤ ε := by
      have hbounds := add_le_add htail hnear
      change _ ≤ ε / 8 + ε / 2 at hbounds
      exact (hcmp.trans hbounds).trans (by linarith)
    have hfull : MarginalCalibration.cdf P x (c + 1) = MarginalCalibration.cdf S x (c + 1) :=
      cdf_congr (propagateSystem_valid S) x (c + 1)
    have hlocal : MarginalCalibration.cdf (truncate P B) x (c + 1) = localCDF S H d R ε x (c + 1) :=
      cdf_truncate P B hP ⟨x, mark_mem_queryBall S H d R ε x⟩ (c + 1)
    rw [hfull, hlocal, abs_sub_comm] at herror
    exact herror

end SortingAdversary.Optimal.CDFAccuracy
