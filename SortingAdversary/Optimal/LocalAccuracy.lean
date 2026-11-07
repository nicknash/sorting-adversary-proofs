import SortingAdversary.Optimal.NumericalGeometry
import SortingAdversary.Optimal.TruncatedLaw

/-!
# Complete comparison accuracy of the induced sparse-ball law

This assembles the actual finite coupling, sparse-ball geometry, exact induced
law, insertion count and explicit scalar parameters. No local/global probability
error, mixing estimate or near-tie bound is an assumption of the final theorem.
-/

namespace SortingAdversary.Optimal.LocalAccuracy

open WeakMaps LocalChoice GraphBalls BallSchedule CouplingHistory
open LocalParameters NumericalGeometry SparseClosure TruncatedLaw

variable {n K : ℕ}

/-- The manuscript's uniform bound on dependency and clock set sizes. -/
def influenceSize (H d : ℕ) : ℕ := (d + 1) ^ (H + 1)

/-- The computed two-mark neighborhood at the explicit sufficient radius. -/
def queryBall (S : WeakSystem (Fin n) (K + 1)) (H d : ℕ) (R ε : ℚ)
    (x y : Fin n) : Finset (Fin n) :=
  twoBalls S.edge x y (H * sweepCount H (influenceSize H d) R ε)

theorem left_mem_queryBall (S : WeakSystem (Fin n) (K + 1)) (H d : ℕ) (R ε : ℚ)
    (x y : Fin n) : x ∈ queryBall S H d R ε x y :=
  Finset.mem_union_left _ (center_mem_ball S.edge x _)

theorem right_mem_queryBall (S : WeakSystem (Fin n) (K + 1)) (H d : ℕ) (R ε : ℚ)
    (x y : Fin n) : y ∈ queryBall S H d R ε x y :=
  Finset.mem_union_right _ (center_mem_ball S.edge y _)

/-- Exact local estimate, computed on the small induced system with the original
propagated unary intervals. Efficient ideal-state counting may evaluate the
same finite count ratio. -/
def localWeakProbability (S : WeakSystem (Fin n) (K + 1)) (H d : ℕ) (R ε : ℚ)
    (x y : Fin n) : ℚ :=
  weakProbability (induced (propagateSystem S) (queryBall S H d R ε x y))
    ⟨x, left_mem_queryBall S H d R ε x y⟩ ⟨y, right_mem_queryBall S H d R ε x y⟩

theorem queryBall_comm (S : WeakSystem (Fin n) (K + 1)) (H d : ℕ) (R ε : ℚ) (x y : Fin n) :
    queryBall S H d R ε x y = queryBall S H d R ε y x := Finset.union_comm _ _

/-- The actual common-carrier truncation used by the coupling computes the
same estimate as the induced finite system. -/
theorem localWeakProbability_eq_truncate (S : WeakSystem (Fin n) (K + 1)) (hS : 0 < S.count)
    (H d : ℕ) (R ε : ℚ) (x y : Fin n) :
    localWeakProbability S H d R ε x y =
      weakProbability (truncate (propagateSystem S) (queryBall S H d R ε x y)) x y := by
  exact (weakProbability_truncate (propagateSystem S) (queryBall S H d R ε x y)
    (by simpa using hS) ⟨x, left_mem_queryBall S H d R ε x y⟩
    ⟨y, right_mem_queryBall S H d R ε x y⟩).symm

/-- A proved ball-size bound for the actual labels inspected by the oracle. -/
theorem queryBall_card (S : WeakSystem (Fin n) (K + 1)) (H d : ℕ) (R ε : ℚ)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d) (x y : Fin n) :
    (queryBall S H d R ε x y).card ≤
      2 * (d + 1) ^ (H * sweepCount H (influenceSize H d) R ε) :=
  twoBalls_card_le S.edge d hdegree x y _

/-- The local weak-comparison estimate has absolute error at most `ε`.
Structural premises concern only raw degree, directed height, topological
indexing, and propagated widths within each touched component. Different
components may have unrelated widths and palette locations. -/
theorem comparison_accuracy (S : WeakSystem (Fin n) (K + 1)) (hS : 0 < S.count)
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (rank : Fin n → ℕ) (H d : ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d)
    (R ε : ℚ) (hR : 0 ≤ R) (hε : 0 < ε) (x y : Fin n) (hxy : y ≠ x)
    (hwidthX : ∀ v, Connected S.edge x v →
      windowWidth (propagateSystem S) v ≤ R * windowWidth (propagateSystem S) x)
    (hwidthY : ∀ v, Connected S.edge y v →
      windowWidth (propagateSystem S) v ≤ R * windowWidth (propagateSystem S) y)
    (hminX : (minimumWidth H (influenceSize H d) R ε : ℚ) ≤ windowWidth (propagateSystem S) x)
    (hminY : (minimumWidth H (influenceSize H d) R ε : ℚ) ≤ windowWidth (propagateSystem S) y) :
    |localWeakProbability S H d R ε x y - weakProbability S x y| ≤ ε := by
  let M := influenceSize H d
  let t := sweepCount H M R ε
  let P := propagateSystem S
  let B := queryBall S H d R ε x y
  let Wx := windowWidth P x
  let Wy := windowWidth P y
  let u := relativeTolerance M ε
  let ex := u * Wx / 2
  let ey := u * Wy / 2
  let z := ((H : ℚ) * t + ex) + ((H : ℚ) * t + ey)
  have hP : 0 < P.count := by simpa [P] using hS
  obtain ⟨f, hf⟩ := P.count_pos_iff.mp hP
  have hWx : 0 < Wx := windowWidth_pos P ⟨f, hf⟩ x
  have hWy : 0 < Wy := windowWidth_pos P ⟨f, hf⟩ y
  have hu : 0 < u := relativeTolerance_pos M hε
  have hM : 0 < M := pow_pos (Nat.succ_pos d) _
  have hex : 0 < ex := halfTolerance_pos M hε hWx
  have hey : 0 < ey := halfTolerance_pos M hε hWy
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have ha := clockThreshold_bounds hM
  have hcmp := comparison_error_twoBalls P hP horder rank H d hstrict hheight hdegree
    (momentOrder H M) (momentOrder_pos H hM) (clockThreshold M) ha.1 ha.2
    (clockThreshold_small hM) (momentOrder_large H hM) t x y R hR hwidthX hwidthY ex ey hex hey
  have htailx := width_tail H M R ε Wx hR hε hWx
  have htaily := width_tail H M R ε Wy hR hε hWy
  have hsizeX := minimumWidth_spec H M R ε Wx hε hminX
  have hsizeY := minimumWidth_spec H M R ε Wy hε hminY
  have hzsum : z ≤ u * (Wx + Wy) := by
    have hxsmall : 2 * (H : ℚ) * t ≤ u * Wx := hsizeX.1
    have hysmall : 2 * (H : ℚ) * t ≤ u * Wy := hsizeY.1
    dsimp [z, ex, ey]
    nlinarith
  have hzmax : z ≤ 2 * u * max Wx Wy := by
    have h := mul_le_mul_of_nonneg_left
      (show Wx + Wy ≤ 2 * max Wx Wy by linarith [le_max_left Wx Wy, le_max_right Wx Wy]) hu.le
    nlinarith
  have hmaxpos : 0 < max Wx Wy := hWx.trans_le (le_max_left _ _)
  have hmaxwidth : 4 * (insertionConstant M : ℚ) ≤ ε * max Wx Wy :=
    hsizeX.2.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hε.le)
  have hnear := (near_bound_max_propagated S hS rank H d hstrict hheight hdegree hxy z hz).trans
    (near_term M ε (max Wx Wy) z hε hmaxpos hmaxwidth hzmax)
  have herror : |weakProbability P x y - weakProbability (truncate P B) x y| ≤ ε := by
    have hbounds := add_le_add (add_le_add htailx htaily) hnear
    change _ ≤ ε / 8 + ε / 8 + ε / 2 at hbounds
    exact (hcmp.trans hbounds).trans (by linarith)
  have hfull : weakProbability P x y = weakProbability S x y :=
    weakProbability_congr (propagateSystem_valid S) x y
  have hlocal : weakProbability (truncate P B) x y = localWeakProbability S H d R ε x y :=
    weakProbability_truncate P B hP ⟨x, left_mem_queryBall S H d R ε x y⟩
      ⟨y, right_mem_queryBall S H d R ε x y⟩
  rw [hfull, hlocal, abs_sub_comm] at herror
  exact herror

end SortingAdversary.Optimal.LocalAccuracy
