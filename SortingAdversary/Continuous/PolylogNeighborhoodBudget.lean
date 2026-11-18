import SortingAdversary.Continuous.PolylogNeighborhood
import SortingAdversary.Continuous.PolylogSchedule

/-! # The logarithmic stage budget bounds repeated neighborhood visits -/

namespace SortingAdversary.Continuous.PolylogNeighborhood

open PolylogSchedule ArbitraryLabels UniformStages CertificateSuccess EnclosureParameters Optimal

/-- A bounded neighborhood may be visited with multiplicity. Even the
two separate incoming/outgoing rows, each of length at most `k`, produce
only quadratically many visits in the logarithmic stage budget. -/
theorem stage_bounds (extra : CappedArithmetic.Expr) (n roots : ℕ) (hq : roots ≤ 2)
    (hk : 64 ≤ parameter extra n) :
    let k := parameter extra n
    let H := pathHeight k
    let w := widthThreshold k H / 2
    let t := Neighborhood.sweeps k H (by omega) w (half_pos (widthThreshold_pos k H))
    let B := Parameters.logCap n
    roots*(2*k+1)^(H*t+1) ≤ 2*B^2 ∧ H*t ≤ B ∧ t ≤ B ∧ k ≤ B := by
  let k := parameter extra n
  let H := pathHeight k
  let w := widthThreshold k H / 2
  have kp : 0 < k := by dsimp [k]; omega
  have hH : 0 < H := by dsimp [H,pathHeight]; positivity
  have hw : 0 < w := half_pos (widthThreshold_pos k H)
  let t := Neighborhood.sweeps k H kp w hw
  let δ := accuracy k (neighborhoodBound k H) w
  let α := failure k
  have hδ := accuracy_pos kp (neighborhoodBound k H) hw
  have hα := failure_pos kp
  have den : δ = 1 / ((2 * accuracyDen k : ℕ) : ℚ) := by
    change accuracy k (neighborhoodBound k (pathHeight k)) (widthThreshold k (pathHeight k)/2) = _
    rw [PolylogEnclosure.accuracy_half,UniformStages.accuracy_eq]
    push_cast; ring
  have hp : enumerationBound k H δ α hδ hα ≤ Parameters.logCap n := by
    simpa only [δ,α,den,UniformStages.failure_eq] using
      (show enumerationBound k H δ α hδ hα ≤ Parameters.logCap n by
        simp_rw [den, show α = 1 / (failureDen k : ℚ) from UniformStages.failure_eq k]
        exact PolylogSchedule.rounded_enumeration_le hk)
  let R := 2*(k+1)^(H*t+2)
  have tpos : 0<t := sweepCount_pos k H δ α hδ hα
  have hr : R ≤ Parameters.logCap n := by
    calc
      R ≤ R*t := Nat.le_mul_of_pos_right R tpos
      _ ≤ 2^(R*t) := Nat.lt_two_pow_self.le
      _ ≤ (alphabet k H)^(R*t) := Nat.pow_le_pow_left
        (by have := Nat.le_of_dvd (alphabet_pos k H) (four_dvd_alphabet k H); omega) _
      _ ≤ _ := hp
  let B := Parameters.logCap n
  have base : (k+1)^(H*t+1) ≤ B := by
    have h := Nat.pow_le_pow_right (by omega : 0 < k+1) (Nat.le_succ (H*t+1))
    change (k+1)^(H*t+1) ≤ (k+1)^(H*t+2) at h
    change 2*(k+1)^(H*t+2) ≤ B at hr
    omega
  have hb : (2*k+1)^(H*t+1) ≤ B^2 := calc
    _ ≤ ((k+1)^2)^(H*t+1) := Nat.pow_le_pow_left (by nlinarith) _
    _ = ((k+1)^(H*t+1))^2 := by rw [← Nat.pow_mul,← Nat.pow_mul,mul_comm]
    _ ≤ _ := Nat.pow_le_pow_left base 2
  have r : H*t ≤ B := calc
    _ ≤ 2^(H*t) := Nat.lt_two_pow_self.le
    _ ≤ (k+1)^(H*t) := Nat.pow_le_pow_left (by omega) _
    _ ≤ (k+1)^(H*t+1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ _)
    _ ≤ _ := base
  have d : k+1 ≤ (k+1)^(H*t+1) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < k+1) (show 1 ≤ H*t+1 by omega)
  exact ⟨Nat.mul_le_mul hq hb,r,(Nat.le_mul_of_pos_left t hH).trans r, (Nat.le_succ k).trans (d.trans base)⟩

/-- A scalar envelope for preparation on short input handles. -/
theorem totalCost_stage (extra : CappedArithmetic.Expr) (n roots W : ℕ) (hq : roots ≤ 2)
    (hk : 64 ≤ parameter extra n) :
    let k := parameter extra n
    let H := pathHeight k
    let w := widthThreshold k H / 2
    let t := Neighborhood.sweeps k H (by omega) w (half_pos (widthThreshold_pos k H))
    let B := Parameters.logCap n
    totalCost (2*k) W roots (H*t) t ≤ 10000*(B+1)^7*(W+1) := by
  let k := parameter extra n
  let H := pathHeight k
  let t := Neighborhood.sweeps k H (by dsimp [k]; omega) (widthThreshold k H/2) (half_pos (widthThreshold_pos k H))
  let B := Parameters.logCap n
  obtain ⟨cm,cr,ct,ck⟩ := stage_bounds extra n roots hq hk
  change roots*(2*k+1)^(H*t+1) ≤ 2*B^2 at cm
  change H*t ≤ B at cr
  change t ≤ B at ct
  change k ≤ B at ck
  change totalCost (2*k) W roots (H*t) t ≤ _
  have visits : roots*(4*(2*k+1)^(H*t+1)+2) ≤ 8*B^2+4 := by
    rw [Nat.mul_add]
    have h := Nat.mul_le_mul_left 4 cm
    rw [← Nat.mul_assoc, Nat.mul_comm roots 4, Nat.mul_assoc]
    omega
  unfold totalCost
  dsimp only
  calc
    _ ≤ 8*B^2 + 4 + 1 + 13*(2*B^2+1)^2 + 3*(2*B^2)+1 + prepCost (2*B^2) (2*B) W 2 B B := by
      unfold prepCost gatherCost
      gcongr
    _ ≤ 10000*(B+1)^7*(W+1) := by
      unfold prepCost gatherCost
      ring_nf
      omega

end SortingAdversary.Continuous.PolylogNeighborhood
