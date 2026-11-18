import SortingAdversary.Continuous.PolylogSchedule
import SortingAdversary.Continuous.PolylogEnclosureWork
import SortingAdversary.Continuous.PolylogSelection

/-!
# Uniform work and precision for the actual local digit enumeration

The same stage controls the dimension of the retained graph, the number
of digit words at half accuracy, and the precision of every affine endpoint.
The counted evaluator takes the two rounded tables of that local graph.
-/

namespace SortingAdversary.Continuous.PolylogLocalBudget

open UniformStages PolylogSchedule ArbitraryLabels FiniteAveraging
open CertificateSuccess EnclosureParameters Optimal Optimal.GraphBalls

variable {n : ℕ} (extra : CappedArithmetic.Expr)

private abbrev height (extra : CappedArithmetic.Expr) (n : ℕ) := pathHeight (parameter extra n)
private abbrev width (extra : CappedArithmetic.Expr) (n : ℕ) :=
  widthThreshold (parameter extra n) (height extra n)
private abbrev delta (extra : CappedArithmetic.Expr) (n : ℕ) :=
  accuracy (parameter extra n) (neighborhoodBound (parameter extra n) (height extra n)) (width extra n)

private theorem accuracy_eq_halfDen :
    accuracy (parameter extra n) (neighborhoodBound (parameter extra n) (height extra n)) ((width extra n) / 2) =
      1 / ((2 * accuracyDen (parameter extra n) : ℕ) : ℚ) := by
  rw [PolylogEnclosure.accuracy_half, UniformStages.accuracy_eq]
  push_cast
  ring

/-- The exact calibrated enumeration is dominated by the capped recipe. -/
private theorem enumeration_le (hk : 0 < (parameter extra n)) :
    enumerationBound (parameter extra n) (height extra n)
      (accuracy (parameter extra n) (neighborhoodBound (parameter extra n) (height extra n)) ((width extra n) / 2)) (failure (parameter extra n))
      (accuracy_pos hk _ (half_pos (widthThreshold_pos (parameter extra n) (height extra n)))) (failure_pos hk) ≤
        roundedEnumeration.value (stage extra n) := by
  simp_rw [accuracy_eq_halfDen extra, failure_eq]
  rw [roundedEnumeration_value]
  exact ParameterBounds.enumerationBound_le_envelope _ _ _ _ (failureDen_pos hk)
    (Nat.mul_pos (by decide) (accuracyDen_pos hk)) _ _

variable (D : System (Fin n) ℚ) (hk : 64 ≤ (parameter extra n)) (Q : Finset (Fin n))

private abbrev verts := Neighborhood.labels D (parameter extra n) (height extra n) ((by decide : 0 < 64).trans_le hk)
  ((width extra n) / 2) (half_pos (widthThreshold_pos (parameter extra n) (height extra n))) Q
private abbrev steps := Neighborhood.schedule D (parameter extra n) (height extra n) ((by decide : 0 < 64).trans_le hk)
  ((width extra n) / 2) (half_pos (widthThreshold_pos (parameter extra n) (height extra n))) Q

variable (hQ : Q.card ≤ 2) (hd : ∀ x, (neighbors D.edge x).card ≤ (parameter extra n))

include hk hQ hd in
theorem word_count :
    alphabet (parameter extra n) (height extra n) ^ (steps extra D hk Q).length ≤
      roundedEnumeration.value (stage extra n) := by
  have h := Neighborhood.enclose_length_bound D (parameter extra n) (height extra n) (by omega)
    ((width extra n) / 2) (half_pos (widthThreshold_pos (parameter extra n) (height extra n))) Q hQ hd
  rw [enclose_length] at h
  exact h.trans (enumeration_le extra (by omega))

include hk hQ hd in
theorem vertex_count : (verts extra D hk Q).card ≤ Parameters.logCap n := by
  have hk' : 0 < (parameter extra n) := by omega
  have hm := Neighborhood.labels_card D (parameter extra n) (height extra n) hk' ((width extra n) / 2)
    (half_pos (widthThreshold_pos (parameter extra n) (height extra n))) Q hQ hd
  let δ := accuracy (parameter extra n) (neighborhoodBound (parameter extra n) (height extra n)) ((width extra n) / 2)
  let α := failure (parameter extra n)
  have hδ : 0 < δ := accuracy_pos hk' _ (half_pos (widthThreshold_pos (parameter extra n) (height extra n)))
  have hα : 0 < α := failure_pos hk'
  let R := retainedBound (parameter extra n) (height extra n) δ α hδ hα
  let T := sweepCount (parameter extra n) (height extra n) δ α hδ hα
  have hT : 0 < T := sweepCount_pos (parameter extra n) (height extra n) δ α hδ hα
  have hS : 4 ≤ alphabet (parameter extra n) (height extra n) :=
    Nat.le_of_dvd (alphabet_pos ..) (four_dvd_alphabet ..)
  apply hm.trans
  calc
    R ≤ R * T := Nat.le_mul_of_pos_right _ hT
    _ ≤ 2 ^ (R * T) := Nat.lt_two_pow_self.le
    _ ≤ alphabet (parameter extra n) (height extra n) ^ (R * T) := Nat.pow_le_pow_left (by omega) _
    _ ≤ roundedEnumeration.value (stage extra n) := enumeration_le extra hk'
    _ ≤ Parameters.logCap n := (admitted_costs hk).1

include hk hQ hd in
theorem endpoint_precision :
    PolylogEnclosure.gridBits (delta extra n) +
      (steps extra D hk Q).length * alphabetExponent (parameter extra n) (height extra n) ≤
      Parameters.logCap n := by
  unfold PolylogEnclosure.gridBits delta width height
  rw [UniformStages.accuracy_eq]
  exact precision_le hk (word_count extra D hk Q hQ hd)

include hk hd in
theorem central_anchor_precision (x : Fin n) {J : Certificates.Interval}
    (hw : ∀ v, D.lower v < D.upper v) (hl : D.WeaklyFeasible D.lower)
    (hu : D.WeaklyFeasible D.upper) (h0 : 0 ≤ D.lower x) (h1 : D.upper x ≤ 1)
    (hc : Certificates.centralInterval (PolylogSelection.oneIntervals D
      (PolylogEnclosure.gridBits (delta extra n)) (parameter extra n) (height extra n) (by omega) (width extra n) (widthThreshold_pos (parameter extra n) (height extra n)) x) = some J) :
    OnDyadicGrid (Parameters.logCap n) (Certificates.roundUp J) := by
  rw [PolylogSelection.oneIntervals_full] at hc
  have hp := PolylogEnclosure.roundedCentral_grid D (PolylogEnclosure.gridBits (delta extra n))
    (alphabetExponent (parameter extra n) (height extra n)) (Neighborhood.fullSchedule D (parameter extra n) (height extra n) (by omega) ((width extra n)/2)
      (half_pos (widthThreshold_pos (parameter extra n) (height extra n))) {x}) x hw hl hu h0 h1 hc
  apply Precision.grid_mono hp.2.2
  simpa only [Neighborhood.fullSchedule, List.length_map] using
    endpoint_precision extra D hk {x} (by simp) hd

include hk hQ hd in
theorem evaluation_work (L U : EnclosureWork.StoredSystem (verts extra D hk Q).card) :
    (PolylogEnclosureWork.evaluate L U (alphabet (parameter extra n) (height extra n)) (steps extra D hk Q)).work ≤
      200 * (Parameters.logCap n + 1) ^ 3 := by
  let m := (verts extra D hk Q).card
  let S := alphabet (parameter extra n) (height extra n)
  let t := (steps extra D hk Q).length
  let b := Parameters.logCap n
  have hm : m ≤ b := vertex_count extra D hk Q hQ hd
  have hwords : S ^ t ≤ b := (word_count extra D hk Q hQ hd).trans (admitted_costs hk).1
  have hS : 4 ≤ S := Nat.le_of_dvd (alphabet_pos ..) (four_dvd_alphabet ..)
  have ht : t ≤ b := Nat.lt_two_pow_self.le.trans ((Nat.pow_le_pow_left (by omega : 2 ≤ S) t).trans hwords)
  apply (PolylogEnclosureWork.evaluate_work _ _ _ (alphabet_pos ..) _).trans
  change EnclosureWork.listBound m S t ≤ 200 * (b + 1) ^ 3
  unfold EnclosureWork.listBound EnclosureWork.endpointBound
  calc
    _ ≤ 20 * (b + 1) * b + b * (2 * (b * (60 * (b + 1) + 5) + 5) + 3) + 1 := by
      gcongr
    _ ≤ _ := by nlinarith [Nat.zero_le (b ^ 2), Nat.zero_le (b ^ 3)]

end SortingAdversary.Continuous.PolylogLocalBudget
