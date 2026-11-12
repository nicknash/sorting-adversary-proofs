import SortingAdversary.Continuous.StageWork
import SortingAdversary.Continuous.NeighborhoodWork
import SortingAdversary.Continuous.SelectionKernelWork

/-!
# Concrete measured public selection routines

Calibration, neighborhood extraction, endpoint enumeration, certification and
rounding are all executed by measured routines. The values equal the public
continuous adversary on the original labels. Accepted-stage work bounds use
the actual graph degree and common endpoint grid, with no runtime oracle.
-/

namespace SortingAdversary.Continuous.SelectionWork

open FiniteAveraging Precision EnclosureWork EnclosureParameters UniformStages
open SortingAdversary.Optimal GraphBalls

variable {n : ℕ}

def select (D : StoredSystem n) (k : ℕ) (hk : 0 < k) (x y : Fin n) :
    PrimitiveWork.Result (LocalSelection.Result n) :=
  let parameters := StageWork.calibrate k hk
  let schedule := NeighborhoodWork.twoSchedule D parameters.value.height parameters.value.sweeps x y
  let result := SelectionKernelWork.selectTwo D k parameters.value.alphabet schedule.value x y
  ⟨result.value, parameters.work + schedule.work + result.work⟩

def selectThreshold (D : StoredSystem n) (k : ℕ) (hk : 0 < k) (x : Fin n) (c : ℚ) :
    PrimitiveWork.Result (LocalSelection.Result n) :=
  let parameters := StageWork.calibrate k hk
  let schedule := NeighborhoodWork.oneSchedule D parameters.value.height parameters.value.sweeps x
  let result := SelectionKernelWork.selectThreshold D k parameters.value.alphabet schedule.value x c
  ⟨result.value, parameters.work + schedule.work + result.work⟩

def chooseAnchor (D : StoredSystem n) (k : ℕ) (hk : 0 < k) (x : Fin n) :
    PrimitiveWork.Result ℚ :=
  let parameters := StageWork.calibrate k hk
  let schedule := NeighborhoodWork.oneSchedule D parameters.value.height parameters.value.sweeps x
  let result := SelectionKernelWork.chooseAnchor D parameters.value.alphabet schedule.value x
  ⟨result.value, parameters.work + schedule.work + result.work⟩

theorem oneSchedule_value (D : StoredSystem n) (k : ℕ) (hk : 0 < k) (x : Fin n) :
    (NeighborhoodWork.oneSchedule D (StageWork.calibrate k hk).value.height
      (StageWork.calibrate k hk).value.sweeps x).value =
      ArbitraryLabels.fullSchedule D.system k (ArbitraryLabels.pathHeight k) hk {x} := by
  rw [StageWork.calibrate_height]
  exact NeighborhoodWork.oneSchedule_value D k _ hk _ (StageWork.calibrate_sweeps k hk) x

theorem twoSchedule_value (D : StoredSystem n) (k : ℕ) (hk : 0 < k) (x y : Fin n) :
    (NeighborhoodWork.twoSchedule D (StageWork.calibrate k hk).value.height
      (StageWork.calibrate k hk).value.sweeps x y).value =
      ArbitraryLabels.fullSchedule D.system k (ArbitraryLabels.pathHeight k) hk {x, y} := by
  rw [StageWork.calibrate_height]
  exact NeighborhoodWork.twoSchedule_value D k _ hk _ (StageWork.calibrate_sweeps k hk) x y

@[simp] theorem select_value (D : StoredSystem n) (k : ℕ) (hk : 0 < k) (x y : Fin n) :
    (select D k hk x y).value = ArbitraryLabels.select D.system k x y := by
  simp only [select, SelectionKernelWork.selectTwo_value, twoSchedule_value,
    StageWork.calibrate_alphabet, ArbitraryLabels.select_pos D.system k hk,
    ArbitraryLabels.selectTwoWithHeight, ArbitraryLabels.twoIntervals_eq_full,
    LocalSelection.selectTwo]
  rfl

@[simp] theorem selectThreshold_value (D : StoredSystem n) (k : ℕ) (hk : 0 < k)
    (x : Fin n) (c : ℚ) :
    (selectThreshold D k hk x c).value = ArbitraryLabels.selectThreshold D.system k x c := by
  simp only [selectThreshold, SelectionKernelWork.selectThreshold_value, oneSchedule_value,
    StageWork.calibrate_alphabet, ArbitraryLabels.selectThreshold_pos D.system k hk,
    ArbitraryLabels.selectThresholdWithHeight, ArbitraryLabels.thresholdIntervals_eq_full,
    LocalSelection.selectThreshold]
  rfl

@[simp] theorem chooseAnchor_value (D : StoredSystem n) (k : ℕ) (hk : 0 < k) (x : Fin n) :
    (chooseAnchor D k hk x).value = ArbitraryLabels.chooseAnchor D.system k x := by
  simp only [chooseAnchor, SelectionKernelWork.chooseAnchor_value, oneSchedule_value,
    StageWork.calibrate_alphabet, ArbitraryLabels.chooseAnchor_pos D.system k hk,
    ArbitraryLabels.anchorWithHeight, ArbitraryLabels.oneIntervals_eq_full, LocalSelection.anchor]

theorem admitted_budget (j cap : ℕ) (hcap : Recipe.budget.need j ≤ cap) (hk : 0 < degree j) :
    enumerationBudget (degree j) hk ≤ cap := by
  apply (enumerationBudget_le (degree j) hk).trans
  exact (Recipe.budget.value_le_need j).trans hcap

theorem admitted_words (D : StoredSystem n) (j : ℕ) (hk : 0 < degree j)
    (hcap : Recipe.budget.need j ≤ n) (Q : Finset (Fin n)) (hQ : Q.card ≤ 2)
    (hdegree : ∀ x, (neighbors D.system.edge x).card ≤ degree j) :
    alphabet (degree j) (ArbitraryLabels.pathHeight (degree j)) ^
      (ArbitraryLabels.fullSchedule D.system (degree j) (ArbitraryLabels.pathHeight (degree j)) hk Q).length ≤ n := by
  have h := RuntimePrecision.localWordCount_le_budget D.system (degree j) hk Q hQ hdegree
  rw [enclose_length] at h
  exact h.trans (admitted_budget j n hcap hk)

theorem length_le_wordCount (S m : ℕ) (hS : 2 ≤ S) : m ≤ S ^ m :=
  Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hS m)

def localBound (n F : ℕ) : ℕ := 20000 * (n + F + 1) ^ 5

private theorem combined_bound (n F s S m : ℕ) (hs : s ≤ n) (hm : m ≤ n) (hE : S ^ m ≤ n) :
    10010 * (n + 1) ^ 5 + listBound n S m + 65 * (S ^ m + 1) ^ 2 +
      6 * (2 * F + s * m) + 40 ≤ localBound n F := by
  let N := n + F + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hn : n + 1 ≤ N := by dsimp [N]; omega
  have hF : F ≤ N := by dsimp [N]; omega
  have hE' : S ^ m + 1 ≤ N := by dsimp [N]; omega
  have hn5 := Nat.pow_le_pow_left hn 5
  have hN15 : N ≤ N ^ 5 := by simpa using Nat.pow_le_pow_right (by omega : 0 < N) (by decide : 1 ≤ 5)
  have hN25 : N ^ 2 ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hN35 : N ^ 3 ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hN5 : 1 ≤ N ^ 5 := Nat.one_le_pow _ _ hN
  have he2 := (Nat.pow_le_pow_left hE' 2).trans hN25
  have hsm : s * m ≤ N ^ 5 := by
    apply (Nat.mul_le_mul (hs.trans (by omega : n ≤ N)) (hm.trans (by omega : n ≤ N))).trans
    simpa only [pow_two] using hN25
  have hl := SelectionKernelWork.listBound_polynomial n S m n hm hE
  have harg : n + n + 1 ≤ 2 * N := by dsimp [N]; omega
  have hcube := Nat.pow_le_pow_left harg 3
  have hl' : listBound n S m ≤ 1600 * N ^ 5 := by
    have hp : (2 * N) ^ 3 = 8 * N ^ 3 := by ring
    rw [hp] at hcube
    nlinarith
  unfold localBound
  change _ ≤ 20000 * N ^ 5
  nlinarith

private theorem combine_select (W K L E F s m P B : ℕ)
    (hW : W ≤ P) (hK : K ≤ L + 20 * (E + 1) + 6 * F + 38)
    (hB : P + L + 65 * (E + 1) ^ 2 + 6 * (2 * F + s * m) + 40 ≤ B) :
    W + K ≤ B := by nlinarith [Nat.zero_le (s * m)]

private theorem combine_anchor (W K L E F s m P B : ℕ)
    (hW : W ≤ P) (hK : K ≤ L + 65 * (E + 1) ^ 2 + 6 * (2 * F + s * m) + 37)
    (hB : P + L + 65 * (E + 1) ^ 2 + 6 * (2 * F + s * m) + 40 ≤ B) :
    W + K ≤ B := by omega

theorem select_work (D : StoredSystem n) (j F : ℕ) (hk : 0 < degree j)
    (hcap : Recipe.budget.need j ≤ n) (x y : Fin n) (hg : BoundsOnGrid D.system F)
    (hunit : ∀ z, 0 ≤ D.system.lower z ∧ D.system.upper z ≤ 1)
    (hwidth : ∀ z, D.system.lower z < D.system.upper z)
    (hdegree : ∀ z, (neighbors D.system.edge z).card ≤ degree j) :
    (select D (degree j) hk x y).work ≤ (StageWork.calibrate (degree j) hk).work + localBound n F := by
  let P := (StageWork.calibrate (degree j) hk).value
  let schedule := NeighborhoodWork.twoSchedule D P.height P.sweeps x y
  have hscalar := admitted_scalar_bounds j n hcap
  have hH : P.height ≤ n := by simpa only [P, StageWork.calibrate_height] using hscalar.2.1
  have hs : alphabetExponent (degree j) (ArbitraryLabels.pathHeight (degree j)) ≤ n := hscalar.2.2.2.1
  have ht : P.sweeps ≤ n := by
    simpa only [P, StageWork.calibrate_sweeps, Neighborhood.sweeps] using admitted_sweepCount j n hcap
  have hprepare := NeighborhoodWork.twoSchedule_work D P.height P.sweeps hH ht x y
  change schedule.work ≤ 10010 * (n + 1) ^ 5 at hprepare
  have hS : 0 < P.alphabet := by simp only [P, StageWork.calibrate_alphabet]; exact alphabet_pos _ _
  have hS2 : 2 ≤ P.alphabet := by
    simp only [P, StageWork.calibrate_alphabet]
    have hh := alphabet_large (degree j) (ArbitraryLabels.pathHeight (degree j))
    have hM := neighborhoodBound_pos (degree j) (ArbitraryLabels.pathHeight (degree j))
    nlinarith
  have hE : P.alphabet ^ schedule.value.length ≤ n := by
    simpa only [P, schedule, StageWork.calibrate_alphabet, twoSchedule_value] using
      admitted_words D j hk hcap {x, y} (by
        simpa using Finset.card_insert_le x ({y} : Finset (Fin n))) hdegree
  have hm := (length_le_wordCount P.alphabet schedule.value.length hS2).trans hE
  have hkernel := SelectionKernelWork.selectTwo_work D (degree j) P.alphabet F hS schedule.value x y hg hunit hwidth
  have hcombined := combined_bound n F (alphabetExponent (degree j) (ArbitraryLabels.pathHeight (degree j)))
    P.alphabet schedule.value.length hs hm hE
  change (StageWork.calibrate (degree j) hk).work + schedule.work +
    (SelectionKernelWork.selectTwo D (degree j) P.alphabet schedule.value x y).work ≤ _
  have htotal := combine_select _ _ _ _ _ _ _ _ _ hprepare hkernel hcombined
  omega

theorem selectThreshold_work (D : StoredSystem n) (j F : ℕ) (hk : 0 < degree j)
    (hcap : Recipe.budget.need j ≤ n) (x : Fin n) (c : ℚ) (hg : BoundsOnGrid D.system F)
    (hunit : 0 ≤ D.system.lower x ∧ D.system.upper x ≤ 1)
    (hwidth : D.system.lower x < D.system.upper x)
    (hdegree : ∀ z, (neighbors D.system.edge z).card ≤ degree j) :
    (selectThreshold D (degree j) hk x c).work ≤
      (StageWork.calibrate (degree j) hk).work + localBound n F := by
  let P := (StageWork.calibrate (degree j) hk).value
  let schedule := NeighborhoodWork.oneSchedule D P.height P.sweeps x
  have hscalar := admitted_scalar_bounds j n hcap
  have hH : P.height ≤ n := by simpa only [P, StageWork.calibrate_height] using hscalar.2.1
  have hs : alphabetExponent (degree j) (ArbitraryLabels.pathHeight (degree j)) ≤ n := hscalar.2.2.2.1
  have ht : P.sweeps ≤ n := by
    simpa only [P, StageWork.calibrate_sweeps, Neighborhood.sweeps] using admitted_sweepCount j n hcap
  have hprepare := NeighborhoodWork.oneSchedule_work D P.height P.sweeps hH ht x
  change schedule.work ≤ 10010 * (n + 1) ^ 5 at hprepare
  have hS : 0 < P.alphabet := by simp only [P, StageWork.calibrate_alphabet]; exact alphabet_pos _ _
  have hS2 : 2 ≤ P.alphabet := by
    simp only [P, StageWork.calibrate_alphabet]
    have hh := alphabet_large (degree j) (ArbitraryLabels.pathHeight (degree j))
    have hM := neighborhoodBound_pos (degree j) (ArbitraryLabels.pathHeight (degree j))
    nlinarith
  have hE : P.alphabet ^ schedule.value.length ≤ n := by
    simpa only [P, schedule, StageWork.calibrate_alphabet, oneSchedule_value] using
      admitted_words D j hk hcap {x} (by simp) hdegree
  have hm := (length_le_wordCount P.alphabet schedule.value.length hS2).trans hE
  have hkernel := SelectionKernelWork.selectThreshold_work D (degree j) P.alphabet F hS schedule.value x c hg hunit hwidth
  have hcombined := combined_bound n F (alphabetExponent (degree j) (ArbitraryLabels.pathHeight (degree j)))
    P.alphabet schedule.value.length hs hm hE
  change (StageWork.calibrate (degree j) hk).work + schedule.work +
    (SelectionKernelWork.selectThreshold D (degree j) P.alphabet schedule.value x c).work ≤ _
  have htotal := combine_select _ _ _ _ _ _ _ _ _ hprepare hkernel hcombined
  omega

theorem chooseAnchor_work (D : StoredSystem n) (j F : ℕ) (hk : 0 < degree j)
    (hcap : Recipe.budget.need j ≤ n) (x : Fin n) (hg : BoundsOnGrid D.system F)
    (hunit : 0 ≤ D.system.lower x ∧ D.system.upper x ≤ 1)
    (hwidth : ∀ z, D.system.lower z < D.system.upper z)
    (hl : D.system.WeaklyFeasible D.system.lower) (hu : D.system.WeaklyFeasible D.system.upper)
    (hdegree : ∀ z, (neighbors D.system.edge z).card ≤ degree j) :
    (chooseAnchor D (degree j) hk x).work ≤
      (StageWork.calibrate (degree j) hk).work + localBound n F := by
  let P := (StageWork.calibrate (degree j) hk).value
  let schedule := NeighborhoodWork.oneSchedule D P.height P.sweeps x
  have hscalar := admitted_scalar_bounds j n hcap
  have hH : P.height ≤ n := by simpa only [P, StageWork.calibrate_height] using hscalar.2.1
  have hs : P.exponent ≤ n := by simpa only [P, StageWork.calibrate_exponent] using hscalar.2.2.2.1
  have ht : P.sweeps ≤ n := by
    simpa only [P, StageWork.calibrate_sweeps, Neighborhood.sweeps] using admitted_sweepCount j n hcap
  have hprepare := NeighborhoodWork.oneSchedule_work D P.height P.sweeps hH ht x
  change schedule.work ≤ 10010 * (n + 1) ^ 5 at hprepare
  have hS : P.alphabet = 2 ^ P.exponent := by
    simp only [P, StageWork.calibrate_alphabet, StageWork.calibrate_exponent, alphabet]
  have hS2 : 2 ≤ P.alphabet := by
    simp only [P, StageWork.calibrate_alphabet]
    have hh := alphabet_large (degree j) (ArbitraryLabels.pathHeight (degree j))
    have hM := neighborhoodBound_pos (degree j) (ArbitraryLabels.pathHeight (degree j))
    nlinarith
  have hE : P.alphabet ^ schedule.value.length ≤ n := by
    simpa only [P, schedule, StageWork.calibrate_alphabet, oneSchedule_value] using
      admitted_words D j hk hcap {x} (by simp) hdegree
  have hm := (length_le_wordCount P.alphabet schedule.value.length hS2).trans hE
  have hkernel := SelectionKernelWork.chooseAnchor_work D F P.exponent schedule.value x hg hunit hwidth hl hu
  rw [← hS] at hkernel
  have hcombined := combined_bound n F P.exponent P.alphabet schedule.value.length hs hm hE
  change (StageWork.calibrate (degree j) hk).work + schedule.work +
    (SelectionKernelWork.chooseAnchor D P.alphabet schedule.value x).work ≤ _
  have htotal := combine_anchor _ _ _ _ _ _ _ _ _ hprepare hkernel hcombined
  omega

end SortingAdversary.Continuous.SelectionWork
