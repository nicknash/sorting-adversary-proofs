import SortingAdversary.Continuous.StageArithmetic
import SortingAdversary.Continuous.RoundingWork

/-!
# Counted exact calibration

Every scalar power and every failed exponent test is executed and charged.
The least-test loop uses proved existence only for its erased termination
argument; it starts at zero and evaluates the concrete integer tests in
order. The output is exactly the manuscript calibration, not its larger
arithmetic envelope used for admitting a stage.
-/

namespace SortingAdversary.Continuous.StageWork

open SortingAdversary.Optimal PrimitiveWork
open EnclosureParameters UniformStages ArbitraryLabels

def power (a : ℕ) : ℕ → PrimitiveWork.Result ℕ
  | 0 => ⟨1, 1⟩
  | e + 1 => let old := power a e; ⟨old.value * a, old.work + 2⟩

@[simp] theorem power_value (a e : ℕ) : (power a e).value = a ^ e := by
  induction e <;> simp_all [power, pow_succ]

theorem power_work (a e : ℕ) : (power a e).work = 2 * e + 1 := by
  induction e <;> simp_all [power] <;> omega

private theorem next_le_find (test : ℕ → PrimitiveWork.Result Bool)
    (hex : ∃ i, (test i).value = true) (i : ℕ) (hi : i ≤ Nat.find hex)
    (ht : ¬ (test i).value = true) : i + 1 ≤ Nat.find hex := by
  have hne : i ≠ Nat.find hex := by
    intro h
    exact ht (h ▸ Nat.find_spec hex)
  omega

def leastFrom (test : ℕ → PrimitiveWork.Result Bool)
    (hex : ∃ i, (test i).value = true) (i : ℕ) (hi : i ≤ Nat.find hex) : PrimitiveWork.Result ℕ :=
  let current := test i
  if ht : current.value = true then ⟨i, current.work + 1⟩ else
    let rest := leastFrom test hex (i + 1) (next_le_find test hex i hi ht)
    ⟨rest.value, current.work + rest.work + 1⟩
termination_by Nat.find hex - i
decreasing_by have := next_le_find test hex i hi ht; omega

theorem leastFrom_value (test : ℕ → PrimitiveWork.Result Bool)
    (hex : ∃ i, (test i).value = true) (i : ℕ) (hi : i ≤ Nat.find hex) :
    (leastFrom test hex i hi).value = Nat.find hex := by
  unfold leastFrom
  dsimp only
  split
  · rename_i ht
    exact le_antisymm hi (Nat.find_min' hex ht)
  · exact leastFrom_value test hex (i + 1) _
termination_by Nat.find hex - i
decreasing_by have := next_le_find test hex i hi ‹¬(test i).value = true›; omega

theorem leastFrom_work (test : ℕ → PrimitiveWork.Result Bool)
    (hex : ∃ i, (test i).value = true) (i : ℕ) (hi : i ≤ Nat.find hex)
    (b : ℕ) (hb : ∀ j ≤ Nat.find hex, (test j).work ≤ b) :
    (leastFrom test hex i hi).work ≤ (Nat.find hex - i + 1) * (b + 2) := by
  have ht := hb i hi
  unfold leastFrom
  dsimp only
  split
  · rename_i hp
    have he : i = Nat.find hex := le_antisymm hi (Nat.find_min' hex hp)
    subst i
    simp only [Nat.sub_self, Nat.zero_add, one_mul]
    omega
  · rename_i hp
    have hn := next_le_find test hex i hi hp
    have ih := leastFrom_work test hex (i + 1) hn b hb
    have hs : Nat.find hex - i = Nat.find hex - (i + 1) + 1 := by omega
    dsimp only
    rw [hs]
    simp only [Nat.add_mul, one_mul] at ih ⊢
    omega
termination_by Nat.find hex - i
decreasing_by have := next_le_find test hex i hi ‹¬(test i).value = true›; omega

def least (test : ℕ → PrimitiveWork.Result Bool) (hex : ∃ i, (test i).value = true) :
    PrimitiveWork.Result ℕ := leastFrom test hex 0 (Nat.zero_le _)

@[simp] theorem least_value (test : ℕ → PrimitiveWork.Result Bool)
    (hex : ∃ i, (test i).value = true) : (least test hex).value = Nat.find hex :=
  leastFrom_value test hex 0 (Nat.zero_le _)

theorem least_work (test : ℕ → PrimitiveWork.Result Bool)
    (hex : ∃ i, (test i).value = true) (b : ℕ)
    (hb : ∀ j ≤ Nat.find hex, (test j).work ≤ b) :
    (least test hex).work ≤ (Nat.find hex + 1) * (b + 2) := by
  simpa only [least, Nat.sub_zero] using leastFrom_work test hex 0 (Nat.zero_le _) b hb

def comparable (d h : ℕ) : PrimitiveWork.Result ℕ := power (d + 1) (h + 1)

@[simp] theorem comparable_value (d h : ℕ) : (comparable d h).value = neighborhoodBound d h :=
  power_value _ _

def exponent (d h : ℕ) : PrimitiveWork.Result ℕ :=
  let M := comparable d h
  let result := RoundingWork.clogTwo (4 * M.value ^ 2)
  ⟨result.value, M.work + result.work + 4⟩

@[simp] theorem exponent_value (d h : ℕ) : (exponent d h).value = alphabetExponent d h := by
  simp only [exponent, comparable_value, RoundingWork.clogTwo_value, alphabetExponent]

def alphabet (d h : ℕ) : PrimitiveWork.Result ℕ :=
  let e := exponent d h
  let result := StateWork.powTwo e.value
  ⟨result.value, e.work + result.work + 1⟩

@[simp] theorem alphabet_value (d h : ℕ) : (alphabet d h).value = EnclosureParameters.alphabet d h := by
  simp only [alphabet, StateWork.powTwo_value, exponent_value, EnclosureParameters.alphabet]

def momentTest (M base p : ℕ) : PrimitiveWork.Result Bool :=
  let low := power (base - 1) p
  let high := power base p
  ⟨decide (0 < p ∧ 4 * M * low.value ≤ high.value), low.work + high.work + 6⟩

@[simp] theorem momentTest_true (M base p : ℕ) :
    (momentTest M base p).value = true ↔ 0 < p ∧ 4 * M * (base - 1) ^ p ≤ base ^ p := by
  simp only [momentTest, power_value, decide_eq_true_eq]

theorem momentTest_work (M base p : ℕ) : (momentTest M base p).work = 4 * p + 8 := by
  simp only [momentTest, power_work]
  omega

private theorem moment_exists (d h : ℕ) :
    ∃ p, (momentTest (comparable d h).value ((power (alphabet d h).value h).value) p).value = true := by
  obtain ⟨p, hp, htest⟩ := momentPower_exists d h
  refine ⟨p, ?_⟩
  simp only [momentTest_true, comparable_value, power_value, alphabet_value]
  exact ⟨hp, (StageArithmetic.moment_test_iff d h p).mp htest⟩

def moment (d h : ℕ) : PrimitiveWork.Result ℕ :=
  let M := comparable d h
  let S := alphabet d h
  let base := power S.value h
  let result := least (momentTest M.value base.value) (moment_exists d h)
  ⟨result.value, M.work + S.work + base.work + result.work + 3⟩

@[simp] theorem moment_value (d h : ℕ) : (moment d h).value = momentPower d h := by
  simp only [moment, least_value]
  unfold momentPower
  apply Nat.find_congr'
  intro p
  simp only [momentTest_true, comparable_value, power_value, alphabet_value]
  exact and_congr_right (fun _ => (StageArithmetic.moment_test_iff d h p).symm)

def accuracyDen (k : ℕ) : PrimitiveWork.Result ℕ :=
  let H := StateWork.powTwo (k + 1)
  let M := comparable k H.value
  let width := StateWork.powTwo (2 * k * M.value)
  ⟨800 * k * (M.value + 1) * width.value, H.work + M.work + width.work + 8⟩

@[simp] theorem accuracyDen_value (k : ℕ) : (accuracyDen k).value = UniformStages.accuracyDen k := by
  simp only [accuracyDen, StateWork.powTwo_value, comparable_value, UniformStages.accuracyDen,
    pathHeight]

def sweepTest (threshold t : ℕ) : PrimitiveWork.Result Bool :=
  let power := StateWork.powTwo t
  ⟨decide (0 < t ∧ threshold ≤ power.value), power.work + 2⟩

@[simp] theorem sweepTest_true (threshold t : ℕ) :
    (sweepTest threshold t).value = true ↔ 0 < t ∧ threshold ≤ 2 ^ t := by
  simp only [sweepTest, StateWork.powTwo_value, decide_eq_true_eq]

theorem sweepTest_work (threshold t : ℕ) : (sweepTest threshold t).work = 2 * t + 3 := by
  simp [sweepTest]

private theorem sweep_exists (threshold : ℕ) : ∃ t, (sweepTest threshold t).value = true := by
  refine ⟨threshold + 1, ?_⟩
  rw [sweepTest_true]
  exact ⟨Nat.succ_pos _, (Nat.le_succ _).trans (Nat.lt_two_pow_self (n := threshold + 1)).le⟩

def sweeps (k : ℕ) (_hk : 0 < k) : PrimitiveWork.Result ℕ :=
  let H := StateWork.powTwo (k + 1)
  let p := moment k H.value
  let D := accuracyDen k
  let Dp := power D.value p.value
  let threshold := 2 * (200 * k) * Dp.value
  let result := least (sweepTest threshold) (sweep_exists threshold)
  ⟨result.value, H.work + p.work + D.work + Dp.work + result.work + 6⟩

@[simp] theorem sweeps_value (k : ℕ) (hk : 0 < k) : (sweeps k hk).value =
    Neighborhood.sweeps k (pathHeight k) hk (widthThreshold k (pathHeight k)) (widthThreshold_pos _ _) := by
  simp only [sweeps, least_value]
  unfold Neighborhood.sweeps sweepCount
  apply Nat.find_congr'
  intro t
  simp only [sweepTest_true, power_value, accuracyDen_value, moment_value, StateWork.powTwo_value]
  rw [UniformStages.accuracy_eq, UniformStages.failure_eq]
  exact and_congr_right (fun _ => (StageArithmetic.sweep_test_iff
    (UniformStages.failureDen k) (UniformStages.accuracyDen k) (momentPower k (pathHeight k)) t
    (failureDen_pos hk) (accuracyDen_pos hk)).symm)

structure Parameters where
  height : ℕ
  exponent : ℕ
  alphabet : ℕ
  moment : ℕ
  sweeps : ℕ
  radius : ℕ

def calibrate (k : ℕ) (hk : 0 < k) : PrimitiveWork.Result Parameters :=
  let H := StateWork.powTwo (k + 1)
  let e := exponent k H.value
  let S := alphabet k H.value
  let p := moment k H.value
  let t := sweeps k hk
  ⟨⟨H.value, e.value, S.value, p.value, t.value, H.value * t.value⟩,
    H.work + e.work + S.work + p.work + t.work + 2⟩

@[simp] theorem calibrate_height (k : ℕ) (hk : 0 < k) : (calibrate k hk).value.height = pathHeight k := by
  simp only [calibrate, StateWork.powTwo_value, pathHeight]

@[simp] theorem calibrate_exponent (k : ℕ) (hk : 0 < k) :
    (calibrate k hk).value.exponent = alphabetExponent k (pathHeight k) := by
  simp only [calibrate, exponent_value, StateWork.powTwo_value, pathHeight]

@[simp] theorem calibrate_alphabet (k : ℕ) (hk : 0 < k) :
    (calibrate k hk).value.alphabet = EnclosureParameters.alphabet k (pathHeight k) := by
  simp only [calibrate, alphabet_value, StateWork.powTwo_value, pathHeight]

@[simp] theorem calibrate_moment (k : ℕ) (hk : 0 < k) :
    (calibrate k hk).value.moment = momentPower k (pathHeight k) := by
  simp only [calibrate, moment_value, StateWork.powTwo_value, pathHeight]

@[simp] theorem calibrate_sweeps (k : ℕ) (hk : 0 < k) :
    (calibrate k hk).value.sweeps =
      Neighborhood.sweeps k (pathHeight k) hk (widthThreshold k (pathHeight k)) (widthThreshold_pos _ _) := by
  simp only [calibrate, sweeps_value]

@[simp] theorem calibrate_radius (k : ℕ) (hk : 0 < k) :
    (calibrate k hk).value.radius = pathHeight k *
      Neighborhood.sweeps k (pathHeight k) hk (widthThreshold k (pathHeight k)) (widthThreshold_pos _ _) := by
  simp only [calibrate, sweeps_value, StateWork.powTwo_value, pathHeight]

theorem comparable_work (d h : ℕ) : (comparable d h).work = 2 * h + 3 := by
  simp only [comparable, power_work]
  omega

theorem exponent_work (d h : ℕ) :
    (exponent d h).work = 2 * h + 4 * alphabetExponent d h + 8 := by
  simp only [exponent, comparable_work, comparable_value, RoundingWork.clogTwo_work,
    alphabetExponent]
  omega

theorem alphabet_work (d h : ℕ) :
    (alphabet d h).work = 2 * h + 6 * alphabetExponent d h + 10 := by
  simp only [alphabet, exponent_work, exponent_value, StateWork.powTwo_work]
  omega

theorem moment_work (d h cap : ℕ) (hh : h ≤ cap)
    (he : alphabetExponent d h ≤ cap) (hp : momentPower d h ≤ cap) :
    (moment d h).work ≤ 40 * (cap + 1) ^ 2 := by
  have hf : Nat.find (moment_exists d h) = momentPower d h := by
    simpa only [moment, least_value] using moment_value d h
  have hl := least_work (momentTest (comparable d h).value
    (power (alphabet d h).value h).value) (moment_exists d h) (4 * cap + 8) (by
      intro i hi
      rw [momentTest_work]
      rw [hf] at hi
      omega)
  rw [hf] at hl
  have hb := Nat.mul_le_mul_right (4 * cap + 8 + 2) (Nat.add_le_add_right hp 1)
  simp only [moment, comparable_work, alphabet_work, power_work]
  nlinarith

theorem accuracyDen_work (k cap : ℕ) (hk : k ≤ cap) (hH : pathHeight k ≤ cap)
    (hB : neighborhoodBound k (pathHeight k) ≤ cap) :
    (accuracyDen k).work ≤ 20 * (cap + 1) ^ 2 := by
  have hb := Nat.mul_le_mul hk hB
  simp only [accuracyDen, StateWork.powTwo_value, StateWork.powTwo_work, comparable_work,
    comparable_value]
  change 2 * (k + 1) + 1 + (2 * pathHeight k + 3) +
    (2 * (2 * k * neighborhoodBound k (pathHeight k)) + 1) + 8 ≤ _
  nlinarith

theorem sweeps_work (k cap : ℕ) (hk : 0 < k) (hkc : k ≤ cap)
    (hH : pathHeight k ≤ cap) (hB : neighborhoodBound k (pathHeight k) ≤ cap)
    (he : alphabetExponent k (pathHeight k) ≤ cap)
    (hp : momentPower k (pathHeight k) ≤ cap)
    (ht : Neighborhood.sweeps k (pathHeight k) hk (widthThreshold k (pathHeight k))
      (widthThreshold_pos _ _) ≤ cap) :
    (sweeps k hk).work ≤ 100 * (cap + 1) ^ 2 := by
  let threshold := 2 * (200 * k) *
    (power (accuracyDen k).value (moment k (StateWork.powTwo (k + 1)).value).value).value
  have hf : Nat.find (sweep_exists threshold) =
      Neighborhood.sweeps k (pathHeight k) hk (widthThreshold k (pathHeight k))
        (widthThreshold_pos _ _) := by
    simpa only [sweeps, least_value] using sweeps_value k hk
  have hl := least_work (sweepTest threshold) (sweep_exists threshold) (2 * cap + 3) (by
    intro i hi
    rw [sweepTest_work]
    rw [hf] at hi
    omega)
  rw [hf] at hl
  have hb := Nat.mul_le_mul_right (2 * cap + 3 + 2) (Nat.add_le_add_right ht 1)
  have hm := moment_work k (pathHeight k) cap hH he hp
  have hd := accuracyDen_work k cap hkc hH hB
  change (StateWork.powTwo (k + 1)).work +
    (moment k (StateWork.powTwo (k + 1)).value).work + (accuracyDen k).work +
    (power (accuracyDen k).value (moment k (StateWork.powTwo (k + 1)).value).value).work +
    (least (sweepTest threshold) (sweep_exists threshold)).work + 6 ≤ _
  simp only [StateWork.powTwo_work, StateWork.powTwo_value, power_work, moment_value]
  change 2 * (k + 1) + 1 + (moment k (pathHeight k)).work + (accuracyDen k).work +
    (2 * momentPower k (pathHeight k) + 1) +
    (least (sweepTest threshold) (sweep_exists threshold)).work + 6 ≤ _
  nlinarith

/-- Every concrete search, including each rejected test, has a common
quadratic word bound once the fixed stage has been admitted. -/
theorem calibrate_work_admitted (j cap : ℕ) (hcap : Recipe.budget.need j ≤ cap) :
    (calibrate (degree j) (degree_pos j)).work ≤ 200 * (cap + 1) ^ 2 := by
  obtain ⟨hk, hH, hB, he, _, hp, _, _, _⟩ := admitted_scalar_bounds j cap hcap
  have ht := admitted_sweepCount j cap hcap
  have hm := moment_work (degree j) (pathHeight (degree j)) cap hH he hp
  have hs := sweeps_work (degree j) cap (degree_pos j) hk hH hB he hp ht
  simp only [calibrate, StateWork.powTwo_work, StateWork.powTwo_value,
    exponent_work, alphabet_work]
  change 2 * (degree j + 1) + 1 +
    (2 * pathHeight (degree j) + 4 * alphabetExponent (degree j) (pathHeight (degree j)) + 8) +
    (2 * pathHeight (degree j) + 6 * alphabetExponent (degree j) (pathHeight (degree j)) + 10) +
    (moment (degree j) (pathHeight (degree j))).work +
    (sweeps (degree j) (degree_pos j)).work + 2 ≤ _
  nlinarith

end SortingAdversary.Continuous.StageWork
