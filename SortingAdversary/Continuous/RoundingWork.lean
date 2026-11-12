import SortingAdversary.Continuous.StateWork
import SortingAdversary.Continuous.CertificateWork

/-!
# Counted exact dyadic rounding

Integer logarithms use successive integer divisions. Powers use explicit
successive multiplication, so neither large exponentiation nor logarithm is
treated as a constant-time oracle. Quotients, floors and ceilings are scalar
arithmetic operations; their binary charge is supplied by the operand bounds.
-/

namespace SortingAdversary.Continuous.RoundingWork

open Certificates Precision FiniteAveraging SortingAdversary.Optimal

def clogTwo (m : ℕ) : PrimitiveWork.Result ℕ :=
  if h : m ≤ 1 then ⟨0, 1⟩ else
    let previous := clogTwo ((m + 1) / 2)
    ⟨previous.value + 1, previous.work + 4⟩
termination_by m
decreasing_by omega

@[simp] theorem clogTwo_value (m : ℕ) : (clogTwo m).value = Nat.clog 2 m := by
  unfold clogTwo
  split
  · exact (Nat.clog_of_right_le_one ‹m ≤ 1› 2).symm
  · dsimp only
    rw [clogTwo_value ((m + 1) / 2), Nat.clog_of_one_lt (by decide) (by omega : 1 < m)]
    congr 2
termination_by m
decreasing_by omega

theorem clogTwo_work (m : ℕ) : (clogTwo m).work = 4 * Nat.clog 2 m + 1 := by
  unfold clogTwo
  split
  · simp [Nat.clog_of_right_le_one ‹m ≤ 1› 2]
  · dsimp only
    rw [clogTwo_work ((m + 1) / 2), Nat.clog_of_one_lt (by decide) (by omega : 1 < m)]
    have he : m + 2 - 1 = m + 1 := by omega
    rw [he]
    omega
termination_by m
decreasing_by omega

def integerLog (r : ℚ) : PrimitiveWork.Result ℤ :=
  if 1 ≤ r then
    let result := StateWork.logTwo ⌊r⌋₊
    ⟨(result.value : ℤ), result.work + 5⟩
  else
    let result := clogTwo ⌈r⁻¹⌉₊
    ⟨-(result.value : ℤ), result.work + 5⟩

@[simp] theorem integerLog_value (r : ℚ) : (integerLog r).value = Int.log 2 r := by
  simp only [integerLog, Int.log]
  split <;> simp only [StateWork.logTwo_value, clogTwo_value]

theorem integerLog_work_small (r : ℚ) (hr : r < 1) :
    (integerLog r).work = 4 * Nat.clog 2 ⌈r⁻¹⌉₊ + 6 := by
  simp only [integerLog, not_le.mpr hr, ↓reduceIte, clogTwo_work]

def zpowTwo (z : ℤ) : PrimitiveWork.Result ℚ :=
  let power := StateWork.powTwo z.natAbs
  ⟨if 0 ≤ z then (power.value : ℚ) else (power.value : ℚ)⁻¹, power.work + 3⟩

@[simp] theorem zpowTwo_value (z : ℤ) : (zpowTwo z).value = (2 : ℚ) ^ z := by
  cases z with
  | ofNat m => simp [zpowTwo]
  | negSucc m => simp [zpowTwo, zpow_negSucc]

theorem zpowTwo_work (z : ℤ) : (zpowTwo z).work = 2 * z.natAbs + 4 := by
  simp only [zpowTwo, StateWork.powTwo_work]

def roundUp (J : Interval) : PrimitiveWork.Result ℚ :=
  let exponent := integerLog (J.2 - J.1)
  let spacing := zpowTwo exponent.value
  ⟨spacing.value * (⌈J.1 / spacing.value⌉ : ℚ), exponent.work + spacing.work + 8⟩

@[simp] theorem roundUp_value (J : Interval) : (roundUp J).value = Certificates.roundUp J := by
  simp only [roundUp, integerLog_value, zpowTwo_value, Certificates.roundUp, spacing]

theorem roundingExponent_eq_clog {J : Interval} (hJ : J.2 - J.1 < 1) :
    roundingExponent J = Nat.clog 2 ⌈(J.2 - J.1)⁻¹⌉₊ := by
  simp only [roundingExponent, Int.log, not_le.mpr hJ, ↓reduceIte, neg_neg, Int.toNat_natCast]

theorem log_natAbs_eq_roundingExponent {J : Interval} (hJ : J.2 - J.1 < 1) :
    (Int.log 2 (J.2 - J.1)).natAbs = roundingExponent J := by
  rw [roundingExponent_eq_clog hJ]
  simp only [Int.log, not_le.mpr hJ, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]

theorem roundUp_work (J : Interval) (hJ : J.2 - J.1 < 1) :
    (roundUp J).work = 6 * roundingExponent J + 18 := by
  simp only [roundUp, integerLog_work_small _ hJ, zpowTwo_work, integerLog_value,
    log_natAbs_eq_roundingExponent hJ, roundingExponent_eq_clog hJ]
  omega

theorem roundUp_work_grid (J : Interval) (F : ℕ)
    (hg : OnDyadicGrid F J.1 ∧ OnDyadicGrid F J.2)
    (hl : 0 < J.1) (hu : J.2 < 1) (hJ : J.1 < J.2) :
    (roundUp J).work ≤ 6 * F + 18 := by
  have he := roundingExponent_le hg hl hu hJ
  rw [roundUp_work J (by linarith)]
  omega

def middleHalf (l r : ℚ) : PrimitiveWork.Result Interval :=
  let width := (r - l) / 4
  ⟨(l + width, r - width), 4⟩

@[simp] theorem middleHalf_value (l r : ℚ) :
    (middleHalf l r).value = Certificates.middleHalf l r := rfl

def fallback (l r : ℚ) : PrimitiveWork.Result ℚ :=
  let interval := middleHalf l r
  let rounded := roundUp interval.value
  ⟨rounded.value, interval.work + rounded.work⟩

@[simp] theorem fallback_value (l r : ℚ) :
    (fallback l r).value = Certificates.roundUp (Certificates.middleHalf l r) := by
  simp only [fallback, middleHalf_value, roundUp_value]

theorem fallback_work (l r : ℚ) (F : ℕ) (hg : OnDyadicGrid F l ∧ OnDyadicGrid F r)
    (hl : 0 ≤ l) (hu : r ≤ 1) (hlr : l < r) :
    (fallback l r).work ≤ 6 * F + 34 := by
  have hgrid := middleHalf_onGrid hg.1 hg.2
  have hlow : 0 < (Certificates.middleHalf l r).1 := by
    dsimp [Certificates.middleHalf]
    linarith
  have hupp : (Certificates.middleHalf l r).2 < 1 := by
    dsimp [Certificates.middleHalf]
    linarith
  have hwidth : (Certificates.middleHalf l r).1 < (Certificates.middleHalf l r).2 := by
    dsimp [Certificates.middleHalf]
    linarith
  have hw := roundUp_work_grid (Certificates.middleHalf l r) (F + 2) hgrid hlow hupp hwidth
  simp only [fallback, middleHalf, show
    (l + (r - l) / 4, r - (r - l) / 4) = Certificates.middleHalf l r from rfl]
  omega

def chooseAnchor (l r : ℚ) (L : List Interval) : PrimitiveWork.Result ℚ :=
  let central := CertificateWork.centralInterval L
  match central.value with
  | some J =>
    let rounded := roundUp J
    ⟨rounded.value, central.work + rounded.work + 1⟩
  | none =>
    let rounded := fallback l r
    ⟨rounded.value, central.work + rounded.work + 1⟩

@[simp] theorem chooseAnchor_value (l r : ℚ) (L : List Interval) :
    (chooseAnchor l r L).value = Certificates.chooseAnchor l r L := by
  simp only [chooseAnchor, CertificateWork.centralInterval_value, Certificates.chooseAnchor]
  cases Certificates.centralInterval L <;> simp only [roundUp_value, fallback_value,
    Option.getD_some, Option.getD_none]

theorem central_interior {l r : ℚ} {L : List Interval} {J : Interval}
    (hL : ∀ I ∈ L, l < I.2 ∧ I.1 < r)
    (hc : Certificates.centralInterval L = some J) : l < J.1 ∧ J.2 < r := by
  have cert := centralInterval_certificates hc
  have hN := centralInterval_positive hc
  have hleft : 0 < leftCount L J.1 := by omega
  have hright : 0 < rightCount L J.2 := by omega
  obtain ⟨I, hI, hend⟩ := List.countP_pos_iff.mp hleft
  obtain ⟨I', hI', hstart⟩ := List.countP_pos_iff.mp hright
  exact ⟨(hL I hI).1.trans_le (of_decide_eq_true hend),
    (of_decide_eq_true hstart).trans_lt (hL I' hI').2⟩

theorem chooseAnchor_work (l r : ℚ) (L : List Interval) (F G : ℕ)
    (hbound : OnDyadicGrid F l ∧ OnDyadicGrid F r)
    (hlist : ∀ I ∈ L, OnDyadicGrid G I.1 ∧ OnDyadicGrid G I.2)
    (hl : 0 ≤ l) (hu : r ≤ 1) (hlr : l < r)
    (hL : ∀ I ∈ L, l < I.2 ∧ I.1 < r) :
    (chooseAnchor l r L).work ≤ 65 * (L.length + 1) ^ 2 + 6 * (F + G) + 35 := by
  have hc := CertificateWork.centralInterval_work L
  simp only [chooseAnchor]
  split
  · rename_i J hJ
    have he : Certificates.centralInterval L = some J := by simpa using hJ
    have hg := centralInterval_onGrid G hlist he
    have hi := central_interior hL he
    have hw := roundUp_work_grid J G hg (hl.trans_lt hi.1) (hi.2.trans_le hu)
      (centralInterval_inside he).1
    dsimp only
    omega
  · have hw := fallback_work l r F hbound hl hu hlr
    dsimp only
    omega

end SortingAdversary.Continuous.RoundingWork
