import SortingAdversary.Continuous.SelectionKernelWork
import SortingAdversary.Optimal.RationalBitWork

/-!
# Actual operands in finite enclosure and certificate arithmetic

The endpoints at every update prefix remain in the unit interval on the
proved common dyadic grid. The affine expression has a fixed number of
arithmetic operations, so its temporary rational operands obey a constant
multiple of the same bit bound. Rational reduction is charged using the
existing measured Euclidean implementation, rather than assuming a native
big-integer timing guarantee.
-/

namespace SortingAdversary.Continuous.OperandBounds

open FiniteAveraging Precision Certificates EnclosureWork SortingAdversary.Optimal

def Fits (B : ℕ) (q : ℚ) : Prop := q.num.natAbs.size ≤ B ∧ q.den.size ≤ B

theorem Fits.mono {A B : ℕ} {q : ℚ} (h : Fits A q) (hAB : A ≤ B) : Fits B q :=
  ⟨h.1.trans hAB, h.2.trans hAB⟩

theorem Fits.of_grid {F : ℕ} {q : ℚ} (h : OnDyadicGrid F q) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    Fits (F + 1) q := (rational_bits h h0 h1).symm

theorem size_le_value (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self

theorem fits_natCast (n cap : ℕ) (hn : n ≤ cap) : Fits (cap + 1) (n : ℚ) := by
  constructor
  · simpa only [Rat.num_natCast, Int.natAbs_natCast] using
      (size_le_value n).trans (by omega : n ≤ cap + 1)
  · simp only [Rat.den_natCast, Nat.size_one]
    omega

theorem fits_one {B : ℕ} (hB : 1 ≤ B) : Fits B 1 := by simpa [Fits] using And.intro hB hB

theorem Fits.neg {B : ℕ} {q : ℚ} (h : Fits B q) : Fits B (-q) := by
  simpa only [Fits, Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den, Int.natAbs_neg] using h

theorem Fits.add {A B : ℕ} {q r : ℚ} (hq : Fits A q) (hr : Fits B r) :
    Fits (A + B + 1) (q + r) := by
  dsimp only [Fits] at hq hr
  have h₁ := RationalWork.size_int_mul_le q.num (r.den : ℤ)
  have h₂ := RationalWork.size_int_mul_le r.num (q.den : ℤ)
  simp only [Int.natAbs_natCast] at h₁ h₂
  have hsum := RationalWork.size_int_add_le (q.num * r.den) (r.num * q.den)
  have hprod := RationalWork.size_mul_le q.den r.den
  have hnorm := RationalWork.normalize_sizes (q.num * r.den + r.num * q.den)
    (q.den * r.den) (Nat.mul_ne_zero q.den_nz r.den_nz)
  rw [RationalWork.normalize_value, ← Rat.add_def] at hnorm
  exact ⟨hnorm.1.trans (by omega), hnorm.2.trans (by omega)⟩

theorem Fits.sub {A B : ℕ} {q r : ℚ} (hq : Fits A q) (hr : Fits B r) :
    Fits (A + B + 1) (q - r) := by simpa only [sub_eq_add_neg] using hq.add hr.neg

theorem Fits.mul {A B : ℕ} {q r : ℚ} (hq : Fits A q) (hr : Fits B r) :
    Fits (A + B) (q * r) := by
  dsimp only [Fits] at hq hr
  have hnum := RationalWork.size_int_mul_le q.num r.num
  have hden := RationalWork.size_mul_le q.den r.den
  have hnorm := RationalWork.normalize_sizes (q.num * r.num) (q.den * r.den)
    (Nat.mul_ne_zero q.den_nz r.den_nz)
  rw [RationalWork.normalize_value, ← Rat.mul_def] at hnorm
  exact ⟨hnorm.1.trans (by omega), hnorm.2.trans (by omega)⟩

theorem Fits.inv {B : ℕ} {q : ℚ} (hq : Fits B q) (hB : 1 ≤ B) : Fits B q⁻¹ := by
  constructor
  · have hn : (q⁻¹).num.natAbs ≤ q.den := by
      rw [Rat.num_inv, Int.natAbs_mul, Int.natAbs_natCast]
      have hs : q.num.sign.natAbs ≤ 1 := by
        by_cases h : q.num = 0 <;> simp [h, Int.natAbs_sign_of_ne_zero]
      simpa only [one_mul] using Nat.mul_le_mul_right q.den hs
    exact (Nat.size_le_size hn).trans hq.2
  · rw [Rat.den_inv]
    split
    · simpa only [Nat.size_one] using hB
    · exact hq.1

theorem Fits.div {A B : ℕ} {q r : ℚ} (hq : Fits A q) (hr : Fits B r) (hB : 1 ≤ B) :
    Fits (A + B) (q / r) := by simpa only [div_eq_mul_inv] using hq.mul (hr.inv hB)

theorem Fits.max {B : ℕ} {q r : ℚ} (hq : Fits B q) (hr : Fits B r) : Fits B (max q r) := by
  rcases le_total q r with h | h
  · simpa only [max_eq_right h] using hr
  · simpa only [max_eq_left h] using hq

theorem Fits.ceil {B : ℕ} {q : ℚ} (hq : Fits B q) (hB : 1 ≤ B) : Fits B (⌈q⌉ : ℚ) := by
  constructor
  · have hnum : ⌈q⌉.natAbs ≤ q.num.natAbs := by
      rw [Rat.ceil_def', Int.natAbs_neg]
      simpa only [Int.natAbs_neg] using Int.natAbs_ediv_le_natAbs (-q.num) (q.den : ℤ)
    simpa only [Rat.num_intCast] using (Nat.size_le_size hnum).trans hq.1
  · simpa only [Rat.den_intCast, Nat.size_one] using hB

/-- Every integer cross product passed to rational comparison fits twice
the common input width; no reduced-rational size argument is substituted
for an unreduced temporary. -/
theorem comparison_operands {B : ℕ} {q r : ℚ} (hq : Fits B q) (hr : Fits B r) :
    (q.num * r.den).natAbs.size ≤ 2 * B ∧
      (r.num * q.den).natAbs.size ≤ 2 * B := by
  dsimp only [Fits] at hq hr
  have hl := RationalWork.size_int_mul_le q.num (r.den : ℤ)
  have hr' := RationalWork.size_int_mul_le r.num (q.den : ℤ)
  simp only [Int.natAbs_natCast] at hl hr'
  constructor <;> omega

def digitOperands (S : ℕ) (j : Fin S) (y l u : ℚ) : List ℚ :=
  let a := (S : ℚ) - 1
  let b := a - j.val
  let lower := b * l
  let upper := (j.val : ℚ) * u
  let first := y + lower
  let second := first + upper
  [y, l, u, (S : ℚ), (j.val : ℚ), 1, a, b, lower, upper, first, second, second / S]

theorem digit_operands (S B : ℕ) (j : Fin S) (y l u : ℚ) (hB : 1 ≤ B)
    (hy : Fits B y) (hl : Fits B l) (hu : Fits B u)
    (hS : Fits B (S : ℚ)) (hj : Fits B (j.val : ℚ)) :
    ∀ q ∈ digitOperands S j y l u, Fits (8 * B + 4) q := by
  have h1 := fits_one hB
  have ha := hS.sub h1
  have hb := ha.sub hj
  have hlow := hb.mul hl
  have hupp := hj.mul hu
  have hfirst := hy.add hlow
  have hsecond := hfirst.add hupp
  have hout := hsecond.div hS hB
  simp only [digitOperands, List.forall_mem_cons]
  exact ⟨hy.mono (by omega), hl.mono (by omega), hu.mono (by omega),
    hS.mono (by omega), hj.mono (by omega), h1.mono (by omega), ha.mono (by omega),
    hb.mono (by omega), hlow.mono (by omega), hupp.mono (by omega),
    hfirst.mono (by omega), hsecond.mono (by omega), hout.mono (by omega), by simp⟩

variable {n : ℕ}

theorem fullSteps_feasible (D : System (Fin n) ℚ) (S : ℕ)
    (steps : List (Fin n × Fin S)) (Y : Fin n → ℚ) (hY : D.WeaklyFeasible Y) :
    D.WeaklyFeasible (FiniteAveraging.fullSteps D S steps Y) := by
  induction steps generalizing Y with
  | nil => exact hY
  | cons a steps ih =>
    exact ih _ (update_weaklyFeasible D S a.2 a.1 hY)

/-- The theorem quantifies over every possible update prefix, including
prefixes that occur while a measured endpoint trajectory is being built. -/
theorem prefix_coordinate_bits (D : StoredSystem n) (F s m : ℕ)
    (hD : BoundsOnGrid D.system F) (Y : Vector ℚ n)
    (hYgrid : ∀ x : Fin n, OnDyadicGrid F Y[x]) (hY : D.system.WeaklyFeasible (values Y))
    (hunit : ∀ x, 0 ≤ D.system.lower x ∧ D.system.upper x ≤ 1)
    (steps : List (Fin n × Fin (2 ^ s))) (hlen : steps.length ≤ m) (x : Fin n) :
    Fits (F + s * m + 1) (EnclosureWork.fullSteps D (2 ^ s) steps Y).value[x] := by
  have he := fullSteps_value D (2 ^ s) steps Y
  have hg := fullSteps_onGrid D.system F s steps (values Y) hD hYgrid x
  have hf := fullSteps_feasible D.system (2 ^ s) steps (values Y) hY
  have hb := Fits.of_grid hg ((hunit x).1.trans (hf.1 x).1) ((hf.1 x).2.trans (hunit x).2)
  have hv := congrFun he x
  change Fits (F + s * m + 1) (values (EnclosureWork.fullSteps D (2 ^ s) steps Y).value x)
  rw [hv]
  exact hb.mono (by nlinarith)

theorem conditional_bits (D : StoredSystem n) (G : ℕ) (Y : Vector ℚ n)
    (hD : BoundsOnGrid D.system G) (hYgrid : ∀ x : Fin n, OnDyadicGrid G Y[x])
    (hY : D.system.WeaklyFeasible (values Y))
    (hunit : ∀ x, 0 ≤ D.system.lower x ∧ D.system.upper x ≤ 1) (x : Fin n) :
    Fits (G + 1) (EnclosureWork.conditionalLower D x Y).value ∧
      Fits (G + 1) (EnclosureWork.conditionalUpper D x Y).value := by
  rw [conditionalLower_value, conditionalUpper_value]
  have hm := conditional_mem D.system x hY
  have hy0 := (hunit x).1.trans (hY.1 x).1
  have hy1 := (hY.1 x).2.trans (hunit x).2
  constructor
  · exact Fits.of_grid (conditionalLower_onDyadicGrid D.system x (values Y) G (hD.1 x) hYgrid)
      ((hunit x).1.trans (lower_le_conditionalLower D.system x (values Y))) (hm.1.trans hy1)
  · exact Fits.of_grid (conditionalUpper_onDyadicGrid D.system x (values Y) G (hD.2 x) hYgrid)
      (hy0.trans hm.2) ((conditionalUpper_le_upper D.system x (values Y)).trans (hunit x).2)

theorem fraction_bits (L : List ComparisonIntervals) (cap : ℕ) (hL : L.length ≤ cap) :
    Fits (2 * (cap + 1)) (lowerFraction L) ∧ Fits (2 * (cap + 1)) (upperFraction L) := by
  have hden := fits_natCast L.length cap hL
  have hl := fits_natCast (L.countP separated) cap ((List.countP_le_length).trans hL)
  have hu := fits_natCast (L.countP reverseSeparated) cap ((List.countP_le_length).trans hL)
  constructor
  · simpa only [lowerFraction, two_mul] using hl.div hden (by omega)
  · simpa only [upperFraction, two_mul] using hu.div hden (by omega)

def answerOperands (k : ℕ) (L : List ComparisonIntervals) : List ℚ :=
  [lowerFraction L, upperFraction L, max (lowerFraction L) (upperFraction L),
    (k : ℚ), 100 * (k : ℚ), 1 / 2, 1 / (100 * (k : ℚ)),
    1 / 2 - 1 / (100 * (k : ℚ))]

/-- The exact decision threshold and both rational fractions are covered,
including their intermediate product and reciprocal. -/
theorem answer_operands (k cap : ℕ) (L : List ComparisonIntervals)
    (hk : k ≤ cap) (hL : L.length ≤ cap) :
    ∀ q ∈ answerOperands k L, Fits (200 * (cap + 1)) q := by
  have hf := fraction_bits L cap hL
  have hkfit := fits_natCast k cap hk
  have hc : Fits 101 (100 : ℚ) := by simpa using fits_natCast 100 100 le_rfl
  have hone : Fits 1 (1 : ℚ) := fits_one le_rfl
  have htwo : Fits 3 (2 : ℚ) := by simpa using fits_natCast 2 2 le_rfl
  have hm := hc.mul hkfit
  have hhalf := hone.div htwo (by omega)
  have hi := hone.div hm (by omega)
  have hcut := hhalf.sub hi
  simp only [answerOperands, List.forall_mem_cons]
  exact ⟨hf.1.mono (by omega), hf.2.mono (by omega), (hf.1.max hf.2).mono (by omega),
    hkfit.mono (by omega), hm.mono (by omega), hhalf.mono (by omega), hi.mono (by omega),
    hcut.mono (by omega), by simp⟩

theorem certificate_indices (L : List Interval) (cap : ℕ) (hL : L.length ≤ cap) (J : Interval) :
    (L.length / 4 - 1).size ≤ 3 * cap + 1 ∧
      (3 * L.length / 4 - 1).size ≤ 3 * cap + 1 ∧
      (insideCount L J).size ≤ cap ∧
      (4 * insideCount L J).size ≤ 4 * cap := by
  have hc : insideCount L J ≤ cap := (List.countP_le_length).trans hL
  have hl : L.length / 4 - 1 ≤ L.length := (Nat.sub_le _ _).trans (Nat.div_le_self _ _)
  have hu : 3 * L.length / 4 - 1 ≤ 3 * L.length := (Nat.sub_le _ _).trans (Nat.div_le_self _ _)
  exact ⟨(size_le_value _).trans (by omega), (size_le_value _).trans (by omega),
    (size_le_value _).trans hc, (size_le_value _).trans (by omega)⟩

theorem Fits.natCeil {B : ℕ} {q : ℚ} (hq : Fits B q) (hB : 1 ≤ B) :
    (Nat.ceil q).size ≤ B := by
  have hc := hq.ceil hB
  have ht : (Int.ceil q).toNat ≤ (Int.ceil q).natAbs := by
    cases Int.ceil q <;> simp
  rw [Int.ceil_toNat] at ht
  have hn := (Nat.size_le_size ht).trans hc.1
  simpa only [Rat.num_intCast] using hn

theorem fits_powTwo (r : ℕ) : Fits (r + 1) ((2 : ℚ) ^ r) := by
  have he : (2 : ℚ) ^ r = ((2 ^ r : ℕ) : ℚ) := by norm_cast
  rw [he]
  simp only [Fits, Rat.num_natCast, Int.natAbs_natCast, Rat.den_natCast, Nat.size_pow,
    Nat.size_one, le_refl, true_and]
  omega

def roundingOperands (J : Interval) : List ℚ :=
  [J.1, J.2, J.2 - J.1, (J.2 - J.1)⁻¹, spacing J, J.1 / spacing J,
    (⌈J.1 / spacing J⌉ : ℚ), Certificates.roundUp J]

/-- This includes the reciprocal fed to the logarithm and the ceiling
numerator fed to rounding, as well as the final dyadic point. -/
theorem rounding_operands (J : Interval) (G : ℕ)
    (hg : OnDyadicGrid G J.1 ∧ OnDyadicGrid G J.2)
    (hl : 0 < J.1) (hu : J.2 < 1) (hJ : J.1 < J.2) :
    (Int.log 2 (J.2 - J.1)).natAbs.size ≤ G ∧
      (Nat.ceil (J.2 - J.1)⁻¹).size ≤ 2 * G + 3 ∧
      ∀ q ∈ roundingOperands J, Fits (4 * G + 5) q := by
  have he := roundingExponent_le hg hl hu hJ
  have hsmall : J.2 - J.1 < 1 := by linarith
  have hlfit := Fits.of_grid hg.1 hl.le (by linarith : J.1 ≤ 1)
  have hufit := Fits.of_grid hg.2 (by linarith : 0 ≤ J.2) hu.le
  have hwidth := hufit.sub hlfit
  have hinv := hwidth.inv (by omega)
  have hspace : Fits (G + 1) (spacing J) := by
    rw [spacing_eq_inverse_pow hl hu hJ]
    have hh := (fits_powTwo (roundingExponent J)).inv (by omega)
    simpa only [one_div] using hh.mono (Nat.add_le_add_right he 1)
  have hquot := hlfit.div hspace (by omega)
  have hceil := hquot.ceil (by omega)
  have hout : Fits (3 * G + 3) (Certificates.roundUp J) := by
    exact (hspace.mul hceil).mono (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [RoundingWork.log_natAbs_eq_roundingExponent hsmall]
    exact (size_le_value _).trans he
  · exact (hinv.natCeil (by omega)).trans (by omega)
  · simp only [roundingOperands, List.forall_mem_cons]
    exact ⟨hlfit.mono (by omega), hufit.mono (by omega), hwidth.mono (by omega),
      hinv.mono (by omega), hspace.mono (by omega), hquot.mono (by omega),
      hceil.mono (by omega), hout.mono (by omega), by simp⟩

theorem endpointEntry_bits (D : StoredSystem n) (F s : ℕ) (schedule : List (Fin n))
    (w : Word (2 ^ s) schedule.length) (x : Fin n) (hD : BoundsOnGrid D.system F)
    (hl : D.system.WeaklyFeasible D.system.lower) (hu : D.system.WeaklyFeasible D.system.upper)
    (hunit : ∀ x, 0 ≤ D.system.lower x ∧ D.system.upper x ≤ 1) :
    Fits (F + s * schedule.length + 1) (EnclosureWork.endpoint D (2 ^ s) schedule w x).value.1 ∧
      Fits (F + s * schedule.length + 1) (EnclosureWork.endpoint D (2 ^ s) schedule w x).value.2 := by
  have hlen := Word.assign_length schedule w
  have hleft := prefix_coordinate_bits D F s schedule.length hD D.lower hD.1 hl hunit
    (Word.assign schedule w).value hlen.le x
  have hright := prefix_coordinate_bits D F s schedule.length hD D.upper hD.2 hu hunit
    (Word.assign schedule w).value hlen.le x
  exact ⟨hleft, hright⟩

theorem oneIntervals_bits (D : StoredSystem n) (F s : ℕ) (schedule : List (Fin n))
    (x : Fin n) (hD : BoundsOnGrid D.system F)
    (hl : D.system.WeaklyFeasible D.system.lower) (hu : D.system.WeaklyFeasible D.system.upper)
    (hunit : ∀ x, 0 ≤ D.system.lower x ∧ D.system.upper x ≤ 1) :
    ∀ I ∈ (EnclosureWork.oneIntervals D (2 ^ s) schedule x).value,
      Fits (F + s * schedule.length + 1) I.1 ∧ Fits (F + s * schedule.length + 1) I.2 := by
  intro I hI
  simp only [EnclosureWork.oneIntervals, PrimitiveWork.map_value] at hI
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hI
  exact endpointEntry_bits D F s schedule w x hD hl hu hunit

/-- Binary charge of the measured Euclidean reduction for a raw fraction.
This is the bridge from scalar arithmetic to the repository's explicit
schoolbook model. -/
theorem normalize_bit_charge (num : ℤ) (den B : ℕ) (hd : den ≠ 0)
    (hn : num.natAbs.size ≤ B) (hden : den.size ≤ B) :
    (RationalBitWork.normalize num den hd).bitWork ≤ (6 * B + 8) * (B + 1) ^ 2 := by
  have hc := RationalBitWork.normalize_bitWork_le num den hd B hn hden
  have hw := RationalWork.normalize_work_le num den hd
  rw [RationalBitWork.normalize_result] at hc
  apply hc.trans
  unfold RationalBitWork.Model.charge RationalBitWork.Model.unit
  exact Nat.mul_le_mul_right _ (hw.trans (by omega))

/-- Actual addition is equal to the normalized fraction whose raw integer
operands appear in the bound. The charge includes Euclid and both quotients. -/
theorem add_bit_charge {B : ℕ} {q r : ℚ} (hq : Fits B q) (hr : Fits B r) :
    let num := q.num * r.den + r.num * q.den
    let den := q.den * r.den
    (RationalBitWork.normalize num den (Nat.mul_ne_zero q.den_nz r.den_nz)).result.value = q + r ∧
      (RationalBitWork.normalize num den (Nat.mul_ne_zero q.den_nz r.den_nz)).bitWork ≤
        56 * (B + 1) ^ 3 := by
  dsimp only
  constructor
  · rw [RationalBitWork.normalize_result, RationalWork.normalize_value, ← Rat.add_def]
  · have hc := comparison_operands hq hr
    dsimp only [Fits] at hq hr
    have hs := RationalWork.size_int_add_le (q.num * r.den) (r.num * q.den)
    have hd := RationalWork.size_mul_le q.den r.den
    have hcharge := normalize_bit_charge (q.num * r.den + r.num * q.den) (q.den * r.den)
      (2 * B + 1) (Nat.mul_ne_zero q.den_nz r.den_nz) (by omega) (by omega)
    apply hcharge.trans
    nlinarith [Nat.zero_le (B ^ 2), Nat.zero_le (B ^ 3)]

theorem mul_bit_charge {B : ℕ} {q r : ℚ} (hq : Fits B q) (hr : Fits B r) :
    (RationalBitWork.normalize (q.num * r.num) (q.den * r.den)
      (Nat.mul_ne_zero q.den_nz r.den_nz)).result.value = q * r ∧
      (RationalBitWork.normalize (q.num * r.num) (q.den * r.den)
        (Nat.mul_ne_zero q.den_nz r.den_nz)).bitWork ≤ 56 * (B + 1) ^ 3 := by
  constructor
  · rw [RationalBitWork.normalize_result, RationalWork.normalize_value, ← Rat.mul_def]
  · have hn := RationalWork.size_int_mul_le q.num r.num
    have hd := RationalWork.size_mul_le q.den r.den
    dsimp only [Fits] at hq hr
    have hc := normalize_bit_charge (q.num * r.num) (q.den * r.den) (2 * B + 1)
      (Nat.mul_ne_zero q.den_nz r.den_nz) (by omega) (by omega)
    apply hc.trans
    nlinarith [Nat.zero_le (B ^ 2), Nat.zero_le (B ^ 3)]

def binaryWidth (q r : ℚ) : ℕ :=
  max (max q.num.natAbs.size q.den.size) (max r.num.natAbs.size r.den.size)

theorem binaryWidth_le {B : ℕ} {q r : ℚ} (hq : Fits B q) (hr : Fits B r) :
    binaryWidth q r ≤ B := max_le (max_le hq.1 hq.2) (max_le hr.1 hr.2)

/-- The actual cross products, sum and reduction; the twelve additional
integer operations cover field reads, products, casts and the final pair. -/
def addProfile (q r : ℚ) : RationalBitWork.Profile ℚ :=
  let reduced := RationalBitWork.normalize (q.num * r.den + r.num * q.den) (q.den * r.den)
    (Nat.mul_ne_zero q.den_nz r.den_nz)
  ⟨⟨reduced.result.value, reduced.result.work + 12⟩,
    reduced.bitWork + 12 * RationalBitWork.Model.unit (2 * binaryWidth q r + 1)⟩

@[simp] theorem addProfile_value (q r : ℚ) : (addProfile q r).result.value = q + r := by
  simp only [addProfile, RationalBitWork.normalize_result, RationalWork.normalize_value,
    ← Rat.add_def]

theorem addProfile_bits {B : ℕ} {q r : ℚ} (hq : Fits B q) (hr : Fits B r) :
    (addProfile q r).bitWork ≤ 104 * (B + 1) ^ 3 := by
  have hc := (add_bit_charge hq hr).2
  have hx := Nat.mul_le_mul_left 12 (RationalBitWork.Model.unit_mono
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (binaryWidth_le hq hr)) 1))
  unfold RationalBitWork.Model.unit at hx
  simp only [addProfile, RationalBitWork.Model.unit]
  nlinarith [Nat.zero_le (B ^ 2), Nat.zero_le (B ^ 3)]

def mulProfile (q r : ℚ) : RationalBitWork.Profile ℚ :=
  let reduced := RationalBitWork.normalize (q.num * r.num) (q.den * r.den)
    (Nat.mul_ne_zero q.den_nz r.den_nz)
  ⟨⟨reduced.result.value, reduced.result.work + 12⟩,
    reduced.bitWork + 12 * RationalBitWork.Model.unit (2 * binaryWidth q r + 1)⟩

@[simp] theorem mulProfile_value (q r : ℚ) : (mulProfile q r).result.value = q * r := by
  simp only [mulProfile, RationalBitWork.normalize_result, RationalWork.normalize_value,
    ← Rat.mul_def]

theorem mulProfile_bits {B : ℕ} {q r : ℚ} (hq : Fits B q) (hr : Fits B r) :
    (mulProfile q r).bitWork ≤ 104 * (B + 1) ^ 3 := by
  have hc := (mul_bit_charge hq hr).2
  have hx := Nat.mul_le_mul_left 12 (RationalBitWork.Model.unit_mono
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (binaryWidth_le hq hr)) 1))
  unfold RationalBitWork.Model.unit at hx
  simp only [mulProfile, RationalBitWork.Model.unit]
  nlinarith [Nat.zero_le (B ^ 2), Nat.zero_le (B ^ 3)]

def divProfile (q r : ℚ) : RationalBitWork.Profile ℚ :=
  let multiplied := mulProfile q r⁻¹
  ⟨⟨multiplied.result.value, multiplied.result.work + 8⟩,
    multiplied.bitWork + 8 * RationalBitWork.Model.unit (binaryWidth q r)⟩

@[simp] theorem divProfile_value (q r : ℚ) : (divProfile q r).result.value = q / r := by
  simp only [divProfile, mulProfile_value, div_eq_mul_inv]

theorem divProfile_bits {B : ℕ} {q r : ℚ} (hq : Fits B q) (hr : Fits B r) (hB : 1 ≤ B) :
    (divProfile q r).bitWork ≤ 128 * (B + 1) ^ 3 := by
  have hm := mulProfile_bits hq (hr.inv hB)
  have hx := Nat.mul_le_mul_left 8 (RationalBitWork.Model.unit_mono (binaryWidth_le hq hr))
  unfold RationalBitWork.Model.unit at hx
  simp only [divProfile, RationalBitWork.Model.unit]
  nlinarith [Nat.zero_le (B ^ 2), Nat.zero_le (B ^ 3)]

theorem comparison_bit_charge {B : ℕ} {q r : ℚ} (hq : Fits B q) (hr : Fits B r) :
    (RationalBitWork.lessEqual q r).bitWork ≤ 128 * (B + 1) ^ 3 := by
  have hc := RationalBitWork.lessEqual_bitWork_le q r B hq hr
  apply hc.trans
  nlinarith [Nat.zero_le (B ^ 2), Nat.zero_le (B ^ 3)]

def subProfile (q r : ℚ) : RationalBitWork.Profile ℚ :=
  let added := addProfile q (-r)
  ⟨⟨added.result.value, added.result.work + 4⟩,
    added.bitWork + 4 * RationalBitWork.Model.unit (binaryWidth q r)⟩

@[simp] theorem subProfile_value (q r : ℚ) : (subProfile q r).result.value = q - r := by
  simp only [subProfile, addProfile_value, sub_eq_add_neg]

theorem subProfile_bits {B : ℕ} {q r : ℚ} (hq : Fits B q) (hr : Fits B r) :
    (subProfile q r).bitWork ≤ 128 * (B + 1) ^ 3 := by
  have ha := addProfile_bits hq hr.neg
  have hx := Nat.mul_le_mul_left 4 (RationalBitWork.Model.unit_mono (binaryWidth_le hq hr))
  unfold RationalBitWork.Model.unit at hx
  simp only [subProfile, RationalBitWork.Model.unit]
  nlinarith [Nat.zero_le (B ^ 2), Nat.zero_le (B ^ 3)]

def ceilProfile (q : ℚ) : RationalBitWork.Profile ℤ :=
  ⟨⟨-(-q.num / (q.den : ℤ)), 8⟩,
    8 * RationalBitWork.Model.unit (max q.num.natAbs.size q.den.size)⟩

@[simp] theorem ceilProfile_value (q : ℚ) : (ceilProfile q).result.value = ⌈q⌉ := by
  exact (Rat.ceil_def' q).symm

theorem ceilProfile_bits {B : ℕ} {q : ℚ} (hq : Fits B q) :
    (ceilProfile q).bitWork ≤ 128 * (B + 1) ^ 3 := by
  have hc := Nat.mul_le_mul_left 8 (RationalBitWork.Model.unit_mono (max_le hq.1 hq.2))
  unfold RationalBitWork.Model.unit at hc
  simp only [ceilProfile, RationalBitWork.Model.unit]
  nlinarith [Nat.zero_le (B ^ 2), Nat.zero_le (B ^ 3)]

/-- A min/max fold performs the exact rational comparator and selects one
stored operand. Its extra reads fit the same scalar allowance. -/
theorem minmax_bit_charge {B : ℕ} {q r : ℚ} (hq : Fits B q) (hr : Fits B r) :
    (RationalBitWork.lessEqual q r).bitWork +
      2 * RationalBitWork.Model.unit (binaryWidth q r) ≤ 128 * (B + 1) ^ 3 := by
  have hc := RationalBitWork.lessEqual_bitWork_le q r B hq hr
  have hx := Nat.mul_le_mul_left 2 (RationalBitWork.Model.unit_mono (binaryWidth_le hq hr))
  unfold RationalBitWork.Model.unit at hx ⊢
  nlinarith [Nat.zero_le (B ^ 2), Nat.zero_le (B ^ 3)]

end SortingAdversary.Continuous.OperandBounds
