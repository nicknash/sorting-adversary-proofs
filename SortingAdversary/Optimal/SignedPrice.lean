import SortingAdversary.Optimal.DyadicDictionary
import SortingAdversary.Optimal.GroupEntropy

/-!
# Signed dyadic promotion prices

This file proves the analytic step between the finite hub dictionary and the
global entropy estimate. The daughter factorial is deducted before summing
prices. Negative surrogate prices are then discarded; only on the remaining
support do we infer that a dyadic deficit is bounded by a logarithmic size
ratio. This order prevents a repeated linear charge at nodes with many cheap
admissions.

All logarithms are natural. The dictionaries and their subprobability mass
are the explicit finite objects of `DyadicDictionary`, not assumptions of the
price theorem.
-/

namespace SortingAdversary.Optimal.SignedPrice

open scoped BigOperators
open DyadicDictionary

/-- Actual upper pin price after deducting the daughter factorial. -/
noncomputable def factorialDebit {M : ℕ} (A : ℝ) (slot : HubSlot M) (k : ℕ) : ℝ :=
  (k : ℝ) * Real.log (A * blockSize slot * (slot.1.val + 2 : ℝ)) -
    Real.log (k.factorial : ℝ)

/-- The elementary factorial estimate replaces the signed debit by this
surrogate, absorbing the factor `exp 1` into the absolute coefficient. -/
noncomputable def surrogate {M : ℕ} (A : ℝ) (slot : HubSlot M) (k : ℕ) : ℝ :=
  (k : ℝ) * Real.log (A * blockSize slot * (slot.1.val + 2 : ℝ) / k)

theorem factorialDebit_le_surrogate {M : ℕ} (A : ℝ) (hA : 0 < A)
    (slot : HubSlot M) (k : ℕ) :
    factorialDebit A slot k ≤ surrogate (Real.exp 1 * A) slot k := by
  by_cases hk : k = 0
  · simp [hk, factorialDebit, surrogate]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hb : (0 : ℝ) < blockSize slot := by simp [blockSize]
  have hp : 0 < A * blockSize slot * (slot.1.val + 2 : ℝ) := by positivity
  have hfactorial := Accounting.log_factorial_lower_bound k
  unfold factorialDebit surrogate
  rw [show Real.exp 1 * A * blockSize slot * (slot.1.val + 2 : ℝ) / k =
      Real.exp 1 * (A * blockSize slot * (slot.1.val + 2 : ℝ)) / k by ring,
    Real.log_div (mul_pos (Real.exp_pos 1) hp).ne' hkpos.ne',
    Real.log_mul (Real.exp_pos 1).ne' hp.ne', Real.log_exp]
  nlinarith

/-- A positive dyadic price bounds its deficit. The constant is explicit
and independent of the controller's degree, path, width, and scale parameters.
The proof uses the tangent inequality for `log ((d+2)/4)`.
-/
theorem deficit_le_log_ratio {M : ℕ} (A k : ℝ) (hA : 0 < A) (hk : 0 < k)
    (slot : HubSlot M)
    (hsmall : k ≤ A * blockSize slot * (slot.1.val + 2 : ℝ)) :
    (slot.1.val : ℝ) ≤ 4 * Real.log ((2 : ℝ) ^ M / k) + 4 * Real.log (4 * A) := by
  have hb : (0 : ℝ) < blockSize slot := by simp [blockSize]
  have hd : (0 : ℝ) < slot.1.val + 2 := by positivity
  have hcap : (blockSize slot : ℝ) * (2 : ℝ) ^ slot.1.val = (2 : ℝ) ^ M := by
    exact_mod_cast blockSize_mul_pow_deficit slot
  have hlogcap := congrArg Real.log hcap
  rw [Real.log_mul hb.ne' (by positivity), Real.log_pow, Real.log_pow] at hlogcap
  have hlog := Real.log_le_log hk hsmall
  rw [Real.log_mul (mul_pos hA hb).ne' hd.ne', Real.log_mul hA.ne' hb.ne'] at hlog
  have htangent := Real.log_le_sub_one_of_pos (show 0 < (slot.1.val + 2 : ℝ) / 4 by positivity)
  rw [Real.log_div hd.ne' (by norm_num : (4 : ℝ) ≠ 0)] at htangent
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hdlog := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg slot.1.val)
  rw [Real.log_div (by positivity) hk.ne', Real.log_pow,
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hA.ne']
  nlinarith

theorem positive_surrogate_properties {M : ℕ} (A : ℝ) (hA : 0 < A)
    (slot : HubSlot M) (k : ℕ) (hpositive : 0 < surrogate A slot k) :
    0 < k ∧ (slot.1.val : ℝ) ≤
      4 * Real.log ((2 : ℝ) ^ M / k) + 4 * Real.log (4 * A) := by
  have hk : 0 < k := by
    by_contra h
    have hz : k = 0 := by omega
    simp [surrogate, hz] at hpositive
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hb : (0 : ℝ) < blockSize slot := by simp [blockSize]
  have hlog : 0 < Real.log (A * blockSize slot * (slot.1.val + 2 : ℝ) / k) := by
    unfold surrogate at hpositive
    exact (mul_pos_iff_of_pos_left hkpos).mp hpositive
  have hratio := (Real.log_pos_iff (by positivity)).mp hlog
  have hsmall : (k : ℝ) ≤ A * blockSize slot * (slot.1.val + 2 : ℝ) := by
    have h := (lt_div_iff₀ hkpos).mp hratio
    linarith
  exact ⟨hk, deficit_le_log_ratio A k hA hkpos slot hsmall⟩

/-- Dropping nonpositive summands is an inequality, never an equality of
the signed accounting. -/
theorem sum_le_positive_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ≤ ∑ i ∈ s.filter (fun i => 0 < f i), f i := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i hi
  split_ifs with h
  · rfl
  · exact le_of_not_gt h

/-- The cubic dictionary converts a block price into a code price and four
logarithmic deficit charges: one from the window length and three from the
normalizing code. The capacity is already global across all nodes. -/
theorem surrogate_eq_globalCode {Node : Type*} [Fintype Node] [Nonempty Node]
    {exponent : Node → ℕ} (A : ℝ) (hA : 0 < A)
    (slot : GlobalSlot exponent) (k : ℕ) (hk : 0 < k) :
    surrogate A slot.2 k =
      (k : ℝ) * Real.log (A * totalCapacity exponent * globalCode slot / k) +
        4 * k * Real.log (slot.2.1.val + 2 : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have htotal : (0 : ℝ) < totalCapacity exponent := by
    exact_mod_cast totalCapacity_pos exponent
  have hd : (0 : ℝ) < slot.2.1.val + 2 := by positivity
  have hratio : 0 < A * totalCapacity exponent * globalCode slot / k := by
    exact div_pos (mul_pos (mul_pos hA htotal) (globalCode_pos slot)) hkpos
  have hcap : (blockSize slot.2 : ℝ) * (2 : ℝ) ^ slot.2.1.val =
      (2 : ℝ) ^ exponent slot.1 := by
    exact_mod_cast blockSize_mul_pow_deficit slot.2
  have hr : (A * totalCapacity exponent * globalCode slot / k) *
      (slot.2.1.val + 2 : ℝ) ^ 4 =
      A * blockSize slot.2 * (slot.2.1.val + 2 : ℝ) / k := by
    unfold globalCode code
    field_simp [htotal.ne', hkpos.ne', hd.ne']
    rw [← hcap]
    ring
  unfold surrogate
  rw [← hr, Real.log_mul hratio.ne' (pow_pos hd 4).ne', Real.log_pow]
  ring

/-- Full aggregation on the positive support. Unlike a per-node linear
allowance, every term here is multiplied by the retained number of expensive
admissions. `entropy` is an explicit sum of their local size ratios.
-/
theorem positive_surrogate_sum_le {Node Colour : Type*} [Fintype Node]
    [Nonempty Node] [DecidableEq Colour] {exponent : Node → ℕ}
    (s : Finset Colour) (selected : Colour → GlobalSlot exponent)
    (decode : GlobalSlot exponent → Colour) (admissions : Colour → ℕ)
    (A : ℝ) (hA : 0 < A)
    (hdecode : ∀ c ∈ s, decode (selected c) = c)
    (hpositive : ∀ c ∈ s, 0 < surrogate A (selected c).2 (admissions c)) :
    let mass := ∑ c ∈ s, (admissions c : ℝ)
    let entropy := ∑ c ∈ s, (admissions c : ℝ) *
      Real.log ((2 : ℝ) ^ exponent (selected c).1 / admissions c)
    (∑ c ∈ s, surrogate A (selected c).2 (admissions c)) ≤
      mass * Real.log (A * totalCapacity exponent / mass) +
        4 * mass * Real.log (2 + 4 * entropy / mass + 4 * Real.log (4 * A)) := by
  classical
  dsimp only
  by_cases hs : s.Nonempty
  · let mass := ∑ c ∈ s, (admissions c : ℝ)
    let entropy := ∑ c ∈ s, (admissions c : ℝ) *
      Real.log ((2 : ℝ) ^ exponent (selected c).1 / admissions c)
    have hk (c : Colour) (hc : c ∈ s) : 0 < admissions c :=
      (positive_surrogate_properties A hA (selected c).2 (admissions c) (hpositive c hc)).1
    have hkr (c : Colour) (hc : c ∈ s) : (0 : ℝ) < admissions c := by
      exact_mod_cast hk c hc
    have hmass : 0 < mass := Finset.sum_pos hkr hs
    have htotal : (0 : ℝ) < totalCapacity exponent := by
      exact_mod_cast totalCapacity_pos exponent
    have hcoded := Accounting.coded_debit_le s (fun c => (admissions c : ℝ))
      (fun c => globalCode (selected c)) (A * totalCapacity exponent)
      (mul_pos hA htotal) hkr (fun c _ => globalCode_pos (selected c))
      (selected_globalCode_le_one s selected decode hdecode)
    have hjensen := Accounting.weighted_log_le s (fun c => (admissions c : ℝ))
      (fun c => (selected c).2.1.val + 2 : Colour → ℝ) hkr (by intros; positivity)
    have hmoment :
        (∑ c ∈ s, (admissions c : ℝ) * ((selected c).2.1.val + 2 : ℝ)) ≤
          2 * mass + 4 * entropy + 4 * Real.log (4 * A) * mass := by
      have hlocal (c : Colour) (hc : c ∈ s) :
          (admissions c : ℝ) * ((selected c).2.1.val + 2 : ℝ) ≤
            2 * admissions c +
              4 * ((admissions c : ℝ) *
                Real.log ((2 : ℝ) ^ exponent (selected c).1 / admissions c)) +
              4 * Real.log (4 * A) * admissions c := by
        have hd := (positive_surrogate_properties A hA (selected c).2
          (admissions c) (hpositive c hc)).2
        have h := mul_le_mul_of_nonneg_left hd (hkr c hc).le
        nlinarith
      have hsum := Finset.sum_le_sum hlocal
      simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, mass, entropy] using hsum
    have hmomentpos :
        0 < ∑ c ∈ s, (admissions c : ℝ) * ((selected c).2.1.val + 2 : ℝ) :=
      Finset.sum_pos (fun c hc => mul_pos (hkr c hc) (by positivity)) hs
    have havg :
        (∑ c ∈ s, (admissions c : ℝ) * ((selected c).2.1.val + 2 : ℝ)) / mass ≤
          2 + 4 * entropy / mass + 4 * Real.log (4 * A) := by
      calc
        _ ≤ (2 * mass + 4 * entropy + 4 * Real.log (4 * A) * mass) / mass :=
          div_le_div_of_nonneg_right hmoment hmass.le
        _ = _ := by field_simp
    have hlog := Real.log_le_log (div_pos hmomentpos hmass) havg
    have hjensen' :
        (∑ c ∈ s, (admissions c : ℝ) * Real.log ((selected c).2.1.val + 2 : ℝ)) ≤
          mass * Real.log (2 + 4 * entropy / mass + 4 * Real.log (4 * A)) :=
      hjensen.trans (mul_le_mul_of_nonneg_left hlog hmass.le)
    have hsplit :
        (∑ c ∈ s, surrogate A (selected c).2 (admissions c)) =
          (∑ c ∈ s, (admissions c : ℝ) *
            Real.log (A * totalCapacity exponent * globalCode (selected c) / admissions c)) +
          4 * ∑ c ∈ s, (admissions c : ℝ) *
            Real.log ((selected c).2.1.val + 2 : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c hc
      simpa only [mul_assoc] using surrogate_eq_globalCode A hA (selected c) (admissions c) (hk c hc)
    rw [hsplit]
    change _ ≤ mass * Real.log (A * totalCapacity exponent / mass) +
      4 * mass * Real.log (2 + 4 * entropy / mass + 4 * Real.log (4 * A))
    nlinarith
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hempty]

/-- The signed price theorem, including the actual factorial credits and
the justified removal of nonpositive terms. The right hand side is derived
from the finite dictionary, not supplied as an accounting hypothesis.

The retained mass is at most the total number of admissions of this type.
Cheap admissions and the scale surcharge are deliberately accounted for
separately.
-/
theorem factorial_debit_sum_le {Node Colour : Type*} [Fintype Node]
    [Nonempty Node] [DecidableEq Colour] {exponent : Node → ℕ}
    (s : Finset Colour) (selected : Colour → GlobalSlot exponent)
    (decode : GlobalSlot exponent → Colour) (admissions : Colour → ℕ)
    (A : ℝ) (hA : 0 < A)
    (hdecode : ∀ c ∈ s, decode (selected c) = c) :
    let A' := Real.exp 1 * A
    let retained := s.filter (fun c => 0 < surrogate A' (selected c).2 (admissions c))
    let mass := ∑ c ∈ retained, (admissions c : ℝ)
    let entropy := ∑ c ∈ retained, (admissions c : ℝ) *
      Real.log ((2 : ℝ) ^ exponent (selected c).1 / admissions c)
    (∑ c ∈ s, factorialDebit A (selected c).2 (admissions c)) ≤
      mass * Real.log (A' * totalCapacity exponent / mass) +
        4 * mass * Real.log (2 + 4 * entropy / mass + 4 * Real.log (4 * A')) := by
  dsimp only
  calc
    _ ≤ ∑ c ∈ s, surrogate (Real.exp 1 * A) (selected c).2 (admissions c) :=
      Finset.sum_le_sum (fun c _ => factorialDebit_le_surrogate A hA (selected c).2 (admissions c))
    _ ≤ ∑ c ∈ s.filter (fun c => 0 < surrogate (Real.exp 1 * A) (selected c).2 (admissions c)),
        surrogate (Real.exp 1 * A) (selected c).2 (admissions c) := sum_le_positive_sum _ _
    _ ≤ _ := positive_surrogate_sum_le _ selected decode admissions _
      (mul_pos (Real.exp_pos 1) hA)
      (fun c hc => hdecode c (Finset.mem_filter.mp hc).1)
      (fun c hc => (Finset.mem_filter.mp hc).2)

/-- Passing to retained terms never increases their total multiplicity. -/
theorem retained_mass_le {ι : Type*} (s : Finset ι) (admissions : ι → ℕ)
    (keep : ι → Prop) [DecidablePred keep] :
    (∑ i ∈ s.filter keep, (admissions i : ℝ)) ≤ ∑ i ∈ s, (admissions i : ℝ) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _i _ _ => Nat.cast_nonneg _)

/-- Splitting a daughter's admissions into price types costs only one
linear copy of the full multiplicity. The comparison with `K ≤ C*s` is
explicit; choosing the dyadic envelope of the manuscript's `2*s+2` palette
bound gives `C = 8` when `s ≥ 1`.
-/
theorem submultiplicity_entropy_le (k full size K C : ℝ)
    (hk : 0 < k) (hkfull : k ≤ full) (hfullsize : full ≤ size)
    (hK : 0 < K) (_hC : 0 < C) (hcap : K ≤ C * size) :
    k * Real.log (K / k) ≤
      full * Real.log (size / full) + full + k * Real.log C := by
  have hfull : 0 < full := hk.trans_le hkfull
  have hsize : 0 < size := hfull.trans_le hfullsize
  have hsplit : Real.log (K / k) =
      Real.log (K / size) + Real.log (size / full) + Real.log (full / k) := by
    rw [Real.log_div hK.ne' hk.ne', Real.log_div hK.ne' hsize.ne',
      Real.log_div hsize.ne' hfull.ne', Real.log_div hfull.ne' hk.ne']
    ring
  have hcap' : K / size ≤ C := (div_le_iff₀ hsize).mpr (by nlinarith [hcap])
  have hlogcap := Real.log_le_log (div_pos hK hsize) hcap'
  have hlogsf : 0 ≤ Real.log (size / full) :=
    Real.log_nonneg ((one_le_div hfull).mpr hfullsize)
  have hfullterm := mul_le_mul_of_nonneg_right hkfull hlogsf
  have htail := Real.log_le_sub_one_of_pos (div_pos hfull hk)
  have htail' := mul_le_mul_of_nonneg_left htail hk.le
  have hcancel : k * (full / k - 1) = full - k := by field_simp
  rw [hcancel] at htail'
  have hhead := mul_le_mul_of_nonneg_left hlogcap hk.le
  rw [hsplit]
  nlinarith

/-- The finite aggregate form needed to combine the type-specific retained
support with the actual tree entropy and promotion incidence budgets. -/
theorem sum_submultiplicity_entropy_le {ι : Type*} (s : Finset ι)
    (k full size K : ι → ℝ) (C : ℝ) (hC : 0 < C)
    (hk : ∀ i ∈ s, 0 < k i) (hkfull : ∀ i ∈ s, k i ≤ full i)
    (hfullsize : ∀ i ∈ s, full i ≤ size i) (hK : ∀ i ∈ s, 0 < K i)
    (hcap : ∀ i ∈ s, K i ≤ C * size i) :
    (∑ i ∈ s, k i * Real.log (K i / k i)) ≤
      (∑ i ∈ s, full i * Real.log (size i / full i)) +
        (∑ i ∈ s, full i) + (∑ i ∈ s, k i) * Real.log C := by
  have h := Finset.sum_le_sum (fun i hi =>
    submultiplicity_entropy_le (k i) (full i) (size i) (K i) C
      (hk i hi) (hkfull i hi) (hfullsize i hi) (hK i hi) hC (hcap i hi))
  simpa only [Finset.sum_add_distrib, ← Finset.sum_mul] using h

/-! ## A single increasing entropy envelope -/

/-- Its value is zero at mass zero, using Lean's total real operations. -/
noncomputable def entropyEnvelope (mass budget : ℝ) : ℝ :=
  mass * Real.log (2 + budget / mass)

theorem entropyEnvelope_nonneg {mass budget : ℝ} (hmass : 0 ≤ mass) (hbudget : 0 ≤ budget) :
    0 ≤ entropyEnvelope mass budget := by
  apply mul_nonneg hmass
  apply Real.log_nonneg
  have h := div_nonneg hbudget hmass
  linarith

/-- Enlarging the available entropy/capacity budget can only enlarge the
envelope. -/
theorem entropyEnvelope_mono_budget {mass budget budget' : ℝ}
    (hmass : 0 ≤ mass) (hbudget : 0 ≤ budget) (h : budget ≤ budget') :
    entropyEnvelope mass budget ≤ entropyEnvelope mass budget' := by
  by_cases hm : mass = 0
  · simp [entropyEnvelope, hm]
  have hmpos : 0 < mass := lt_of_le_of_ne hmass (Ne.symm hm)
  apply mul_le_mul_of_nonneg_left _ hmass
  apply Real.log_le_log
  · have h := div_nonneg hbudget hmass
    linarith
  · exact add_le_add (le_refl 2) (div_le_div_of_nonneg_right h hmass)

/-- Enlarging the admission count also enlarges the envelope. This finite
Jensen proof allows the retained positive mass to be replaced by the complete
number of expensive pins, without silently assuming monotonicity.
-/
theorem entropyEnvelope_mono_mass {mass mass' budget : ℝ}
    (hmass : 0 ≤ mass) (h : mass ≤ mass') (hbudget : 0 ≤ budget) :
    entropyEnvelope mass budget ≤ entropyEnvelope mass' budget := by
  by_cases hm : mass = 0
  · simpa [entropyEnvelope, hm] using entropyEnvelope_nonneg (hm ▸ h) hbudget
  by_cases heq : mass = mass'
  · rw [heq]
  have hmpos : 0 < mass := lt_of_le_of_ne hmass (Ne.symm hm)
  have hm' : 0 < mass' := hmpos.trans_le h
  have hdiff : 0 < mass' - mass := sub_pos.mpr (lt_of_le_of_ne h heq)
  let weight : Fin 2 → ℝ := fun i => if i = 0 then mass else mass' - mass
  let value : Fin 2 → ℝ := fun i => if i = 0 then 2 + budget / mass else 2
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 < weight i := by
    intro i hi
    dsimp [weight]
    split_ifs <;> assumption
  have hv : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 < value i := by
    intro i hi
    dsimp [value]
    split_ifs
    · have h := div_nonneg hbudget hmass
      linarith
    · norm_num
  have hjensen := Accounting.weighted_log_le Finset.univ weight value hw hv
  simp only [Fin.sum_univ_two, weight, value, ite_true, Fin.isValue,
    one_ne_zero, ite_false] at hjensen
  have hweights : mass + (mass' - mass) = mass' := by ring
  rw [hweights] at hjensen
  have havg : (mass * (2 + budget / mass) + (mass' - mass) * 2) / mass' =
      2 + budget / mass' := by field_simp; ring
  rw [havg] at hjensen
  have hextra : 0 ≤ (mass' - mass) * Real.log 2 :=
    mul_nonneg hdiff.le (Real.log_nonneg (by norm_num))
  unfold entropyEnvelope
  linarith

/-- An explicit absolute coefficient. Its argument is the absolute factor
in the individual block price, including the factorial factor `exp 1`. -/
noncomputable def priceCoefficient (A : ℝ) : ℝ :=
  5 + 2 * Real.log A + 8 * Real.log (4 + 2 * Real.log (4 * A))

theorem priceCoefficient_nonneg {A : ℝ} (hA : 1 ≤ A) : 0 ≤ priceCoefficient A := by
  have hlogA := Real.log_nonneg hA
  have hlog4A : 0 ≤ Real.log (4 * A) := Real.log_nonneg (by linarith)
  have hlogD : 0 ≤ Real.log (4 + 2 * Real.log (4 * A)) := Real.log_nonneg (by linarith)
  unfold priceCoefficient
  linarith

/-- The two logarithms obtained from coding and Jensen have the manuscript's
single-envelope form, with an explicit coefficient independent of any node
or controller parameter. -/
theorem coded_bound_le_entropyEnvelope (A mass K entropy : ℝ)
    (hA : 1 ≤ A) (hmass : 0 ≤ mass) (hK : 0 < K) (hentropy : 0 ≤ entropy) :
    mass * Real.log (A * K / mass) +
        4 * mass * Real.log (2 + 4 * entropy / mass + 4 * Real.log (4 * A)) ≤
      priceCoefficient A * entropyEnvelope mass (K + entropy) := by
  by_cases hm : mass = 0
  · simp [hm, entropyEnvelope]
  have hmpos : 0 < mass := lt_of_le_of_ne hmass (Ne.symm hm)
  have hApos : 0 < A := by linarith
  let Z := 2 + (K + entropy) / mass
  let D := 4 + 2 * Real.log (4 * A)
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hlog4A : 0 ≤ Real.log (4 * A) := Real.log_nonneg (by linarith)
  have hD : 0 < D := by dsimp [D]; linarith
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg (by dsimp [D]; linarith)
  have hEm : 0 ≤ entropy / mass := div_nonneg hentropy hmass
  have hKm : 0 < K / mass := div_pos hK hmpos
  have hZ2 : 2 ≤ Z := by
    have h := div_nonneg (show 0 ≤ K + entropy by linarith) hmass
    dsimp [Z]
    linarith
  have hZ : 0 < Z := by linarith
  have hZentropy : 2 + entropy / mass ≤ Z := by
    dsimp [Z]
    exact add_le_add (le_refl 2)
      (div_le_div_of_nonneg_right (by linarith : entropy ≤ K + entropy) hmass)
  have hZK : K / mass ≤ Z := by
    dsimp [Z]
    have h := div_le_div_of_nonneg_right (show K ≤ K + entropy by linarith) hmass
    linarith
  have hfirst : Real.log (A * K / mass) ≤ Real.log A + Real.log Z := by
    rw [← Real.log_mul hApos.ne' hZ.ne']
    apply Real.log_le_log (div_pos (mul_pos hApos hK) hmpos)
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hZK hApos.le
  have hsecondarg : 2 + 4 * entropy / mass + 4 * Real.log (4 * A) ≤ D * Z := by
    have hbase : 2 + 4 * entropy / mass + 4 * Real.log (4 * A) ≤
        D * (2 + entropy / mass) := by
      dsimp [D]
      rw [mul_div_assoc]
      nlinarith [mul_nonneg hlog4A hEm]
    exact hbase.trans (mul_le_mul_of_nonneg_left hZentropy hD.le)
  have hsecond : Real.log (2 + 4 * entropy / mass + 4 * Real.log (4 * A)) ≤
      Real.log D + Real.log Z := by
    rw [← Real.log_mul hD.ne' hZ.ne']
    apply Real.log_le_log _ hsecondarg
    rw [mul_div_assoc]
    nlinarith
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlogZ : (1 / 2 : ℝ) ≤ Real.log Z :=
    hhalf.trans (Real.log_le_log (by norm_num) hZ2)
  have hB : 0 ≤ Real.log A + 4 * Real.log D := by linarith
  have habsorb : Real.log A + 4 * Real.log D ≤
      2 * (Real.log A + 4 * Real.log D) * Real.log Z := by
    nlinarith [mul_le_mul_of_nonneg_left hlogZ hB]
  calc
    _ ≤ mass * (Real.log A + Real.log Z) + 4 * mass * (Real.log D + Real.log Z) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst hmass)
        (mul_le_mul_of_nonneg_left hsecond (by positivity))
    _ = mass * (5 * Real.log Z + (Real.log A + 4 * Real.log D)) := by ring
    _ ≤ mass * ((5 + 2 * (Real.log A + 4 * Real.log D)) * Real.log Z) := by
      apply mul_le_mul_of_nonneg_left _ hmass
      nlinarith
    _ = _ := by unfold priceCoefficient entropyEnvelope; dsimp [Z, D]; ring

theorem admission_entropy_nonneg {M k : ℕ} (hcap : (k : ℝ) ≤ (2 : ℝ) ^ M) :
    0 ≤ (k : ℝ) * Real.log ((2 : ℝ) ^ M / k) := by
  by_cases hk : k = 0
  · simp [hk]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  exact mul_nonneg hkpos.le (Real.log_nonneg ((one_le_div hkpos).mpr hcap))

/-- The manuscript's calibrated signed-price estimate in a concrete finite
form. The only combinatorial data are actual dictionary records, their
decoding to distinct destinations, and the elementary bound that a daughter
cannot receive more labels than its node's birth cap.

The right-hand side uses the full expensive-admission count and the explicit
type entropy. `sum_submultiplicity_entropy_le` then bounds that entropy by
the tree entropy plus linear promotion terms.
-/
theorem full_type_signed_debit_le {Node Colour : Type*} [Fintype Node]
    [Nonempty Node] [DecidableEq Colour] {exponent : Node → ℕ}
    (s : Finset Colour) (selected : Colour → GlobalSlot exponent)
    (decode : GlobalSlot exponent → Colour) (admissions : Colour → ℕ)
    (A : ℝ) (hA : 1 ≤ A)
    (hdecode : ∀ c ∈ s, decode (selected c) = c)
    (hcap : ∀ c ∈ s, (admissions c : ℝ) ≤ (2 : ℝ) ^ exponent (selected c).1) :
    (∑ c ∈ s, factorialDebit A (selected c).2 (admissions c)) ≤
      priceCoefficient (Real.exp 1 * A) *
        entropyEnvelope (∑ c ∈ s, (admissions c : ℝ))
          ((totalCapacity exponent : ℝ) +
            ∑ c ∈ s, (admissions c : ℝ) *
              Real.log ((2 : ℝ) ^ exponent (selected c).1 / admissions c)) := by
  classical
  let A' := Real.exp 1 * A
  let retained := s.filter (fun c => 0 < surrogate A' (selected c).2 (admissions c))
  let mass := ∑ c ∈ retained, (admissions c : ℝ)
  let entropy := ∑ c ∈ retained, (admissions c : ℝ) *
    Real.log ((2 : ℝ) ^ exponent (selected c).1 / admissions c)
  have hApos : 0 < A := by linarith
  have hA' : 1 ≤ A' := by
    have hexp : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
    dsimp [A']
    nlinarith
  have hmass : 0 ≤ mass := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hsubset : retained ⊆ s := Finset.filter_subset _ _
  have hentropy : 0 ≤ entropy :=
    Finset.sum_nonneg (fun c hc => admission_entropy_nonneg (hcap c (hsubset hc)))
  have htotal : (0 : ℝ) < totalCapacity exponent := by
    exact_mod_cast totalCapacity_pos exponent
  have hbase := factorial_debit_sum_le s selected decode admissions A hApos hdecode
  change (∑ c ∈ s, factorialDebit A (selected c).2 (admissions c)) ≤
      mass * Real.log (A' * totalCapacity exponent / mass) +
        4 * mass * Real.log (2 + 4 * entropy / mass + 4 * Real.log (4 * A')) at hbase
  have hmassle : mass ≤ ∑ c ∈ s, (admissions c : ℝ) := retained_mass_le _ _ _
  have hentropyle : entropy ≤ ∑ c ∈ s, (admissions c : ℝ) *
      Real.log ((2 : ℝ) ^ exponent (selected c).1 / admissions c) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun c hc _ => admission_entropy_nonneg (hcap c hc))
  have hbudget :
      0 ≤ (totalCapacity exponent : ℝ) + ∑ c ∈ s, (admissions c : ℝ) *
        Real.log ((2 : ℝ) ^ exponent (selected c).1 / admissions c) := by
    linarith
  have henvelope : entropyEnvelope mass (totalCapacity exponent + entropy) ≤
      entropyEnvelope (∑ c ∈ s, (admissions c : ℝ))
        ((totalCapacity exponent : ℝ) + ∑ c ∈ s, (admissions c : ℝ) *
          Real.log ((2 : ℝ) ^ exponent (selected c).1 / admissions c)) :=
    (entropyEnvelope_mono_budget hmass (by linarith) (by linarith :
      (totalCapacity exponent : ℝ) + entropy ≤ (totalCapacity exponent : ℝ) +
        ∑ c ∈ s, (admissions c : ℝ) *
          Real.log ((2 : ℝ) ^ exponent (selected c).1 / admissions c))).trans
      (entropyEnvelope_mono_mass hmass hmassle hbudget)
  exact hbase.trans ((coded_bound_le_entropyEnvelope A' mass _ entropy hA' hmass htotal hentropy).trans
    (mul_le_mul_of_nonneg_left henvelope (priceCoefficient_nonneg hA')))

theorem entropyEnvelope_eq_mass_ratio (mass budget : ℝ) :
    entropyEnvelope mass budget = mass * Real.log ((2 * mass + budget) / mass) := by
  by_cases hm : mass = 0
  · simp [hm, entropyEnvelope]
  unfold entropyEnvelope
  congr 2
  field_simp

/-- One further finite Jensen inequality combines the ordinary and scale
types (or any finite collection of types) into a single total expensive-pin
count. Zero-admission types are included without a separate convention. -/
theorem sum_entropyEnvelope_le {ι : Type*} (s : Finset ι) (mass budget : ι → ℝ)
    (hmass : ∀ i ∈ s, 0 ≤ mass i) (hbudget : ∀ i ∈ s, 0 ≤ budget i) :
    (∑ i ∈ s, entropyEnvelope (mass i) (budget i)) ≤
      entropyEnvelope (∑ i ∈ s, mass i) (∑ i ∈ s, budget i) := by
  simp_rw [entropyEnvelope_eq_mass_ratio]
  have h := GroupEntropy.log_sum_le_mass_ratio s mass (fun i => 2 * mass i + budget i)
    hmass (fun i hi => by nlinarith [hmass i hi, hbudget i hi])
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using h

end SortingAdversary.Optimal.SignedPrice
