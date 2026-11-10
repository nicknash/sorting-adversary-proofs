import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Finset.Interval

/-!
# The continuous paper's single dyadic weight distribution

This is the distribution in `for-humans/sections/lower-bound.tex`, rather than
the dictionary used by the earlier integer-colour construction.  Level `m`
has `2^m` reduced dyadic anchors, each with weight
`k⁻² ((1 - k⁻¹) / 2)^m`.  We prove the total mass, the stopping mass, and the
conversion of the paper's density gain into the logarithmic cost of a move.
-/

namespace SortingAdversary.Continuous

open scoped BigOperators

/-- All logarithms in the continuous manuscript have base two. -/
noncomputable def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

theorem log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

@[simp] theorem log2_one : log2 1 = 0 := by simp [log2]

@[simp] theorem log2_two : log2 2 = 1 := by
  exact div_self (ne_of_gt log_two_pos)

theorem log2_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    log2 x ≤ log2 y :=
  div_le_div_of_nonneg_right (Real.log_le_log hx hxy) log_two_pos.le

theorem log2_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    log2 (x * y) = log2 x + log2 y := by
  simp [log2, Real.log_mul hx hy, add_div]

theorem log2_div {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    log2 (x / y) = log2 x - log2 y := by
  simp [log2, Real.log_div hx hy, sub_div]

theorem log2_pow (x : ℝ) (m : ℕ) : log2 (x ^ m) = m * log2 x := by
  simp [log2, Real.log_pow, mul_div_assoc]

theorem log2_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ log2 x := by
  simpa using log2_mono (by norm_num : (0 : ℝ) < 1) hx

theorem log2_nonpos {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : log2 x ≤ 0 := by
  simpa using log2_mono hx hx1

/-- An anchor in its reduced form `(2 i + 1) / 2^(m+1)`. -/
abbrev DyadicAnchor := Σ m : ℕ, Fin (2 ^ m)

def DyadicAnchor.coordinate (c : DyadicAnchor) : ℚ :=
  (2 * c.2.val + 1 : ℚ) / (2 : ℚ) ^ (c.1 + 1)

theorem DyadicAnchor.coordinate_pos (c : DyadicAnchor) : 0 < c.coordinate := by
  unfold coordinate
  positivity

theorem DyadicAnchor.coordinate_lt_one (c : DyadicAnchor) : c.coordinate < 1 := by
  unfold coordinate
  apply (div_lt_one (by positivity)).mpr
  have hc : (c.2.val : ℚ) < (2 : ℚ) ^ c.1 := by exact_mod_cast c.2.isLt
  rw [pow_succ]
  have hc' : (c.2.val : ℚ) + 1 ≤ (2 : ℚ) ^ c.1 := by
    exact_mod_cast (Nat.succ_le_of_lt c.2.isLt)
  linarith

/-- A level-respecting integer code. Level `m` occupies `[2^m,2^(m+1))`. -/
def DyadicAnchor.index (c : DyadicAnchor) : ℕ := 2 ^ c.1 + c.2.val

theorem DyadicAnchor.index_injective : Function.Injective DyadicAnchor.index := by
  intro c d heq
  have hlevel : c.1 = d.1 := by
    have hcd : c.1 < d.1 → False := by
      intro hlt
      have hp : 2 ^ (c.1 + 1) ≤ 2 ^ d.1 :=
        Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt hlt)
      have hi := c.2.isLt
      simp only [index, pow_succ] at heq hp
      omega
    have hdc : d.1 < c.1 → False := by
      intro hlt
      have hp : 2 ^ (d.1 + 1) ≤ 2 ^ c.1 :=
        Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt hlt)
      have hi := d.2.isLt
      simp only [index, pow_succ] at heq hp
      omega
    exact le_antisymm (le_of_not_gt hdc) (le_of_not_gt hcd)
  obtain ⟨m, i⟩ := c
  obtain ⟨m', j⟩ := d
  dsimp at hlevel
  subst m'
  congr 1
  apply Fin.ext
  simpa [index] using heq

/-- There are fewer than `2^r` distinct anchors at levels below `r`. -/
theorem low_anchor_count (anchors : Finset DyadicAnchor) (r : ℕ) :
    (anchors.filter (fun c => c.1 < r)).card ≤ 2 ^ r - 1 := by
  classical
  have h := Finset.card_le_card_of_injOn
    (s := anchors.filter (fun c => c.1 < r)) (t := Finset.Ico 1 (2 ^ r))
    DyadicAnchor.index (by
      intro c hc
      have hc' := (Finset.mem_filter.mp hc).2
      have hp : 2 ^ (c.1 + 1) ≤ 2 ^ r :=
        Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt hc')
      have hi := c.2.isLt
      have hpos := Nat.two_pow_pos c.1
      simp only [Finset.mem_coe, Finset.mem_Ico, DyadicAnchor.index]
      rw [pow_succ] at hp
      omega)
    DyadicAnchor.index_injective.injOn
  simpa using h

/-- In a batch of `2^k` distinct anchors, at least half have level at least
`k-1`. This is the counting step in the paper's path-repair argument. -/
theorem high_anchor_count {anchors : Finset DyadicAnchor} {k : ℕ}
    (hk : 1 ≤ k) (hcard : anchors.card = 2 ^ k) :
    2 ^ (k - 1) ≤ (anchors.filter (fun c => k - 1 ≤ c.1)).card := by
  have hlow := low_anchor_count anchors (k - 1)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := anchors) (p := fun c => c.1 < k - 1)
  have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ, Nat.mul_comm]
  simp only [not_lt] at hsplit
  rw [hcard, hpow] at hsplit
  omega

/-- The guaranteed probability of stopping at a node. -/
noncomputable def stopMass (k : ℝ) : ℝ := 1 - 1 / k

/-- The weight of each anchor at reduced denominator `2^(m+1)`. -/
noncomputable def anchorWeight (k : ℝ) (m : ℕ) : ℝ :=
  1 / k ^ 2 * (stopMass k / 2) ^ m

theorem stopMass_pos {k : ℝ} (hk : 1 < k) : 0 < stopMass k := by
  unfold stopMass
  have h := (div_lt_one (lt_trans zero_lt_one hk)).mpr hk
  linarith

theorem stopMass_lt_one {k : ℝ} (hk : 0 < k) : stopMass k < 1 := by
  unfold stopMass
  have h : 0 < 1 / k := one_div_pos.mpr hk
  linarith

theorem anchorWeight_pos {k : ℝ} (hk : 1 < k) (m : ℕ) :
    0 < anchorWeight k m := by
  unfold anchorWeight
  exact mul_pos (one_div_pos.mpr (sq_pos_of_pos (lt_trans zero_lt_one hk)))
    (pow_pos (div_pos (stopMass_pos hk) (by norm_num)) _)

theorem level_mass (k : ℝ) (m : ℕ) :
    (2 : ℝ) ^ m * anchorWeight k m = (1 / k ^ 2) * stopMass k ^ m := by
  unfold anchorWeight
  rw [div_pow]
  have hp : (2 : ℝ) ^ m ≠ 0 := by positivity
  field_simp

theorem sum_level_mass (k : ℝ) (m : ℕ) :
    (∑ _ : Fin (2 ^ m), anchorWeight k m) = (1 / k ^ 2) * stopMass k ^ m := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using level_mass k m

/-- The sum over *all* reduced dyadic anchors is exactly `1/k`. -/
theorem anchorWeight_hasSum {k : ℝ} (hk : 1 < k) :
    HasSum (fun m : ℕ => (2 : ℝ) ^ m * anchorWeight k m) (1 / k) := by
  have hgeo := hasSum_geometric_of_lt_one (stopMass_pos hk).le
    (stopMass_lt_one (lt_trans zero_lt_one hk))
  have hscaled := hgeo.mul_left (1 / k ^ 2)
  have htotal : 1 / k ^ 2 * (1 - stopMass k)⁻¹ = 1 / k := by
    unfold stopMass
    field_simp
    ring
  rw [htotal] at hscaled
  simpa only [level_mass] using hscaled

theorem anchorWeight_tsum {k : ℝ} (hk : 1 < k) :
    (∑' m : ℕ, (2 : ℝ) ^ m * anchorWeight k m) = 1 / k :=
  (anchorWeight_hasSum hk).tsum_eq

theorem all_anchors_summable {k : ℝ} (hk : 1 < k) :
    Summable (fun c : DyadicAnchor => anchorWeight k c.1) := by
  apply (summable_sigma_of_nonneg (fun c => (anchorWeight_pos hk c.1).le)).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simp_rw [tsum_fintype, sum_level_mass, ← level_mass]
  exact (anchorWeight_hasSum hk).summable

theorem all_anchors_tsum {k : ℝ} (hk : 1 < k) :
    (∑' c : DyadicAnchor, anchorWeight k c.1) = 1 / k := by
  rw [(all_anchors_summable hk).tsum_sigma]
  simp_rw [tsum_fintype, sum_level_mass, ← level_mass]
  exact anchorWeight_tsum hk

/-- Actual nodes store only finitely many children. Any such set is a
subdistribution, with at least the paper's stopping probability left over. -/
theorem child_mass_le {k : ℝ} (hk : 1 < k) (children : Finset DyadicAnchor) :
    (∑ c ∈ children, anchorWeight k c.1) ≤ 1 / k := by
  simpa only [all_anchors_tsum hk] using
    (Summable.sum_le_tsum children
      (fun c _ => (anchorWeight_pos hk c.1).le) (all_anchors_summable hk))

theorem stopping_mass_lower {k : ℝ} (hk : 1 < k) (children : Finset DyadicAnchor) :
    stopMass k ≤ 1 - ∑ c ∈ children, anchorWeight k c.1 := by
  unfold stopMass
  linarith [child_mass_le hk children]

/-- Any finite collection of complete levels has mass at most `1/k`. -/
theorem finite_level_mass_le {k : ℝ} (hk : 1 < k) (levels : Finset ℕ) :
    (∑ m ∈ levels, (2 : ℝ) ^ m * anchorWeight k m) ≤ 1 / k := by
  simpa only [anchorWeight_tsum hk] using
    (Summable.sum_le_tsum levels
      (fun m _ => mul_nonneg (by positivity) (anchorWeight_pos hk m).le)
      (anchorWeight_hasSum hk).summable)

noncomputable def stopCost (k : ℝ) : ℝ := -log2 (stopMass k)
noncomputable def anchorCost (k : ℝ) (m : ℕ) : ℝ := -log2 (anchorWeight k m)
noncomputable def tariffSlope (k : ℝ) : ℝ := (1 + stopCost k) / stopMass k
noncomputable def tariffIntercept (k : ℝ) : ℝ := 4 * tariffSlope k + 2 * log2 k

theorem stopCost_nonneg {k : ℝ} (hk : 1 < k) : 0 ≤ stopCost k := by
  exact neg_nonneg.mpr (log2_nonpos (stopMass_pos hk)
    (stopMass_lt_one (lt_trans zero_lt_one hk)).le)

/-- Each move's information cost, in the notation of the prefix proof. -/
theorem anchorCost_eq {k : ℝ} (hk : 1 < k) (m : ℕ) :
    anchorCost k m = (1 + stopCost k) * m + 2 * log2 k := by
  have hk0 : k ≠ 0 := ne_of_gt (lt_trans zero_lt_one hk)
  have hs0 : stopMass k ≠ 0 := ne_of_gt (stopMass_pos hk)
  unfold anchorCost anchorWeight stopCost
  rw [log2_mul (one_div_ne_zero (pow_ne_zero _ hk0))
      (pow_ne_zero _ (div_ne_zero hs0 (by norm_num))),
    log2_div (by norm_num) (pow_ne_zero _ hk0), log2_pow,
    log2_pow, log2_div hs0 (by norm_num), log2_one, log2_two]
  ring

theorem tariffSlope_ge_one {k : ℝ} (hk : 1 < k) : 1 ≤ tariffSlope k := by
  unfold tariffSlope
  apply (one_le_div (stopMass_pos hk)).mpr
  have hs := stopMass_lt_one (lt_trans zero_lt_one hk)
  have hd := stopCost_nonneg hk
  linarith

theorem tariffIntercept_nonneg {k : ℝ} (hk : 1 < k) : 0 ≤ tariffIntercept k := by
  unfold tariffIntercept
  have ha := tariffSlope_ge_one hk
  have hl := log2_nonneg hk.le
  positivity

/-- The density tariff `g ≥ (1 - 1/k)m - 4` pays for the new child weight. -/
theorem anchorCost_le_tariff {k g : ℝ} (hk : 1 < k) (m : ℕ)
    (hgain : stopMass k * m - 4 ≤ g) :
    anchorCost k m ≤ tariffSlope k * g + tariffIntercept k := by
  have hs := stopMass_pos hk
  have ha : 0 ≤ tariffSlope k := le_trans (by norm_num) (tariffSlope_ge_one hk)
  have hscaled := mul_le_mul_of_nonneg_left hgain ha
  have hcancel : tariffSlope k * stopMass k = 1 + stopCost k := by
    unfold tariffSlope
    exact div_mul_cancel₀ _ hs.ne'
  rw [anchorCost_eq hk]
  unfold tariffIntercept
  nlinarith

end SortingAdversary.Continuous
