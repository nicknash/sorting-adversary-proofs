import SortingAdversary.Optimal.WeakMaps
import SortingAdversary.Optimal.ComponentSwap
import SortingAdversary.Optimal.DiscreteCalibration
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Weak-map marginal log-concavity and calibrated intervals

The marginal inequalities in this file are proved from an actual injection
between pairs of weak-map fibres.  The component swap is reconstructed from
unordered coordinate pairs and is therefore reversible.  The integer shift
is justified by the original individual intervals at every coordinate.
-/

namespace SortingAdversary.Optimal.MarginalCalibration

open Finset WeakMaps

variable {α : Type*} [Fintype α] [DecidableEq α] {K : ℕ}

/-- A fibre indexed by a natural number; indices outside the palette have
empty fibres. -/
def levelFiber (S : WeakSystem α K) (v : α) (i : ℕ) : Finset (ColorMap α K) :=
  S.maps.filter (fun f => (f v).val = i)

def levelCount (S : WeakSystem α K) (v : α) (i : ℕ) : ℕ := (levelFiber S v i).card

@[simp] theorem mem_levelFiber (S : WeakSystem α K) (v : α) (i : ℕ)
    (f : ColorMap α K) :
    f ∈ levelFiber S v i ↔ S.Valid f ∧ (f v).val = i := by
  simp [levelFiber]

theorem levelFiber_fin (S : WeakSystem α K) (v : α) (i : Fin K) :
    levelFiber S v i.val = S.fiber v i := by
  ext f
  simp only [mem_levelFiber, WeakSystem.mem_fiber, Fin.ext_iff]

/-- Integer coordinates make the shift by one literal, including near the
bottom of a unary interval. -/
def intMap (f : ColorMap α K) : α → ℤ := fun x => (f x).val

def shifted (f : ColorMap α K) : α → ℤ := fun x => intMap f x - 1

def rowRel (S : WeakSystem α K) (u v : α) : Prop := S.edge u v = true

omit [Fintype α] [DecidableEq α] in
theorem intMap_injective : Function.Injective (intMap : ColorMap α K → α → ℤ) := by
  intro f g h
  funext x
  apply Fin.ext
  have hx := congrFun h x
  exact Int.ofNat_inj.mp hx

omit [Fintype α] [DecidableEq α] in
theorem integer_along {S : WeakSystem α K} {f : ColorMap α K} (hf : S.Valid f) :
    ComponentSwap.Along (rowRel S) (intMap f) := by
  intro u v huv
  exact Int.ofNat_le.mpr (hf.2 u v huv)

omit [Fintype α] [DecidableEq α] in
theorem shifted_along {S : WeakSystem α K} {f : ColorMap α K} (hf : S.Valid f) :
    ComponentSwap.Along (rowRel S) (shifted f) := by
  intro u v huv
  have h := integer_along hf u v huv
  dsimp [shifted]
  omega

omit [Fintype α] [DecidableEq α] in
theorem integer_walls {S : WeakSystem α K} {f : ColorMap α K} (hf : S.Valid f) (x : α) :
    ((S.lower x).val : ℤ) ≤ intMap f x ∧ intMap f x ≤ (S.upper x).val := by
  exact ⟨Int.ofNat_le.mpr (hf.1 x).1, Int.ofNat_le.mpr (hf.1 x).2⟩

omit [Fintype α] [DecidableEq α] in
theorem valid_of_integer_data {S : WeakSystem α K} {f : ColorMap α K} {F : α → ℤ}
    (hF : ∀ x, intMap f x = F x)
    (hw : ∀ x, ((S.lower x).val : ℤ) ≤ F x ∧ F x ≤ (S.upper x).val)
    (ho : ComponentSwap.Along (rowRel S) F) : S.Valid f := by
  constructor
  · intro x
    have h := hw x
    rw [← hF x] at h
    exact ⟨Int.ofNat_le.mp h.1, Int.ofNat_le.mp h.2⟩
  · intro u v huv
    have h := ho u v huv
    rw [← hF u, ← hF v] at h
    exact Int.ofNat_le.mp h

/-- Total conversion used to define a map on all input pairs.  On valid
separated pairs the integer lies inside the palette, so no reduction occurs. -/
def toColor (K : ℕ) (z : ℤ) : Fin (K + 1) :=
  ⟨z.toNat % (K + 1), Nat.mod_lt _ (Nat.succ_pos K)⟩

theorem toColor_val {K : ℕ} {z : ℤ} (hz : 0 ≤ z) (hK : z < (K + 1 : ℕ)) :
    ((toColor K z).val : ℤ) = z := by
  have hn : z.toNat < K + 1 := by omega
  simp only [toColor, Nat.mod_eq_of_lt hn]
  exact Int.toNat_of_nonneg hz

noncomputable def firstInt (S : WeakSystem α K) (v : α) (f g : ColorMap α K) : α → ℤ :=
  ComponentSwap.first (rowRel S) v (intMap f) (shifted g)

noncomputable def secondInt (S : WeakSystem α K) (v : α) (f g : ColorMap α K) : α → ℤ :=
  fun x => ComponentSwap.second (rowRel S) v (intMap f) (shifted g) x + 1

noncomputable def compressPair (S : WeakSystem α (K + 1)) (v : α)
    (p : ColorMap α (K + 1) × ColorMap α (K + 1)) :
    ColorMap α (K + 1) × ColorMap α (K + 1) :=
  (fun x => toColor K (firstInt S v p.1 p.2 x),
    fun x => toColor K (secondInt S v p.1 p.2 x))

omit [Fintype α] [DecidableEq α] in
theorem output_walls {S : WeakSystem α K} {v : α} {f g : ColorMap α K}
    (hf : S.Valid f) (hg : S.Valid g) (hsep : intMap f v < shifted g v) (x : α) :
    (((S.lower x).val : ℤ) ≤ firstInt S v f g x ∧ firstInt S v f g x ≤ (S.upper x).val) ∧
      (((S.lower x).val : ℤ) ≤ secondInt S v f g x ∧ secondInt S v f g x ≤ (S.upper x).val) := by
  apply ComponentSwap.walls_swapped (integer_along hf) (shifted_along hg) hsep
    (integer_walls hf)
  intro y
  have h := integer_walls hg y
  dsimp [shifted]
  omega

omit [Fintype α] [DecidableEq α] in
theorem compressPair_coe {S : WeakSystem α (K + 1)} {v : α}
    {p : ColorMap α (K + 1) × ColorMap α (K + 1)}
    (hf : S.Valid p.1) (hg : S.Valid p.2) (hsep : intMap p.1 v < shifted p.2 v) (x : α) :
    intMap (compressPair S v p).1 x = firstInt S v p.1 p.2 x ∧
      intMap (compressPair S v p).2 x = secondInt S v p.1 p.2 x := by
  have hw := output_walls hf hg hsep x
  have hupper : ((S.upper x).val : ℤ) < (K + 1 : ℕ) := Int.ofNat_lt.mpr (S.upper x).isLt
  have hlower : (0 : ℤ) ≤ (S.lower x).val := Int.natCast_nonneg _
  constructor <;> apply toColor_val <;> omega

omit [Fintype α] [DecidableEq α] in
theorem compressPair_valid {S : WeakSystem α (K + 1)} {v : α}
    {p : ColorMap α (K + 1) × ColorMap α (K + 1)}
    (hf : S.Valid p.1) (hg : S.Valid p.2) (hsep : intMap p.1 v < shifted p.2 v) :
    S.Valid (compressPair S v p).1 ∧ S.Valid (compressPair S v p).2 := by
  have horder := ComponentSwap.along_swapped (root := v) (integer_along hf) (shifted_along hg)
  constructor
  · exact valid_of_integer_data (fun x => (compressPair_coe hf hg hsep x).1)
      (fun x => (output_walls hf hg hsep x).1) horder.1
  · apply valid_of_integer_data (fun x => (compressPair_coe hf hg hsep x).2)
      (fun x => (output_walls hf hg hsep x).2)
    intro u w huw
    have h := horder.2 u w huw
    dsimp [secondInt]
    omega

omit [Fintype α] [DecidableEq α] in
theorem compressPair_recover {S : WeakSystem α (K + 1)} {v : α}
    {p q : ColorMap α (K + 1) × ColorMap α (K + 1)}
    (hpf : S.Valid p.1) (hpg : S.Valid p.2) (hpsep : intMap p.1 v < shifted p.2 v)
    (hqf : S.Valid q.1) (hqg : S.Valid q.2) (hqsep : intMap q.1 v < shifted q.2 v)
    (heq : compressPair S v p = compressPair S v q) : p = q := by
  have hfirst : firstInt S v p.1 p.2 = firstInt S v q.1 q.2 := by
    funext x
    have h := congrArg (fun pair => intMap pair.1 x) heq
    simpa only [(compressPair_coe hpf hpg hpsep x).1,
      (compressPair_coe hqf hqg hqsep x).1] using h
  have hsecond : ComponentSwap.second (rowRel S) v (intMap p.1) (shifted p.2) =
      ComponentSwap.second (rowRel S) v (intMap q.1) (shifted q.2) := by
    funext x
    have h := congrArg (fun pair => intMap pair.2 x) heq
    rw [(compressPair_coe hpf hpg hpsep x).2,
      (compressPair_coe hqf hqg hqsep x).2] at h
    dsimp [secondInt] at h
    omega
  have hrec := ComponentSwap.recover hfirst hsecond
  apply Prod.ext (intMap_injective hrec.1)
  funext x
  apply Fin.ext
  have h := congrFun hrec.2 x
  dsimp [shifted, intMap] at h
  omega

private theorem separated_of_fibres {S : WeakSystem α (K + 1)} {v : α} {a b : ℕ}
    (hab : a < b) {p : ColorMap α (K + 1) × ColorMap α (K + 1)}
    (hp : p ∈ levelFiber S v a ×ˢ levelFiber S v (b + 1)) :
    S.Valid p.1 ∧ S.Valid p.2 ∧ intMap p.1 v < shifted p.2 v := by
  obtain ⟨⟨hf, hfa⟩, ⟨hg, hgb⟩⟩ :=
    (show (S.Valid p.1 ∧ (p.1 v).val = a) ∧
        (S.Valid p.2 ∧ (p.2 v).val = b + 1) from by simpa using hp)
  refine ⟨hf, hg, ?_⟩
  dsimp [intMap, shifted]
  omega

theorem compressPair_mem {S : WeakSystem α (K + 1)} {v : α} {a b : ℕ}
    (hab : a < b) {p : ColorMap α (K + 1) × ColorMap α (K + 1)}
    (hp : p ∈ levelFiber S v a ×ˢ levelFiber S v (b + 1)) :
    compressPair S v p ∈ levelFiber S v b ×ˢ levelFiber S v (a + 1) := by
  obtain ⟨hf, hg, hsep⟩ := separated_of_fibres hab hp
  have hv := compressPair_valid hf hg hsep
  have hc := compressPair_coe hf hg hsep v
  have hfa : (p.1 v).val = a := ((mem_levelFiber _ _ _ _).mp (mem_product.mp hp).1).2
  have hgb : (p.2 v).val = b + 1 := ((mem_levelFiber _ _ _ _).mp (mem_product.mp hp).2).2
  have hleft : ((compressPair S v p).1 v).val = b := by
    have h := hc.1
    simp only [firstInt, ComponentSwap.first_root, shifted, intMap] at h
    omega
  have hright : ((compressPair S v p).2 v).val = a + 1 := by
    have h := hc.2
    simp only [secondInt, ComponentSwap.second_root, intMap] at h
    omega
  simpa only [mem_product, mem_levelFiber] using ⟨⟨hv.1, hleft⟩, ⟨hv.2, hright⟩⟩

/-- A stronger adjacent-ratio inequality: the injection moves the two marked
values one step toward one another, even when they are far apart. -/
theorem levelCount_cross (S : WeakSystem α (K + 1)) (v : α) (a b : ℕ) (hab : a ≤ b) :
    levelCount S v a * levelCount S v (b + 1) ≤
      levelCount S v (a + 1) * levelCount S v b := by
  rcases lt_or_eq_of_le hab with hlt | rfl
  · have hcard : (levelFiber S v a ×ˢ levelFiber S v (b + 1)).card ≤
        (levelFiber S v b ×ˢ levelFiber S v (a + 1)).card := by
      apply Finset.card_le_card_of_injOn (compressPair S v)
      · intro p hp
        exact compressPair_mem hlt hp
      · intro p hp q hq heq
        obtain ⟨hpf, hpg, hpsep⟩ := separated_of_fibres hlt hp
        obtain ⟨hqf, hqg, hqsep⟩ := separated_of_fibres hlt hq
        exact compressPair_recover hpf hpg hpsep hqf hqg hqsep heq
    simpa only [card_product, levelCount, Nat.mul_comm] using hcard
  · exact le_of_eq (Nat.mul_comm _ _)

/-- The actual weak-map marginal count sequence is log-concave. -/
theorem levelCount_logConcave (S : WeakSystem α (K + 1)) (v : α) (i : ℕ) :
    levelCount S v i * levelCount S v (i + 2) ≤ levelCount S v (i + 1) ^ 2 := by
  simpa only [Nat.add_assoc, pow_two] using levelCount_cross S v i (i + 1) (Nat.le_succ i)

/-- Empty palettes are vacuous when a marked label is present. -/
theorem levelCount_cross_any (S : WeakSystem α K) (v : α) (a b : ℕ) (hab : a ≤ b) :
    levelCount S v a * levelCount S v (b + 1) ≤
      levelCount S v (a + 1) * levelCount S v b := by
  cases K with
  | zero => exact Fin.elim0 (S.lower v)
  | succ K => exact levelCount_cross S v a b hab

/-- Exact rational probability of a marked colour in the uniform weak-map
law.  As with the existing local law, an empty family gives zero. -/
def mass (S : WeakSystem α K) (v : α) (i : ℕ) : ℚ :=
  (levelCount S v i : ℚ) / S.count

theorem mass_nonneg (S : WeakSystem α K) (v : α) (i : ℕ) : 0 ≤ mass S v i :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The scalar ratio hypothesis is discharged by the actual fibre injection. -/
theorem mass_ratios (S : WeakSystem α K) (v : α) :
    DiscreteCalibration.DecreasingRatios (mass S v) := by
  intro a b hab
  have h : (levelCount S v a : ℚ) * levelCount S v (b + 1) ≤
      (levelCount S v (a + 1) : ℚ) * levelCount S v b := by
    exact_mod_cast levelCount_cross_any S v a b hab
  simp only [mass, div_mul_div_comm]
  exact div_le_div_of_nonneg_right h (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem mass_logConcave (S : WeakSystem α K) (v : α) (i : ℕ) :
    mass S v i * mass S v (i + 2) ≤ mass S v (i + 1) ^ 2 := by
  simpa only [Nat.add_assoc, pow_two] using mass_ratios S v i (i + 1) (Nat.le_succ i)

/-- The exclusive CDF: the probability that the marked value is `< cut`. -/
def cdf (S : WeakSystem α K) (v : α) (cut : ℕ) : ℚ :=
  DiscreteCalibration.cdf (mass S v) cut

/-- The summed marginal CDF is exactly the relative cardinality of the
corresponding event in the original parent family. -/
theorem cdf_eq_card (S : WeakSystem α K) (v : α) (cut : ℕ) :
    cdf S v cut = ((S.maps.filter (fun f => (f v).val < cut)).card : ℚ) / S.count := by
  have hsum : (∑ i ∈ range cut, levelCount S v i) =
      (S.maps.filter (fun f => (f v).val < cut)).card := by
    simpa only [levelCount, levelFiber, mem_range] using
      (sum_card_fiberwise_eq_card_filter S.maps (range cut) (fun f => (f v).val))
  unfold cdf DiscreteCalibration.cdf mass
  rw [← sum_div]
  have hcast : (∑ i ∈ range cut, (levelCount S v i : ℚ)) =
      ((S.maps.filter (fun f => (f v).val < cut)).card : ℚ) := by
    exact_mod_cast hsum
  rw [hcast]

/-- Inclusive CDF queries from the local oracle use this one-step offset. -/
theorem cdf_inclusive_eq_card (S : WeakSystem α K) (v : α) (i : Fin K) :
    cdf S v (i.val + 1) = ((S.maps.filter (fun f => f v ≤ i)).card : ℚ) / S.count := by
  simpa only [Nat.lt_succ_iff, Fin.le_iff_val_le_val] using cdf_eq_card S v (i.val + 1)

theorem mass_total (S : WeakSystem α K) (v : α) (hS : 0 < S.count) :
    DiscreteCalibration.cdf (mass S v) K = 1 := by
  change cdf S v K = 1
  rw [cdf_eq_card]
  have hfilter : S.maps.filter (fun f => (f v).val < K) = S.maps :=
    filter_true_of_mem (fun f _ => (f v).isLt)
  rw [hfilter]
  change (S.count : ℚ) / S.count = 1
  apply div_self
  exact_mod_cast (Nat.ne_of_gt hS)

/-- The true cumulative law is log-concave, not merely the numerical CDF
reported by a local approximation routine. -/
theorem cdf_logConcave (S : WeakSystem α K) (v : α) (i : ℕ) :
    cdf S v i * cdf S v (i + 2) ≤ cdf S v (i + 1) ^ 2 :=
  DiscreteCalibration.cdf_logConcave (mass_nonneg S v) (mass_ratios S v) i

theorem mass_min_endpoints_le (S : WeakSystem α K) (v : α)
    {a b i : ℕ} (hai : a ≤ i) (hib : i ≤ b) :
    min (mass S v a) (mass S v b) ≤ mass S v i :=
  DiscreteCalibration.min_endpoints_le (mass_nonneg S v) (mass_ratios S v) hai hib

/-- In particular, the support of the actual marginal has no gaps. -/
theorem mass_support_contiguous (S : WeakSystem α K) (v : α)
    {a b i : ℕ} (ha : 0 < mass S v a) (hb : 0 < mass S v b)
    (hai : a ≤ i) (hib : i ≤ b) : 0 < mass S v i :=
  lt_of_lt_of_le (lt_min ha hb) (mass_min_endpoints_le S v hai hib)

/-- Deterministic finite first-crossing selection from a noisy rational CDF.
The mathematical inputs in the hypotheses are proofs and do not enter the
executable threshold search. -/
def selectedInterval (S : WeakSystem α (K + 1)) (v : α) (hS : 0 < S.count)
    (q : Fin (K + 1) → ℚ)
    (herr : ∀ i, |q i - cdf S v (i.val + 1)| ≤ (1 / 16 : ℚ)) :
    Fin (K + 1) × Fin (K + 1) :=
  DiscreteCalibration.quartiles q
    (DiscreteCalibration.top_crosses (mass_total S v hS) q herr)

/-- The manuscript's calibrated true-parent guarantee, with its original
constant.  Log-concavity is proved above from the weak maps, not assumed here.
The statement includes both endpoints and singleton selected intervals. -/
theorem noisy_quartile_calibration (S : WeakSystem α (K + 1)) (v : α) (hS : 0 < S.count)
    (q : Fin (K + 1) → ℚ)
    (herr : ∀ i, |q i - cdf S v (i.val + 1)| ≤ (1 / 16 : ℚ)) :
    let I := selectedInterval S v hS q herr
    I.1 ≤ I.2 ∧ ∀ i : ℕ, I.1.val ≤ i → i ≤ I.2.val →
      1 / (16 * (I.2.val + 1 - I.1.val : ℕ) : ℚ) ≤ mass S v i :=
  DiscreteCalibration.noisy_quartiles (mass_nonneg S v) (mass_ratios S v)
    (mass_total S v hS) q herr

/-- An integer form directly usable in the signed pin/birth accounting:
the selected true fibre loses at most the factor `16m`. -/
theorem selected_fiber_count (S : WeakSystem α (K + 1)) (v : α) (hS : 0 < S.count)
    (q : Fin (K + 1) → ℚ)
    (herr : ∀ i, |q i - cdf S v (i.val + 1)| ≤ (1 / 16 : ℚ))
    (i : ℕ) (hai : (selectedInterval S v hS q herr).1.val ≤ i)
    (hib : i ≤ (selectedInterval S v hS q herr).2.val) :
    S.count ≤ 16 *
      ((selectedInterval S v hS q herr).2.val + 1 - (selectedInterval S v hS q herr).1.val) *
      levelCount S v i := by
  let I := selectedInterval S v hS q herr
  have hcal := noisy_quartile_calibration S v hS q herr
  have hm : (0 : ℚ) < (I.2.val + 1 - I.1.val : ℕ) := by
    have horder : I.1.val ≤ I.2.val := hcal.1
    exact_mod_cast (show 0 < I.2.val + 1 - I.1.val by omega)
  have hn : (0 : ℚ) < S.count := by exact_mod_cast hS
  have h := hcal.2 i hai hib
  change 1 / (16 * (I.2.val + 1 - I.1.val : ℕ) : ℚ) ≤
    (levelCount S v i : ℚ) / S.count at h
  have hmul := (div_le_div_iff₀ (mul_pos (by norm_num : (0 : ℚ) < 16) hm) hn).mp h
  have hcast : (S.count : ℚ) ≤
      16 * (I.2.val + 1 - I.1.val : ℕ) * (levelCount S v i : ℚ) := by nlinarith
  exact_mod_cast hcast

/-- The same guarantee stated with the repository's original parent-fibre API. -/
theorem selected_parent_fiber_count (S : WeakSystem α (K + 1)) (v : α) (hS : 0 < S.count)
    (q : Fin (K + 1) → ℚ)
    (herr : ∀ i, |q i - cdf S v (i.val + 1)| ≤ (1 / 16 : ℚ))
    (i : Fin (K + 1)) (hai : (selectedInterval S v hS q herr).1 ≤ i)
    (hib : i ≤ (selectedInterval S v hS q herr).2) :
    S.count ≤ 16 *
      ((selectedInterval S v hS q herr).2.val + 1 - (selectedInterval S v hS q herr).1.val) *
      (S.fiber v i).card := by
  simpa only [levelCount, levelFiber_fin] using selected_fiber_count S v hS q herr i.val hai hib

end SortingAdversary.Optimal.MarginalCalibration
