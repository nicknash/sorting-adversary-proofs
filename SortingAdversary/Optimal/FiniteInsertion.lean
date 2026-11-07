import SortingAdversary.Optimal.Insertion
import SortingAdversary.Optimal.LocalError
import SortingAdversary.Optimal.SparseClosure

/-!
# Integer insertion estimates for actual finite weak systems

The integer compression theorem is transferred through an explicit embedding
of finite-palette maps. The order here is the closure of the numerical raw
rows. Retired public comparisons need not be included when their artificial
walls already imply them.
-/

namespace SortingAdversary.Optimal.FiniteInsertion

open WeakMaps WeakMaps.WeakSystem
open LocalCoupling ClockStationarity FiniteProbability
open scoped BigOperators

structure OrderedSystem (n K : ℕ) where
  system : WeakSystem (Fin n) (K + 1)
  closed : system.Closed
  antisymm : ∀ u v, system.edge u v = true → system.edge v u = true → u = v

structure Label {n K : ℕ} (_C : OrderedSystem n K) where
  down : Fin n
  deriving DecidableEq

@[ext] theorem Label.ext {n K : ℕ} {C : OrderedSystem n K} {x y : Label C}
    (h : x.down = y.down) : x = y := by
  cases x
  cases y
  cases h
  rfl

def labelEquiv {n K : ℕ} (C : OrderedSystem n K) : Label C ≃ Fin n where
  toFun := Label.down
  invFun := Label.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

instance {n K : ℕ} (C : OrderedSystem n K) : Fintype (Label C) :=
  Fintype.ofEquiv (Fin n) (labelEquiv C).symm

instance {n K : ℕ} (C : OrderedSystem n K) : PartialOrder (Label C) where
  le x y := C.system.edge x.down y.down = true
  le_refl x := C.closed.refl x.down
  le_trans x y z hxy hyz := C.closed.trans x.down y.down z.down hxy hyz
  le_antisymm x y hxy hyx := Label.ext (C.antisymm x.down y.down hxy hyx)

instance {n K : ℕ} (C : OrderedSystem n K) : DecidableLE (Label C) :=
  fun x y => inferInstanceAs (Decidable (C.system.edge x.down y.down = true))

def intLower {n K : ℕ} (C : OrderedSystem n K) (x : Label C) : ℤ :=
  (C.system.effectiveLower x.down).val

def intUpper {n K : ℕ} (C : OrderedSystem n K) (x : Label C) : ℤ :=
  (C.system.effectiveUpper x.down).val

def colorEmbedding {n K : ℕ} (C : OrderedSystem n K) :
    ColorMap (Fin n) (K + 1) ↪ (Label C → ℤ) where
  toFun f x := (f x.down).val
  inj' := by
    intro f g h
    funext v
    apply Fin.ext
    exact Int.ofNat.inj (congrFun h (Label.mk v))

theorem intLower_monotone {n K : ℕ} (C : OrderedSystem n K) : Monotone (intLower C) := by
  intro x y hxy
  exact Int.ofNat_le.mpr (C.system.effectiveLower_mono C.closed hxy)

theorem intUpper_monotone {n K : ℕ} (C : OrderedSystem n K) : Monotone (intUpper C) := by
  intro x y hxy
  exact Int.ofNat_le.mpr (C.system.effectiveUpper_mono C.closed hxy)

theorem valid_embedding_iff {n K : ℕ} (C : OrderedSystem n K)
    (f : ColorMap (Fin n) (K + 1)) :
    Insertion.Valid (intLower C) (intUpper C) (colorEmbedding C f) ↔ C.system.Valid f := by
  constructor
  · rintro ⟨hw, hr⟩
    constructor
    · intro v
      have hv := hw (Label.mk v)
      have hlo := C.system.lower_le_effectiveLower (C.closed.refl v)
      have hhi := C.system.effectiveUpper_le_upper (C.closed.refl v)
      change ((C.system.effectiveLower v).val : ℤ) ≤ (f v).val ∧
        ((f v).val : ℤ) ≤ (C.system.effectiveUpper v).val at hv
      constructor <;> omega
    · intro u v huv
      have hh := hr (show (Label.mk u : Label C) ≤ Label.mk v from huv)
      change ((f u).val : ℤ) ≤ (f v).val at hh
      exact Int.ofNat_le.mp hh
  · intro hf
    constructor
    · intro x
      have hw := C.system.valid_between_windows f hf x.down
      constructor
      · exact Int.ofNat_le.mpr hw.1
      · exact Int.ofNat_le.mpr hw.2
    · intro x y hxy
      exact Int.ofNat_le.mpr (hf.2 x.down y.down hxy)

/-- Every integer map within the finite windows is the embedding of a unique
finite-palette map, including all unary bounds and raw-order implications. -/
theorem fullMaps_eq_map {n K : ℕ} (C : OrderedSystem n K) :
    Insertion.fullMaps (intLower C) (intUpper C) = C.system.maps.map (colorEmbedding C) := by
  classical
  ext f
  constructor
  · intro hf
    have hv := Insertion.mem_fullMaps.mp hf
    have hnonneg (v : Fin n) : 0 ≤ f (Label.mk v) := by
      have hh := (hv.1 (Label.mk v)).1
      have hl : (0 : ℤ) ≤ (C.system.effectiveLower v).val := Int.natCast_nonneg _
      exact hl.trans hh
    let g : ColorMap (Fin n) (K + 1) := fun v =>
      ⟨(f (Label.mk v)).toNat, by
        have hh := (hv.1 (Label.mk v)).2
        have hu := (C.system.effectiveUpper v).isLt
        change f (Label.mk v) ≤ ((C.system.effectiveUpper v).val : ℤ) at hh
        omega⟩
    have heq : colorEmbedding C g = f := by
      funext x
      exact Int.toNat_of_nonneg (hnonneg x.down)
    have hg : C.system.Valid g := (valid_embedding_iff C g).mp (heq.symm ▸ hv)
    exact Finset.mem_map.mpr ⟨g, (mem_maps _ _).mpr hg, heq⟩
  · intro hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hf
    exact Insertion.mem_fullMaps.mpr ((valid_embedding_iff C g).mpr ((mem_maps _ _).mp hg))

theorem fullMaps_card {n K : ℕ} (C : OrderedSystem n K) :
    (Insertion.fullMaps (intLower C) (intUpper C)).card = C.system.count := by
  rw [fullMaps_eq_map, Finset.card_map]
  rfl

def comparableCount {n K : ℕ} (C : OrderedSystem n K) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun x => x ≠ v ∧
    (C.system.edge x v = true ∨ C.system.edge v x = true))).card

theorem comparable_card {n K : ℕ} (C : OrderedSystem n K) (v : Fin n) :
    Fintype.card (Insertion.ComparableTo (Label.mk v : Label C)) = comparableCount C v := by
  let e : Insertion.ComparableTo (Label.mk v : Label C) ≃
      {x : Fin n // x ≠ v ∧ (C.system.edge x v = true ∨ C.system.edge v x = true)} :=
    Equiv.subtypeEquiv (labelEquiv C) (by
      intro x
      cases x with
      | mk u =>
        change ((Label.mk u : Label C) ≠ Label.mk v ∧
          (C.system.edge u v = true ∨ C.system.edge v u = true)) ↔ _
        simp only [ne_eq, Label.mk.injEq]
        rfl)
  simpa [comparableCount, Fintype.card_subtype] using Fintype.card_congr e

def windowWidth {n K : ℕ} (C : OrderedSystem n K) (v : Fin n) : ℕ :=
  (C.system.effectiveUpper v).val + 1 - (C.system.effectiveLower v).val

theorem int_width {n K : ℕ} (C : OrderedSystem n K) (v : Fin n) :
    (intUpper C (Label.mk v) - intLower C (Label.mk v) + 1).toNat = windowWidth C v := by
  change (((C.system.effectiveUpper v).val : ℤ) - (C.system.effectiveLower v).val + 1).toNat = _
  unfold windowWidth
  omega

def nearMaps {n K : ℕ} (S : WeakSystem (Fin n) (K + 1))
    (x y : Fin n) (z : ℕ) : Finset (ColorMap (Fin n) (K + 1)) :=
  S.maps.filter (fun f => |((f x).val : ℤ) - (f y).val| ≤ (z : ℤ))

theorem nearMaps_card {n K : ℕ} (C : OrderedSystem n K) (x y : Fin n) (z : ℕ) :
    (Insertion.nearMaps (Label.mk x : Label C) (Label.mk y)
      (intLower C) (intUpper C) z).card = (nearMaps C.system x y z).card := by
  rw [Insertion.nearMaps, fullMaps_eq_map, Finset.filter_map, Finset.card_map]
  rfl

theorem near_count_bound {n K : ℕ} (C : OrderedSystem n K)
    (hne : ∃ f, C.system.Valid f) {x y : Fin n} (hxy : y ≠ x) (z : ℕ) :
    (nearMaps C.system x y z).card * windowWidth C x ≤
      2 * 4 ^ comparableCount C x * (2 * z + 1) * C.system.count := by
  have hw := (C.system.feasible_iff_windows C.closed).mp hne x
  have hz := Insertion.near_count_mul_width_le
    (v := (Label.mk x : Label C)) (w := Label.mk y) (by simpa using hxy)
    (intLower_monotone C) (intUpper_monotone C) (by exact Int.ofNat_le.mpr hw) z
  simpa only [nearMaps_card, int_width, comparable_card, fullMaps_card] using hz

theorem nearProbability_eq_count {n K : ℕ} (S : WeakSystem (Fin n) (K + 1))
    (x y : Fin n) (z : ℚ) :
    LocalError.nearProbability S x y z =
      ((S.maps.filter (fun f => |((f x).val : ℚ) - (f y).val| ≤ z)).card : ℚ) / S.count := by
  unfold LocalError.nearProbability probability mean indicator
  rw [sum_states S (fun f => if |((f x).val : ℚ) - (f y).val| ≤ z then 1 else 0), card_states]
  simp [count]

theorem rational_near_iff_integer (a b : ℕ) {z : ℚ} (hz : 0 ≤ z) :
    |(a : ℚ) - b| ≤ z ↔ |(a : ℤ) - b| ≤ (⌊z⌋.toNat : ℤ) := by
  rw [Int.toNat_of_nonneg (Int.floor_nonneg.mpr hz), Int.le_floor]
  simp only [Int.cast_abs, Int.cast_sub, Int.cast_natCast]

theorem windowWidth_pos {n K : ℕ} (C : OrderedSystem n K)
    (hne : ∃ f, C.system.Valid f) (x : Fin n) : 0 < windowWidth C x := by
  have h := (C.system.feasible_iff_windows C.closed).mp hne x
  unfold windowWidth
  omega

/-- The manuscript's near-tie bound, now for the exact finite weak-map law
used by the constructed coupling. Rational radii introduce no extra loss. -/
theorem near_probability_bound {n K : ℕ} (C : OrderedSystem n K)
    (hcount : 0 < C.system.count) {x y : Fin n} (hxy : y ≠ x)
    (z : ℚ) (hz : 0 ≤ z) :
    LocalError.nearProbability C.system x y z ≤
      (2 * 4 ^ comparableCount C x : ℚ) * (2 * z + 1) / windowWidth C x := by
  have hne := C.system.count_pos_iff.mp hcount
  have hw : (0 : ℚ) < windowWidth C x := by exact_mod_cast windowWidth_pos C hne x
  have hc : (0 : ℚ) < C.system.count := by exact_mod_cast hcount
  let zN : ℕ := ⌊z⌋.toNat
  have hfloor : 0 ≤ ⌊z⌋ := Int.floor_nonneg.mpr hz
  have hzN : (zN : ℚ) ≤ z := by
    have hh := Int.floor_le z
    rw [← Int.toNat_of_nonneg hfloor] at hh
    simpa only [Int.cast_natCast] using hh
  have hcard := near_count_bound C hne hxy zN
  have hcard' : ((nearMaps C.system x y zN).card : ℚ) * windowWidth C x ≤
      (2 * 4 ^ comparableCount C x : ℚ) * (2 * zN + 1) * C.system.count := by
    exact_mod_cast hcard
  rw [nearProbability_eq_count]
  simp_rw [rational_near_iff_integer _ _ hz]
  change ((nearMaps C.system x y zN).card : ℚ) / C.system.count ≤ _
  calc
    _ ≤ (2 * 4 ^ comparableCount C x : ℚ) * (2 * zN + 1) / windowWidth C x :=
      (div_le_div_iff₀ hc hw).mpr hcard'
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hw.le

/-- A coordinate event in the genuine finite-palette model, specified by an
arbitrary finite set of integer values. -/
def restrictedMaps {n K : ℕ} (S : WeakSystem (Fin n) (K + 1))
    (x : Fin n) (A : Finset ℤ) : Finset (ColorMap (Fin n) (K + 1)) :=
  S.maps.filter (fun f => ((f x).val : ℤ) ∈ A)

theorem restricted_count_bound {n K : ℕ} (C : OrderedSystem n K)
    (hne : ∃ f, C.system.Valid f) (x : Fin n) (A : Finset ℤ) :
    (restrictedMaps C.system x A).card * windowWidth C x ≤
      2 * 4 ^ comparableCount C x * A.card * C.system.count := by
  have hw := (C.system.feasible_iff_windows C.closed).mp hne x
  have h := Insertion.restricted_count_mul_width_le
    (v := (Label.mk x : Label C)) (intLower_monotone C) (intUpper_monotone C)
    (Int.ofNat_le.mpr hw) A
  rw [fullMaps_eq_map, Finset.filter_map, Finset.card_map] at h
  have heq : C.system.maps.filter
      ((fun f : Label C → ℤ => f (Label.mk x) ∈ A) ∘ colorEmbedding C) =
      restrictedMaps C.system x A := by
    ext f
    simp only [Finset.mem_filter, restrictedMaps]
    rfl
  rw [heq, Finset.card_map] at h
  simpa only [int_width, comparable_card, count] using h

/-- Every central colour has the insertion lemma's explicit point-mass lower
bound, expressed without division for use in promotion certificates. -/
theorem central_fiber_count {n K : ℕ} (C : OrderedSystem n K)
    (hne : ∃ f, C.system.Valid f) (x : Fin n) (c : Fin (K + 1))
    (hc : (c.val : ℤ) ∈ Insertion.centralColors
      (intLower C (Label.mk x)) (intUpper C (Label.mk x))) :
    C.system.count ≤ windowWidth C x * 4 ^ comparableCount C x *
      (C.system.maps.filter (fun f => f x = c)).card := by
  have hw := (C.system.feasible_iff_windows C.closed).mp hne x
  have h := Insertion.full_count_le_central_fiber_mul
    (v := (Label.mk x : Label C)) (intLower_monotone C) (intUpper_monotone C)
    (Int.ofNat_le.mpr hw) hc
  rw [fullMaps_eq_map, Finset.filter_map, Finset.card_map, Finset.card_map] at h
  have heq : (C.system.maps.filter (fun f => colorEmbedding C f (Label.mk x) = (c.val : ℤ))) =
      C.system.maps.filter (fun f => f x = c) := by
    ext f
    simp only [Finset.mem_filter]
    change (f ∈ C.system.maps ∧ ((f x).val : ℤ) = (c.val : ℤ)) ↔
      (f ∈ C.system.maps ∧ f x = c)
    simp only [Int.natCast_inj, Fin.val_inj]
  change C.system.count ≤
    (intUpper C (Label.mk x) - intLower C (Label.mk x) + 1).toNat *
      4 ^ Fintype.card (Insertion.ComparableTo (Label.mk x : Label C)) *
      (C.system.maps.filter (fun f => colorEmbedding C f (Label.mk x) = (c.val : ℤ))).card at h
  simpa only [heq, int_width, comparable_card] using h

/-- Probability that a coordinate lies near a fixed integer threshold. -/
def thresholdNearProbability {n K : ℕ} (S : WeakSystem (Fin n) (K + 1))
    (x : Fin n) (c : ℕ) (z : ℚ) : ℚ :=
  probability (fun f : SystematicCoupling.State S => |((f.val x).val : ℚ) - c| ≤ z)

theorem thresholdNearProbability_eq_count {n K : ℕ}
    (S : WeakSystem (Fin n) (K + 1)) (x : Fin n) (c : ℕ) (z : ℚ) :
    thresholdNearProbability S x c z =
      ((S.maps.filter (fun f => |((f x).val : ℚ) - c| ≤ z)).card : ℚ) / S.count := by
  unfold thresholdNearProbability probability mean indicator
  rw [sum_states S (fun f => if |((f x).val : ℚ) - c| ≤ z then 1 else 0), card_states]
  simp [count]

/-- Fixed-threshold near events satisfy the same estimate as near ties.
This supplies the error term for the local cumulative-probability oracle. -/
theorem threshold_near_probability_bound {n K : ℕ} (C : OrderedSystem n K)
    (hcount : 0 < C.system.count) (x : Fin n) (c : ℕ) (z : ℚ) (hz : 0 ≤ z) :
    thresholdNearProbability C.system x c z ≤
      (2 * 4 ^ comparableCount C x : ℚ) * (2 * z + 1) / windowWidth C x := by
  have hne := C.system.count_pos_iff.mp hcount
  have hw : (0 : ℚ) < windowWidth C x := by exact_mod_cast windowWidth_pos C hne x
  have hc : (0 : ℚ) < C.system.count := by exact_mod_cast hcount
  let zN : ℕ := ⌊z⌋.toNat
  let A : Finset ℤ := Finset.Icc ((c : ℤ) - zN) ((c : ℤ) + zN)
  have hfloor : 0 ≤ ⌊z⌋ := Int.floor_nonneg.mpr hz
  have hzN : (zN : ℚ) ≤ z := by
    have hh := Int.floor_le z
    rw [← Int.toNat_of_nonneg hfloor] at hh
    simpa only [Int.cast_natCast] using hh
  have hA : A.card = 2 * zN + 1 := by
    simp only [A, Int.card_Icc]
    omega
  have hevent (f : ColorMap (Fin n) (K + 1)) :
      |((f x).val : ℚ) - c| ≤ z ↔ ((f x).val : ℤ) ∈ A := by
    rw [rational_near_iff_integer _ _ hz]
    simp only [A, Finset.mem_Icc, abs_le]
    omega
  have hcard := restricted_count_bound C hne x A
  rw [hA] at hcard
  have hcard' : ((restrictedMaps C.system x A).card : ℚ) * windowWidth C x ≤
      (2 * 4 ^ comparableCount C x : ℚ) * (2 * zN + 1) * C.system.count := by
    exact_mod_cast hcard
  rw [thresholdNearProbability_eq_count]
  simp_rw [hevent]
  change ((restrictedMaps C.system x A).card : ℚ) / C.system.count ≤ _
  calc
    _ ≤ (2 * 4 ^ comparableCount C x : ℚ) * (2 * zN + 1) / windowWidth C x :=
      (div_le_div_iff₀ hc hw).mpr hcard'
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hw.le

/-- Systems with exactly the same represented assignments have the same
near-tie probabilities, even when their sparse row representations differ. -/
theorem nearProbability_congr {n K : ℕ} {S T : WeakSystem (Fin n) (K + 1)}
    (h : ∀ f, S.Valid f ↔ T.Valid f) (x y : Fin n) (z : ℚ) :
    LocalError.nearProbability S x y z = LocalError.nearProbability T x y z := by
  have hm : S.maps = T.maps := by ext f; simp [h f]
  rw [nearProbability_eq_count, nearProbability_eq_count]
  simp only [count, hm]

theorem nearProbability_close {n K : ℕ} (S : WeakSystem (Fin n) (K + 1))
    (x y : Fin n) (z : ℚ) :
    LocalError.nearProbability (SparseClosure.closeSystem S) x y z =
      LocalError.nearProbability S x y z :=
  nearProbability_congr (SparseClosure.closeSystem_valid S) x y z

theorem nearProbability_propagate {n K : ℕ} (S : WeakSystem (Fin n) (K + 1))
    (x y : Fin n) (z : ℚ) :
    LocalError.nearProbability (SparseClosure.propagateSystem S) x y z =
      LocalError.nearProbability S x y z :=
  nearProbability_congr (SparseClosure.propagateSystem_valid S) x y z

end SortingAdversary.Optimal.FiniteInsertion
