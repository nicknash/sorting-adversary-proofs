import SortingAdversary.Optimal.ScaleHubs
import SortingAdversary.Optimal.HubPricing
import SortingAdversary.Optimal.FiniteInsertion
import SortingAdversary.Optimal.MarginalCalibration
import SortingAdversary.Optimal.FiniteRefinement

/-!
# Actual central insertion intervals and selected scale-hub prices

Scale repairs use the explicit central interval from integer insertion. They
do not call the local CDF while their component's width ratio is still large.
The natural endpoints below are executable half-open palette intervals. Their
length and point-mass guarantees feed the existing actual hub selector.
-/

namespace SortingAdversary.Optimal.ScaleMass

open WeakMaps WeakMaps.WeakSystem FiniteInsertion MarginalCalibration
open StableBatches HubSelector BatchWindows ScaleHubs

/-- Inclusive left endpoint of the central insertion interval. -/
def centralLower (L U : ℕ) : ℕ := L + (U - L) / 4

/-- Exclusive right endpoint of that interval. -/
def centralUpper (L U : ℕ) : ℕ := U - (U - L) / 4 + 1

theorem central_bounds {L U : ℕ} (hLU : L ≤ U) :
    L ≤ centralLower L U ∧ centralLower L U < centralUpper L U ∧ centralUpper L U ≤ U + 1 := by
  unfold centralLower centralUpper
  omega

theorem central_length {L U : ℕ} (hLU : L ≤ U) :
    U + 1 - L ≤ 2 * (centralUpper L U - centralLower L U) ∧
      centralUpper L U - centralLower L U ≤ U + 1 - L := by
  unfold centralLower centralUpper
  omega

/-- The natural interval is exactly the integer interval in the insertion
theorem, including both inclusive endpoint corrections. -/
theorem central_integer_iff {L U c : ℕ} (hLU : L ≤ U) :
    (c : ℤ) ∈ Insertion.centralColors (L : ℤ) (U : ℤ) ↔
      centralLower L U ≤ c ∧ c < centralUpper L U := by
  simp only [Insertion.centralColors, Finset.mem_Icc, centralLower, centralUpper]
  omega

theorem midpoint_central {L U : ℕ} (hLU : L ≤ U) :
    centralLower L U ≤ L + (U - L) / 2 ∧ L + (U - L) / 2 < centralUpper L U := by
  unfold centralLower centralUpper
  omega

variable {n K : ℕ}

def intervalLower (C : OrderedSystem n K) (x : Fin n) : ℕ :=
  centralLower (C.system.effectiveLower x).val (C.system.effectiveUpper x).val

def intervalUpper (C : OrderedSystem n K) (x : Fin n) : ℕ :=
  centralUpper (C.system.effectiveLower x).val (C.system.effectiveUpper x).val

theorem effective_bounds (C : OrderedSystem n K) (hne : ∃ f, C.system.Valid f) (x : Fin n) :
    (C.system.effectiveLower x).val ≤ (C.system.effectiveUpper x).val :=
  (C.system.feasible_iff_windows C.closed).mp hne x

theorem interval_bounds (C : OrderedSystem n K) (hne : ∃ f, C.system.Valid f) (x : Fin n) :
    (C.system.effectiveLower x).val ≤ intervalLower C x ∧
      intervalLower C x < intervalUpper C x ∧
      intervalUpper C x ≤ (C.system.effectiveUpper x).val + 1 :=
  central_bounds (effective_bounds C hne x)

theorem interval_upper_le (C : OrderedSystem n K) (hne : ∃ f, C.system.Valid f) (x : Fin n) :
    intervalUpper C x ≤ K + 1 := by
  have h := (interval_bounds C hne x).2.2
  have hK := (C.system.effectiveUpper x).isLt
  omega

theorem interval_length (C : OrderedSystem n K) (hne : ∃ f, C.system.Valid f) (x : Fin n) :
    windowWidth C x ≤ 2 * (intervalUpper C x - intervalLower C x) ∧
      intervalUpper C x - intervalLower C x ≤ windowWidth C x :=
  central_length (effective_bounds C hne x)

theorem interval_large (C : OrderedSystem n K) (hne : ∃ f, C.system.Valid f) (x : Fin n)
    (hwidth : 32 ≤ windowWidth C x) : 8 ≤ intervalUpper C x - intervalLower C x := by
  have h := (interval_length C hne x).1
  omega

theorem interval_integer_iff (C : OrderedSystem n K) (hne : ∃ f, C.system.Valid f)
    (x : Fin n) (c : ℕ) :
    (c : ℤ) ∈ Insertion.centralColors (intLower C (Label.mk x)) (intUpper C (Label.mk x)) ↔
      intervalLower C x ≤ c ∧ c < intervalUpper C x :=
  central_integer_iff (effective_bounds C hne x)

/-- Exact denominator-free central fibre bound for the current finite law. -/
theorem central_count (C : OrderedSystem n K) (hne : ∃ f, C.system.Valid f)
    (x : Fin n) (c : Fin (K + 1))
    (hc : intervalLower C x ≤ c.val ∧ c.val < intervalUpper C x) :
    C.system.count ≤ windowWidth C x * 4 ^ comparableCount C x * (C.system.fiber x c).card := by
  exact central_fiber_count C hne x c ((interval_integer_iff C hne x c.val).mpr hc)

/-- Replace the actual comparable count by a proved structural cap, then
express the denominator in terms of the actual central-window length. -/
theorem central_count_by_length (C : OrderedSystem n K) (hne : ∃ f, C.system.Valid f)
    (x : Fin n) (c : Fin (K + 1)) (B : ℕ) (hB : comparableCount C x ≤ B)
    (hc : intervalLower C x ≤ c.val ∧ c.val < intervalUpper C x) :
    C.system.count ≤ 2 * 4 ^ B * (intervalUpper C x - intervalLower C x) *
      (C.system.fiber x c).card := by
  calc
    _ ≤ windowWidth C x * 4 ^ comparableCount C x * (C.system.fiber x c).card :=
      central_count C hne x c hc
    _ ≤ (2 * (intervalUpper C x - intervalLower C x)) * 4 ^ B *
        (C.system.fiber x c).card :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (interval_length C hne x).1
        (Nat.pow_le_pow_right (by decide : 0 < 4) hB))
    _ = _ := by ring

theorem central_support (C : OrderedSystem n K) (hS : 0 < C.system.count)
    (x : Fin n) (c : Fin (K + 1))
    (hc : intervalLower C x ≤ c.val ∧ c.val < intervalUpper C x) :
    ∃ f, C.system.Valid f ∧ f x = c := by
  have h := central_count C (C.system.count_pos_iff.mp hS) x c hc
  have hf : 0 < (C.system.fiber x c).card := by
    by_contra hz
    have hz' : (C.system.fiber x c).card = 0 := by omega
    rw [hz', Nat.mul_zero] at h
    omega
  obtain ⟨f, hf⟩ := Finset.card_pos.mp hf
  exact ⟨f, (C.system.mem_fiber x c f).mp hf⟩

/-- A deterministic central midpoint used by cheap promotions. Its definition
needs only the actual current endpoint arithmetic, never enumeration of maps. -/
def midpoint (C : OrderedSystem n K) (hne : ∃ f, C.system.Valid f) (x : Fin n) : Fin (K + 1) :=
  ⟨(C.system.effectiveLower x).val +
      ((C.system.effectiveUpper x).val - (C.system.effectiveLower x).val) / 2, by
    have h := (midpoint_central (effective_bounds C hne x)).2
    exact h.trans_le (interval_upper_le C hne x)⟩

theorem midpoint_mem (C : OrderedSystem n K) (hne : ∃ f, C.system.Valid f) (x : Fin n) :
    intervalLower C x ≤ (midpoint C hne x).val ∧ (midpoint C hne x).val < intervalUpper C x :=
  midpoint_central (effective_bounds C hne x)

theorem midpoint_supported (C : OrderedSystem n K) (hS : 0 < C.system.count) (x : Fin n) :
    ∃ f, C.system.Valid f ∧ f x = midpoint C (C.system.count_pos_iff.mp hS) x :=
  central_support C hS x _ (midpoint_mem C _ x)

/-- The actual cheap midpoint loses at most the advertised `W₀·4^B` factor. -/
theorem midpoint_cheap_count (C : OrderedSystem n K) (hne : ∃ f, C.system.Valid f)
    (x : Fin n) (B W₀ : ℕ) (hB : comparableCount C x ≤ B) (hW : windowWidth C x ≤ W₀) :
    C.system.count ≤ W₀ * 4 ^ B * (C.system.fiber x (midpoint C hne x)).card :=
  (central_count C hne x _ (midpoint_mem C hne x)).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul hW (Nat.pow_le_pow_right (by decide : 0 < 4) hB)))

/-- The elementary normalization of a genuine finite fibre count. -/
theorem mass_lower_of_count (S : WeakSystem (Fin n) (K + 1)) (hS : 0 < S.count)
    (x : Fin n) (c : Fin (K + 1)) (D : ℕ) (hD : 0 < D)
    (hcount : S.count ≤ D * (S.fiber x c).card) :
    1 / (D : ℚ) ≤ mass S x c.val := by
  rw [mass, levelCount, levelFiber_fin]
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  have hS' : (0 : ℚ) < S.count := by exact_mod_cast hS
  apply (div_le_div_iff₀ hD' hS').mpr
  have hc : (S.count : ℚ) ≤ (D : ℚ) * (S.fiber x c).card := by exact_mod_cast hcount
  nlinarith

/-- The true central probability has exactly the window-form lower bound
needed by the dyadic price lemma. -/
theorem central_mass (C : OrderedSystem n K) (hS : 0 < C.system.count)
    (x : Fin n) (c : Fin (K + 1)) (B : ℕ) (hB : comparableCount C x ≤ B)
    (hc : intervalLower C x ≤ c.val ∧ c.val < intervalUpper C x) :
    1 / ((2 * 4 ^ B : ℚ) * (intervalUpper C x - intervalLower C x : ℕ)) ≤
      mass C.system x c.val := by
  have hne := C.system.count_pos_iff.mp hS
  have hm : 0 < intervalUpper C x - intervalLower C x := by
    have h := (interval_bounds C hne x).2.1
    omega
  have hD : 0 < 2 * 4 ^ B * (intervalUpper C x - intervalLower C x) := by positivity
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
    mass_lower_of_count C.system hS x c _ hD (central_count_by_length C hne x c B hB hc)

theorem central_mass_real (C : OrderedSystem n K) (hS : 0 < C.system.count)
    (x : Fin n) (c : Fin (K + 1)) (B : ℕ) (hB : comparableCount C x ≤ B)
    (hc : intervalLower C x ≤ c.val ∧ c.val < intervalUpper C x) :
    1 / ((2 * 4 ^ B : ℝ) * (intervalUpper C x - intervalLower C x : ℕ)) ≤
      (mass C.system x c.val : ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).mpr (central_mass C hS x c B hB hc)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat] using h

/-- Numerical palette rank of the actual immutable hub identity. -/
def chosenRank (order : Equiv.Perm (Fin (K + 1))) (chosen : Block) : ℕ :=
  paletteRank order (hubColour (paletteRank order) (paletteRank_injective order) chosen)

/-- The selected rank lies in the current finite palette by the proved
window bounds. This conversion does not wrap or change its value. -/
def chosenColour (C : OrderedSystem n K) (hne : ∃ f, C.system.Valid f) (x : Fin n)
    (order : Equiv.Perm (Fin (K + 1))) {veto : Finset Block} {chosen : Block}
    (hchosen : selectWindow order (intervalLower C x + 1) (intervalUpper C x - 1) veto = some chosen) :
    Fin (K + 1) :=
  ⟨chosenRank order chosen, by
    have h := (selected_hub_in_window order hchosen).2
    have hK := interval_upper_le C hne x
    dsimp [chosenRank]
    omega⟩

@[simp] theorem chosenColour_val (C : OrderedSystem n K) (hne : ∃ f, C.system.Valid f)
    (x : Fin n) (order : Equiv.Perm (Fin (K + 1))) {veto : Finset Block} {chosen : Block}
    (hchosen : selectWindow order (intervalLower C x + 1) (intervalUpper C x - 1) veto = some chosen) :
    (chosenColour C hne x order hchosen).val = chosenRank order chosen := rfl

theorem chosenColour_mem (C : OrderedSystem n K) (hne : ∃ f, C.system.Valid f)
    (x : Fin n) (order : Equiv.Perm (Fin (K + 1))) {veto : Finset Block} {chosen : Block}
    (hchosen : selectWindow order (intervalLower C x + 1) (intervalUpper C x - 1) veto = some chosen) :
    intervalLower C x ≤ (chosenColour C hne x order hchosen).val ∧
      (chosenColour C hne x order hchosen).val < intervalUpper C x := by
  have h := selected_hub_in_window order hchosen
  simp only [chosenColour_val, chosenRank]
  omega

/-- Trimming the central interval makes the actual physical pin strictly
interior to its original effective window, so it needs no palette split. -/
theorem chosenColour_interior (C : OrderedSystem n K) (hne : ∃ f, C.system.Valid f)
    (x : Fin n) (order : Equiv.Perm (Fin (K + 1))) {veto : Finset Block} {chosen : Block}
    (hchosen : selectWindow order (intervalLower C x + 1) (intervalUpper C x - 1) veto = some chosen) :
    C.system.effectiveLower x < chosenColour C hne x order hchosen ∧
      chosenColour C hne x order hchosen < C.system.effectiveUpper x := by
  have h := selected_hub_in_window order hchosen
  have hw := interval_bounds C hne x
  simp only [Fin.lt_def, chosenColour_val, chosenRank]
  omega

theorem chosenColour_supported (C : OrderedSystem n K) (hS : 0 < C.system.count)
    (x : Fin n) (order : Equiv.Perm (Fin (K + 1))) {veto : Finset Block} {chosen : Block}
    (hchosen : selectWindow order (intervalLower C x + 1) (intervalUpper C x - 1) veto = some chosen) :
    ∃ f, C.system.Valid f ∧ f x = chosenColour C (C.system.count_pos_iff.mp hS) x order hchosen :=
  central_support C hS x _ (chosenColour_mem C _ x order hchosen)

/-- The actual physical pin retains the insertion fraction of the current
parent model. All counting is on the true finite map family. -/
theorem chosen_pin_count (C : OrderedSystem n K) (hne : ∃ f, C.system.Valid f)
    (x : Fin n) (order : Equiv.Perm (Fin (K + 1))) {veto : Finset Block} {chosen : Block}
    (hchosen : selectWindow order (intervalLower C x + 1) (intervalUpper C x - 1) veto = some chosen)
    (B : ℕ) (hB : comparableCount C x ≤ B) :
    C.system.count ≤ 2 * 4 ^ B * (intervalUpper C x - intervalLower C x) *
      (FiniteRefinement.pinAt C.system x (chosenColour C hne x order hchosen)).count := by
  simpa only [WeakSystem.count, FiniteRefinement.maps_pinAt] using
    central_count_by_length C hne x _ B hB (chosenColour_mem C hne x order hchosen)

/-- Complete scale-hub price: actual insertion fibres discharge the true
probability premise of the dyadic selector's price theorem. -/
theorem selected_log_price_bound (C : OrderedSystem n K) (hS : 0 < C.system.count)
    (x : Fin n) (order : Equiv.Perm (Fin (K + 1))) {veto : Finset Block} {chosen : Block}
    (hchosen : selectWindow order (intervalLower C x + 1) (intervalUpper C x - 1) veto = some chosen)
    (B M : ℕ) (hB : comparableCount C x ≤ B) (hcap : K + 1 ≤ 2 ^ M)
    (hwidth : 32 ≤ windowWidth C x)
    (hveto : 4 * vetoCost veto ≤ intervalUpper C x - intervalLower C x) :
    -Real.log (mass C.system x (chosenRank order chosen) : ℝ) ≤
      Real.log ((8 * (2 * 4 ^ B : ℝ)) * chosen.size * (M - chosen.level + 2 : ℕ)) := by
  have hne := C.system.count_pos_iff.mp hS
  apply HubPricing.selected_log_price_bound order hcap (interval_upper_le C hne x)
    (interval_large C hne x hwidth) hveto hchosen (2 * 4 ^ B)
    (mass C.system x (chosenRank order chosen)) (by positivity)
  simpa only [chosenColour_val] using central_mass_real C hS x
    (chosenColour C hne x order hchosen) B hB (chosenColour_mem C hne x order hchosen)

end SortingAdversary.Optimal.ScaleMass
