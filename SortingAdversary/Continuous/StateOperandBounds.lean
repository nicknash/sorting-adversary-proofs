import SortingAdversary.Continuous.StateWork
import SortingAdversary.Continuous.OperandBounds

/-!
# State-mutation operands and raw dyadic decoding

The decoder's output code alone does not bound the numerator it reads. This
module records the raw input integers, division operands and results, every
denominator-halving prefix, and every intermediate power of two. The input
fraction's proved width and grid exponent supply the bounds. For the actual
interior anchors, the common grid also bounds the input fraction itself.
Finite min/max scans and every normalization prefix retain their input
width, because their values are selected from the supplied endpoints.
-/

namespace SortingAdversary.Continuous.StateOperandBounds

open SortingAdversary.Optimal
open OperandBounds Precision FiniteAveraging

structure DecoderOperands (q : ℚ) (B : ℕ) : Prop where
  denominator : q.den.size ≤ B
  signedNumerator : q.num.natAbs.size ≤ B
  numerator : q.num.toNat.size ≤ B
  half : (q.num.toNat / 2).size ≤ B
  logarithm : (StateWork.logTwo q.den).value.size ≤ B
  level : ((StateWork.logTwo q.den).value - 1).size ≤ B
  power : (StateWork.powTwo ((StateWork.logTwo q.den).value - 1)).value.size ≤ B
  remainder : ((q.num.toNat / 2) %
    (StateWork.powTwo ((StateWork.logTwo q.den).value - 1)).value).size ≤ B
  halvingPrefixes : ∀ a ≤ q.den, a.size ≤ B
  powerPrefixes : ∀ e ≤ (StateWork.logTwo q.den).value - 1,
    (StateWork.powTwo e).value.size ≤ B

theorem DecoderOperands.mono {q : ℚ} {A B : ℕ} (h : DecoderOperands q A) (hAB : A ≤ B) :
    DecoderOperands q B :=
  ⟨h.denominator.trans hAB, h.signedNumerator.trans hAB, h.numerator.trans hAB,
    h.half.trans hAB, h.logarithm.trans hAB, h.level.trans hAB, h.power.trans hAB,
    h.remainder.trans hAB, fun a ha => (h.halvingPrefixes a ha).trans hAB,
    fun e he => (h.powerPrefixes e he).trans hAB⟩

theorem decode_operands (q : ℚ) (B F : ℕ) (hq : Fits B q) (hg : OnDyadicGrid F q) :
    DecoderOperands q (B + F + 4) := by
  have hnum : q.num.toNat ≤ q.num.natAbs := by
    have h := Int.toNat_add_toNat_neg_eq_natAbs q.num
    omega
  have hn : q.num.toNat.size ≤ B := (Nat.size_le_size hnum).trans hq.1
  have hh : (q.num.toNat / 2).size ≤ B :=
    (Nat.size_le_size (Nat.div_le_self _ _)).trans hn
  have hl : (StateWork.logTwo q.den).value ≤ F := by
    rw [StateWork.logTwo_value]
    exact StateWork.grid_log_den hg
  have hp (e : ℕ) (he : e ≤ (StateWork.logTwo q.den).value - 1) :
      (StateWork.powTwo e).value.size ≤ F + 1 := by
    rw [StateWork.powTwo_value, Nat.size_pow]
    omega
  refine ⟨hq.2.trans (by omega), hq.1.trans (by omega), hn.trans (by omega),
    hh.trans (by omega), ?_, ?_, (hp _ le_rfl).trans (by omega), ?_, ?_, ?_⟩
  · exact (size_le_value _).trans (by omega)
  · exact (size_le_value _).trans (by omega)
  · exact (Nat.size_le_size (Nat.mod_le _ _)).trans (hh.trans (by omega))
  · intro a ha
    exact (Nat.size_le_size ha).trans (hq.2.trans (by omega))
  · intro e he
    exact (hp e he).trans (by omega)

/-- The real refinement inputs lie in the unit interval, so their raw
numerator and denominator have the same grid bound as the stored state. -/
theorem decode_operands_of_unit_grid (q : ℚ) (F : ℕ) (hg : OnDyadicGrid F q)
    (h0 : 0 ≤ q) (h1 : q ≤ 1) : DecoderOperands q (2 * F + 5) := by
  have h := decode_operands q (F + 1) F (Fits.of_grid hg h0 h1) hg
  convert h using 1; omega

def BoundsFit {ι : Type*} (B : ℕ) (D : System ι ℚ) : Prop :=
  ∀ x, Fits B (D.lower x) ∧ Fits B (D.upper x)

theorem min_fits {B : ℕ} {q r : ℚ} (hq : Fits B q) (hr : Fits B r) : Fits B (min q r) := by
  rcases le_total q r with h | h
  · simpa only [min_eq_left h] using hq
  · simpa only [min_eq_right h] using hr

/-- An arbitrary subset includes every intermediate prefix of a finite
maximum scan, not only its final value. -/
theorem maxFold_fits {ι : Type*} {B : ℕ} (S : Finset ι) (base : ℚ) (f : ι → ℚ)
    (hbase : Fits B base) (hf : ∀ x ∈ S, Fits B (f x)) : Fits B (S.fold max base f) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hbase
  | @insert x S hx ih =>
    rw [Finset.fold_insert hx]
    exact (hf x (by simp)).max (ih (fun y hy => hf y (by simp [hy])))

theorem minFold_fits {ι : Type*} {B : ℕ} (S : Finset ι) (base : ℚ) (f : ι → ℚ)
    (hbase : Fits B base) (hf : ∀ x ∈ S, Fits B (f x)) : Fits B (S.fold min base f) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hbase
  | @insert x S hx ih =>
    rw [Finset.fold_insert hx]
    exact min_fits (hf x (by simp)) (ih (fun y hy => hf y (by simp [hy])))

theorem conditionalLower_fits {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ℕ}
    (D : System ι ℚ) (x : ι) (Y : ι → ℚ) (hD : BoundsFit B D)
    (hY : ∀ y, Fits B (Y y)) : Fits B (conditionalLower D x Y) :=
  maxFold_fits _ _ _ (hD x).1 (fun y _ => hY y)

theorem conditionalUpper_fits {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ℕ}
    (D : System ι ℚ) (x : ι) (Y : ι → ℚ) (hD : BoundsFit B D)
    (hY : ∀ y, Fits B (Y y)) : Fits B (conditionalUpper D x Y) :=
  minFold_fits _ _ _ (hD x).2 (fun y _ => hY y)

variable {n B : ℕ}

theorem propagateLower_fits (D : EnclosureWork.StoredSystem n) (x : Fin n)
    (hD : BoundsFit B D.system) : BoundsFit B (StateWork.propagateLower D x).value.system := by
  rw [StateWork.propagateLower_value]
  intro y
  refine ⟨?_, (hD y).2⟩
  change Fits B (Function.update D.system.lower x (conditionalLower D.system x D.system.lower) y)
  by_cases hy : y = x
  · subst y
    simp only [Function.update_self]
    exact conditionalLower_fits _ _ _ hD (fun z => (hD z).1)
  · simpa only [Function.update_of_ne hy] using (hD y).1

theorem propagateUpper_fits (D : EnclosureWork.StoredSystem n) (x : Fin n)
    (hD : BoundsFit B D.system) : BoundsFit B (StateWork.propagateUpper D x).value.system := by
  rw [StateWork.propagateUpper_value]
  intro y
  refine ⟨(hD y).1, ?_⟩
  change Fits B (Function.update D.system.upper x (conditionalUpper D.system x D.system.upper) y)
  by_cases hy : y = x
  · subst y
    simp only [Function.update_self]
    exact conditionalUpper_fits _ _ _ hD (fun z => (hD z).2)
  · simpa only [Function.update_of_ne hy] using (hD y).2

/-- Arbitrary orders include every prefix of the actual lower pass. -/
theorem lowerPass_fits (D : EnclosureWork.StoredSystem n) (order : List (Fin n))
    (hD : BoundsFit B D.system) : BoundsFit B (StateWork.lowerPass D order).value.system := by
  induction order generalizing D with
  | nil => exact hD
  | cons x xs ih => exact ih _ (propagateLower_fits D x hD)

theorem upperPass_fits (D : EnclosureWork.StoredSystem n) (order : List (Fin n))
    (hD : BoundsFit B D.system) : BoundsFit B (StateWork.upperPass D order).value.system := by
  induction order generalizing D with
  | nil => exact hD
  | cons x xs ih => exact ih _ (propagateUpper_fits D x hD)

theorem normalize_fits (D : EnclosureWork.StoredSystem n) (order : List (Fin n))
    (hD : BoundsFit B D.system) : BoundsFit B (StateWork.normalize D order).value.system :=
  upperPass_fits _ _ (lowerPass_fits D order hD)

theorem reset_fits (D : EnclosureWork.StoredSystem n) (x : Fin n) (c : ℚ)
    (hD : BoundsFit B D.system) (hc : Fits B c) (hB : 1 ≤ B) :
    BoundsFit B (StateWork.reset D x c).value.system := by
  rw [StateWork.reset_value]
  intro y
  have hz : Fits B 0 := by simpa [Fits] using And.intro (Nat.zero_le B) hB
  by_cases hy : y = x
  · subst y
    simpa [TreeState.resetCoordinate] using And.intro hz (fits_one hB)
  · simp only [TreeState.resetCoordinate, if_neg hy]
    constructor
    · split
      · exact (hD y).1.max hc
      · exact (hD y).1
    · split
      · exact min_fits (hD y).2 hc
      · exact (hD y).2

theorem addArc_fits (D : EnclosureWork.StoredSystem n) (x y : Fin n)
    (hD : BoundsFit B D.system) : BoundsFit B (StateWork.addArc D x y).value.system := hD

theorem boundBelow_fits (D : EnclosureWork.StoredSystem n) (x : Fin n) (c : ℚ)
    (hD : BoundsFit B D.system) (hc : Fits B c) :
    BoundsFit B (StateWork.boundBelow D x c).value.system := by
  rw [StateWork.boundBelow_value]
  intro y
  refine ⟨(hD y).1, ?_⟩
  change Fits B (Function.update D.system.upper x (min (D.system.upper x) c) y)
  by_cases hy : y = x
  · subst y
    simp only [Function.update_self]
    exact min_fits (hD x).2 hc
  · simpa only [Function.update_of_ne hy] using (hD y).2

theorem boundAbove_fits (D : EnclosureWork.StoredSystem n) (x : Fin n) (c : ℚ)
    (hD : BoundsFit B D.system) (hc : Fits B c) :
    BoundsFit B (StateWork.boundAbove D x c).value.system := by
  rw [StateWork.boundAbove_value]
  intro y
  refine ⟨?_, (hD y).2⟩
  change Fits B (Function.update D.system.lower x (max (D.system.lower x) c) y)
  by_cases hy : y = x
  · subst y
    simp only [Function.update_self]
    exact (hD x).1.max hc
  · simpa only [Function.update_of_ne hy] using (hD y).1

def RoutedFits (B : ℕ) : TreeState.Routing ℚ → Prop
  | .coordinates => True
  | .leftFree c | .rightFree c => Fits B c
  | .anchors c d => Fits B c ∧ Fits B d

theorem recordSystem_fits (D : EnclosureWork.StoredSystem n) (r : TreeState.Routing ℚ)
    (x y : Fin n) (a : Answer) (hD : BoundsFit B D.system) (hr : RoutedFits B r) :
    BoundsFit B (StateWork.recordSystem D r x y a).value.system := by
  cases r with
  | coordinates => cases a <;> exact addArc_fits _ _ _ hD
  | leftFree c =>
    cases a with
    | less => exact boundBelow_fits _ _ _ hD hr
    | greater => exact boundAbove_fits _ _ _ hD hr
  | rightFree c =>
    cases a with
    | less => exact boundAbove_fits _ _ _ hD hr
    | greater => exact boundBelow_fits _ _ _ hD hr
  | anchors c d => cases a <;> exact hD

end SortingAdversary.Continuous.StateOperandBounds
