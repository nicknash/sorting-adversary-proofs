import SortingAdversary.Continuous.PolylogBits
import SortingAdversary.Continuous.PolylogAnchor
import Mathlib.Data.Rat.Floor

/-!
# The fallback on shared binary blocks

A block's binary point is fixed at `D` fractional bits. Bisection probes
allocate a temporary sum in an extended heap; the input heap and both
walls survive unchanged. The final anchor copies a prefix of the lower wall
and adds three units using the same shared-block operations.
-/

namespace SortingAdversary.Continuous.PolylogBlockAnchor

open PolylogBits PolylogAnchor

variable {S : Store} {H : Heap} {h cap : ℕ}

/-- Only the proof interprets the block as a rational. -/
def coord (S : Store) (D : ℕ) {h} (a : S.Ref h) : ℚ := value S h a / (2 : ℚ)^D

def placeFor (h D s : ℕ) : Position h := atBit h (D-s)

theorem unit_placeFor (D s : ℕ) (hD : D < 2^h) (hs : s ≤ D) :
    (weight (placeFor h D s) : ℚ) / (2 : ℚ)^D = unit s := by
  rw [placeFor, weight_eq, place_atBit _ _ (by omega)]
  push_cast
  have e : 2^(D-s) * (2:ℚ)^s = 2^D := by rw [← pow_add]; congr 1; omega
  rw [unit]
  field_simp
  linarith

/-- Test whether adding a unit at this bit of the lower wall stays at most
the upper wall. Overflow immediately falsifies the test. -/
def fits (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap)
    {a b : S.Ref h} (left : Cell S H a) (right : Cell S H b) (p : Position h) : Bool :=
  let t := addUnitAddr v cache p hc left
  !t.carry && !(t.out.heap.lessAddr h right.addr t.out.cell.addr).1

theorem fits_iff (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap)
    {a b : S.Ref h} (left : Cell S H a) (right : Cell S H b) (p : Position h) :
    fits v cache hc left right p = true ↔ value S h a + weight p ≤ value S h b := by
  let t := addUnitAddr v cache p hc left
  have eq := Heap.lessAddr_refines S t.out.valid (right.rep.lift t.out.growth) t.out.cell.rep
  have cmp := less_correct S h b (addUnit S (uniformSpec S) p a).result
  have arith := addUnit_correct S (uniformSpec S) p a
  change (!t.carry && !(t.out.heap.lessAddr h right.addr t.out.cell.addr).1) = true ↔ _
  rw [eq, t.correct]
  cases e : (addUnit S (uniformSpec S) p a).carry with
  | false =>
    simp [e] at arith
    simp [Bool.eq_false_iff, cmp, arith]
  | true =>
    simp [e] at arith
    have hb := value_lt S h b
    simp
    omega

def widthSearchAddr (D F : ℕ) (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap)
    {a b : S.Ref h} (left : Cell S H a) (right : Cell S H b) : ℕ × ℕ :=
  bisect (fun s => fits v cache hc left right (placeFor h D (min s F)))
    (Nat.log 2 F + 1) 0 F

theorem widthSearchAddr_eq (D F : ℕ) (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap)
    {a b : S.Ref h} (left : Cell S H a) (right : Cell S H b)
    (hD : D < 2^h) (hF : F ≤ D) (hw : unit F ≤ coord S D b - coord S D a) :
    widthSearchAddr D F v cache hc left right = widthSearch F (coord S D a) (coord S D b) := by
  unfold widthSearchAddr widthSearch
  congr 1
  funext s
  apply Bool.eq_iff_iff.mpr
  rw [fits_iff, decide_eq_true_eq]
  let j := min s F
  have hj : j ≤ D := (min_le_right _ _).trans hF
  have conv : (value S h a + weight (placeFor h D j) ≤ value S h b) ↔
      coord S D a + unit j ≤ coord S D b := by
    rw [← unit_placeFor D j hD hj]
    unfold coord
    rw [← add_div, div_le_div_iff_of_pos_right (by positivity)]
    exact_mod_cast Iff.rfl
  rw [conv]
  by_cases e : s ≤ F
  · simp [j, min_eq_left e]
  · have ant : unit s ≤ unit F := by
      apply one_div_le_one_div_of_le (by positivity : (0:ℚ) < 2^F)
      exact pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 2) (by omega)
    simp [j, min_eq_right (by omega : F ≤ s)]
    exact iff_of_true (by linarith) (by linarith)

/-- The concrete output heap and the address of the three-unit anchor,
including its representation proof. -/
def atScaleAddr (D s : ℕ) (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap)
    {a : S.Ref h} (left : Cell S H a) :=
  let p := placeFor h D (s+2)
  let t := truncateAddr v cache p hc left
  (advanceAddr t.valid (cache.lift t.growth) p hc t.cell 3).after t.growth

def fallbackAddr (D F : ℕ) (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap)
    {a b : S.Ref h} (left : Cell S H a) (right : Cell S H b) :=
  atScaleAddr D (widthSearchAddr D F v cache hc left right).1 v cache hc left

def modelAtScale (S : Store) (D s : ℕ) {h} (a : S.Ref h) : Advanced S h :=
  let p := placeFor h D (s+2)
  advance S (uniformSpec S) p (truncate S (uniformSpec S) p a).1 3

private theorem modelAtScale_total (D s : ℕ) {a : S.Ref h} (hD : D < 2^h) (hs : s+2 ≤ D) :
    ((value S h (modelAtScale S D s a).result + (modelAtScale S D s a).wraps * radix h : ℕ) : ℚ)
      / (2 : ℚ)^D = atScale s (coord S D a) := by
  let p := placeFor h D (s+2)
  let U := uniformSpec S
  have hw : (weight p : ℚ) / (2:ℚ)^D = unit (s+2) := unit_placeFor _ _ hD hs
  have ratio : coord S D a / unit (s+2) = (value S h a : ℚ) / weight p := by
    rw [← hw, coord]
    field_simp
  have total := advance_correct S U p (truncate S U p a).1 3
  rw [value_truncate] at total
  change value S h (modelAtScale S D s a).result + (modelAtScale S D s a).wraps * radix h =
    value S h a / weight p * weight p + 3 * weight p at total
  rw [total, atScale, ratio, Rat.floor_natCast_div_natCast, ← Int.natCast_ediv, ← hw]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.cast_natCast]
  ring

/-- If the scale is bracketed by the actual wall gap, the three additions
cannot overflow. The decoded returned block is the paper's rational anchor. -/
theorem atScaleAddr_represents (D s : ℕ) (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap)
    {a b : S.Ref h} (left : Cell S H a) (hD : D < 2^h) (hs : s+2 ≤ D)
    (lo : unit s ≤ coord S D b - coord S D a)
    (hi : coord S D b - coord S D a < 2 * unit s) :
    let w := atScaleAddr D s v cache hc left
    ∃ z : S.Ref h, Represents S w.heap w.cell.addr z ∧ coord S D z = atScale s (coord S D a) := by
  let m := modelAtScale S D s a
  refine ⟨m.result, (atScaleAddr D s v cache hc left).cell.rep, ?_⟩
  have total := modelAtScale_total D s (a := a) hD hs
  have bound := (atScale_middle lo hi).2
  have hp : 0 < unit s := by unfold unit; positivity
  have ltq : atScale s (coord S D a) ≤ coord S D b := by linarith
  rw [← total, coord, div_le_div_iff_of_pos_right (by positivity)] at ltq
  have natle : value S h m.result + m.wraps * radix h ≤ value S h b := by exact_mod_cast ltq
  have R := value_lt S h b
  have noCarry : m.wraps = 0 := by
    by_contra! hn
    have hh : radix h ≤ m.wraps * radix h := by simpa using Nat.mul_le_mul_right (radix h) (show 1 ≤ m.wraps by omega)
    omega
  change ((value S h m.result + m.wraps * radix h : ℕ) : ℚ) / (2:ℚ)^D = _ at total
  simpa [coord, noCarry] using total

/-- End-to-end refinement of the short-prefix fallback, including bisection
on actual heap addresses, truncation, three additions, and decoding. -/
theorem fallbackAddr_represents (D F : ℕ) (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap)
    {a b : S.Ref h} (left : Cell S H a) (right : Cell S H b)
    (hD : D < 2^h) (hF : F+2 ≤ D) (hw : unit F ≤ coord S D b - coord S D a)
    (hu : coord S D b - coord S D a ≤ 1) :
    let w := fallbackAddr D F v cache hc left right
    ∃ z : S.Ref h, Represents S w.heap w.cell.addr z ∧
      coord S D z = fallback F (coord S D a) (coord S D b) := by
  have eq := widthSearchAddr_eq D F v cache hc left right hD (by omega) hw
  have bounds := widthSearch_of_bound hw hu
  have ie := congrArg Prod.fst eq
  obtain ⟨z, hz, hf⟩ := atScaleAddr_represents D (widthSearchAddr D F v cache hc left right).1
    v cache hc left hD (by rw [ie]; have := bounds.1; omega)
    (by rw [ie]; exact bounds.2.1) (by rw [ie]; exact bounds.2.2)
  exact ⟨z, hz, hf.trans (congrArg (fun s => atScale s (coord S D a)) ie)⟩

/-- Bisection discards its temporary sums. The newly returned persistent heap
allocates at most seven new addresses per block height. -/
theorem fallbackAddr_growth (D F : ℕ) (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap)
    {a b : S.Ref h} (left : Cell S H a) (right : Cell S H b) :
    (fallbackAddr D F v cache hc left right).heap.next ≤ H.next + 7*h := by
  let s := (widthSearchAddr D F v cache hc left right).1
  let p := placeFor h D (s+2)
  let t := truncateAddr v cache p hc left
  have trunc := truncateAddr_growth v cache p hc left
  change t.heap.next ≤ H.next + h at trunc
  have adds := advanceAddr_growth t.valid (cache.lift t.growth) p hc t.cell 3
  change (advanceAddr t.valid (cache.lift t.growth) p hc t.cell 3).heap.next ≤ _
  omega

/-- A probe uses one addition and one comparison. The final prefix and
three-unit write use at most `3h + 3(10h+2)` block primitives. -/
theorem fallback_block_work (F : ℕ) (tests : Fin (Nat.log 2 F + 1) → Position h)
    (finalBit : Position h) (a b : S.Ref h) :
    let U := uniformSpec S
    (∑ i, ((addUnit S U (tests i) a).work + (less S h b (addUnit S U (tests i) a).result).2)) +
        (truncate S U finalBit a).2 +
        (advance S U finalBit (truncate S U finalBit a).1 3).work ≤
      (Nat.log 2 F + 1) * (13*h+4) + (33*h+6) := by
  dsimp only
  let U := uniformSpec S
  have probe (i : Fin (Nat.log 2 F + 1)) : (addUnit S U (tests i) a).work +
      (less S h b (addUnit S U (tests i) a).result).2 ≤ 13*h+4 := by
    rw [less_work]
    have := (addUnit_work S U (tests i) a).1
    omega
  have sum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => probe i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at sum
  have trunc := truncate_work S U finalBit a
  have adv := advance_work S U finalBit (truncate S U finalBit a).1 3
  dsimp only [U] at sum trunc adv
  omega

end SortingAdversary.Continuous.PolylogBlockAnchor
