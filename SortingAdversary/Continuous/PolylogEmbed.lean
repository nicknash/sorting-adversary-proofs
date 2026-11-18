import SortingAdversary.Continuous.PolylogBlockAnchor

/-!
# Embedding a short numerator into the canonical block heap

Starting from the cached zero block, visit only the numerator's e+1 digits
and their addressed ancestor paths. The integer with D fractional places is
used in the proof of decoding. The executable write never constructs it.
Work counts word operations, record accesses and intern calls, with one
intern call charged as a block primitive.
-/

namespace SortingAdversary.Continuous.PolylogEmbed

open PolylogBits PolylogBlockAnchor

variable {S : Store} {H : Heap} {h cap : ℕ}

/-- The heap extension carries its actual allocation bound. -/
structure Counted (S : Store) (H : Heap) {h : ℕ} (a : S.Ref h) extends Write S H a where
  work : ℕ
  allocated : heap.next ≤ H.next + work

/-- The abstract bits corresponding to the short numerator. -/
def digits (S : Store) (h : ℕ) : ℕ → ℕ → ℕ → S.Ref h
  | 0, _, _ => filled S h false
  | l+1, off, z =>
    let prev := digits S h l (off+1) (z/2)
    if z%2 = 1 then (addUnit S (uniformSpec S) (atBit h off) prev).result else prev

private theorem digits_value (S : Store) (h l off z : ℕ) (hz : z < 2^l)
    (fit : off + l ≤ 2^h) : value S h (digits S h l off z) = z * 2^off := by
  induction l generalizing off z with
  | zero =>
    have he : z = 0 := by simpa using hz
    simp [digits, he]
  | succ l ih =>
    have small : z/2 < 2^l := by rw [Nat.div_lt_iff_lt_mul (by decide)]; simpa [pow_succ] using hz
    have prev := ih (off+1) (z/2) small (by omega)
    have off_lt : off < 2^h := by omega
    have parity := Nat.mod_add_div z 2
    let w := digits S h l (off+1) (z/2)
    let t := addUnit S (uniformSpec S) (atBit h off) w
    have total := addUnit_correct S (uniformSpec S) (atBit h off) w
    change value S h t.result + (if t.carry then radix h else 0) = value S h w + _ at total
    change value S h w = _ at prev
    rw [prev, weight_eq, place_atBit _ _ off_lt, pow_succ 2 off] at total
    simp only [digits]
    split
    · rename_i one
      have zeq : z = 1 + 2 * (z/2) := by omega
      have ht : value S h t.result + (if t.carry then radix h else 0) = z*2^off := by
        calc
          _ = (z/2) * (2^off * 2) + 2^off := total
          _ = (1 + 2*(z/2)) * 2^off := by ring
          _ = _ := by rw [← zeq]
      have bound : z*2^off < radix h := by
        calc
          _ < 2^(l+1) * 2^off := Nat.mul_lt_mul_of_pos_right hz (Nat.two_pow_pos _)
          _ = 2^(off+(l+1)) := by rw [← pow_add, Nat.add_comm]
          _ ≤ radix h := by rw [radix_eq]; exact Nat.pow_le_pow_right (by decide) fit
      cases e : t.carry with
      | false => simpa only [e, Bool.false_eq_true, if_false, Nat.add_zero] using ht
      | true => simp only [e, if_true] at ht; omega
    · rename_i odd
      have zeq : 2 * (z/2) = z := by omega
      calc
        _ = (z/2) * (2^off * 2) := by rw [prev, pow_succ 2 off]
        _ = (2 * (z/2)) * 2^off := by ring
        _ = _ := by rw [zeq]

private def retag {a b : S.Ref h} (w : Write S H a) (e : a = b) : Write S H b :=
  ⟨w.heap, w.valid, w.growth, ⟨w.cell.addr, e ▸ w.cell.rep⟩⟩

private def emit (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap) :
    (l off z : ℕ) → Counted S H (digits S h l off z)
  | 0, _, _ => ⟨.unchanged v (cache.cell hc false), 1, Nat.le_succ _⟩
  | l+1, off, z =>
    let prev := emit v cache hc l (off+1) (z/2)
    if e : z%2 = 1 then
      let p := atBit h off
      let t := addUnitAddr prev.valid (cache.lift prev.growth) p hc prev.cell
      ⟨retag (t.out.after prev.growth) (by simp [digits, e, p]),
        prev.work + (10*h+2) + (h+1)^2 + 4, by
          change t.out.heap.next ≤ _
          have h₁ := (addUnitAddr_growth prev.valid (cache.lift prev.growth) p hc prev.cell).1
          change t.out.heap.next ≤ prev.heap.next + 2*h at h₁
          have h₂ := prev.allocated; omega⟩
    else
      ⟨retag prev.toWrite (by simp [digits, e]), prev.work+4, by
        change prev.heap.next ≤ _; have := prev.allocated; omega⟩

private theorem emit_work (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap)
    (l off z : ℕ) :
    (emit v cache hc l off z).work ≤ 1 + l*((h+1)^2+10*h+6) := by
  induction l generalizing off z with
  | zero => simp [emit]
  | succ l ih =>
    have prev := ih (off+1) (z/2)
    simp only [emit]
    split <;> dsimp only <;> rw [Nat.succ_mul l] <;> omega

/-- Embed z/2^e at a binary point D by reading the e+1 short input digits. -/
def embedAddr (D e z : ℕ) (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap) :=
  emit v cache hc (e+1) (D-e) z

theorem embedAddr_work (D e z : ℕ) (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap) :
    (embedAddr D e z v cache hc).work ≤ 1 + (e+1)*((h+1)^2+10*h+6) := emit_work ..

theorem embedAddr_represents (D e z : ℕ) (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap)
    (hD : D < 2^h) (he : e ≤ D) (hz : z ≤ 2^e) :
    let w := embedAddr D e z v cache hc
    ∃ b : S.Ref h, Represents S w.heap w.cell.addr b ∧ coord S D b = (z : ℚ)/(2:ℚ)^e := by
  refine ⟨_, (embedAddr D e z v cache hc).cell.rep, ?_⟩
  change (value S h (digits S h (e+1) (D-e) z) : ℚ)/(2:ℚ)^D = _
  have hz' : z < 2^(e+1) := by have h := Nat.two_pow_pos e; rw [pow_succ]; omega
  rw [digits_value _ _ _ _ _ hz' (by omega)]
  push_cast
  have hsplit : (2 : ℚ)^(D-e) * 2^e = 2^D := by rw [← pow_add, Nat.sub_add_cancel he]
  rw [← hsplit]
  field_simp

end SortingAdversary.Continuous.PolylogEmbed
