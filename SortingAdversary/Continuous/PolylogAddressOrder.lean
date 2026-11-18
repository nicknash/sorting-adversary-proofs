import SortingAdversary.Continuous.PolylogBlockAnchor
import SortingAdversary.Optimal.PrimitiveWork

/-!
# Ordering raw addresses in the sparse tables

The concrete tables contain natural-number addresses and need no change of
type as the heap grows. A height tag identifies roots at the binary point's
chosen block height. A root decodes to its nonnegative dyadic value. Other
addresses get distinct negative values, making the logical decoder total
and injective. Only the tag and the shared-block comparator run on a query.
-/

namespace SortingAdversary.Continuous.PolylogAddressOrder

open PolylogBits PolylogBlockAnchor
open Optimal.PrimitiveWork (Result)

variable {S : Store} {H H' : Heap} {D h i j : ℕ}

def isRoot (H : Heap) : ℕ → ℕ → Bool
  | 0, i => decide (i < 2)
  | d+1, i => (H.record[i]?).any fun k => k.1 == d+1

theorem isRoot_of_rep {a : S.Ref h} (r : Represents S H i a) : isRoot H h i = true := by
  cases r with
  | leaf b => cases b <;> rfl
  | node e _ _ => simp [isRoot, e]

theorem isRoot_iff (S : Store) (H : Heap) (ht : H.Typed) (h i : ℕ) :
    isRoot H h i = true ↔ ∃ a : S.Ref h, Represents S H i a := by
  constructor
  · intro e
    cases h with
    | zero =>
      have hi : i < 2 := of_decide_eq_true e
      interval_cases i
      · exact ⟨_, .leaf false⟩
      · exact ⟨_, .leaf true⟩
    | succ d =>
      cases f : H.record[i]? with
      | none => simp [isRoot, f] at e
      | some k =>
        obtain ⟨z, l, r⟩ := k
        simp [isRoot, f] at e
        subst z
        exact ht S d i l r f
  · rintro ⟨_, r⟩; exact isRoot_of_rep r

noncomputable def decode (S : Store) (H : Heap) (D h i : ℕ) : ℚ := by
  classical
  exact if e : ∃ a : S.Ref h, Represents S H i a then coord S D e.choose else -(i+1 : ℕ)

theorem decode_of_rep (v : H.Valid) {a : S.Ref h} (r : Represents S H i a) :
    decode S H D h i = coord S D a := by
  classical
  have e := Exists.intro a r
  rw [decode, dif_pos e, (e.choose_spec.same_iff v r).mp rfl]

private theorem coord_nonneg (S : Store) (D : ℕ) {h} (a : S.Ref h) : 0 ≤ coord S D a := by
  unfold coord; positivity

theorem nonneg_iff (S : Store) (H : Heap) (D h i : ℕ) :
    0 ≤ decode S H D h i ↔ ∃ a : S.Ref h, Represents S H i a := by
  classical
  unfold decode
  split
  · exact iff_of_true (coord_nonneg _ _ _) ‹_›
  · simp_all; linarith [Nat.cast_nonneg (α := ℚ) i]

/-- Already allocated wall values agree in every extending valid heap. -/
theorem persistent (v : H.Valid) (v' : H'.Valid) (growth : H'.Extends H)
    (hi : 0 ≤ decode S H D h i) : decode S H' D h i = decode S H D h i := by
  obtain ⟨a,r⟩ := (nonneg_iff S H D h i).mp hi
  rw [decode_of_rep v r, decode_of_rep v' (r.lift growth)]

theorem injective (S : Store) (H : Heap) (v : H.Valid) (D h : ℕ) :
    Function.Injective (decode S H D h) := by
  intro i j e
  by_cases hi : 0 ≤ decode S H D h i
  · obtain ⟨a,r⟩ := (nonneg_iff _ _ _ _ _).mp hi
    obtain ⟨b,t⟩ := (nonneg_iff _ _ _ _ _).mp (e ▸ hi)
    rw [decode_of_rep v r, decode_of_rep v t, coord, coord,
      div_left_inj' (by positivity : (2:ℚ)^D ≠ 0), Nat.cast_inj] at e
    exact (r.same_iff v t).2 (value_injective S h e)
  · have hn := mt (nonneg_iff S H D h i).mpr hi
    have hn' := mt (nonneg_iff S H D h j).mpr (hi ∘ (e ▸ id))
    simpa [decode, hn, hn'] using e

/-- At most two tag reads precede the shared-block comparison. False roots
are ordered by reverse address to agree with the negative-value convention. -/
def less (H : Heap) (h i j : ℕ) : Result Bool :=
  if isRoot H h i then
    if isRoot H h j then
      let r := H.lessAddr h i j
      ⟨r.1, r.2+4⟩
    else ⟨false, 4⟩
  else ⟨if isRoot H h j then true else decide (j < i), 5⟩

theorem correct (S : Store) (H : Heap) (v : H.Valid) (ht : H.Typed) (D h i j : ℕ) :
    (less H h i j).value = true ↔ decode S H D h i < decode S H D h j := by
  classical
  by_cases hi : isRoot H h i = true <;> by_cases hj : isRoot H h j = true
  · obtain ⟨a,r⟩ := (isRoot_iff S H ht h i).mp hi
    obtain ⟨b,t⟩ := (isRoot_iff S H ht h j).mp hj
    rw [decode_of_rep v r, decode_of_rep v t, coord, coord,
      div_lt_div_iff_of_pos_right (by positivity), Nat.cast_lt]
    simpa [less, hi, hj, Heap.lessAddr_refines S v r t] using less_correct S h a b
  · obtain ⟨a,r⟩ := (isRoot_iff S H ht h i).mp hi
    have ne := mt (isRoot_iff S H ht h j).mpr hj
    rw [decode_of_rep v r]
    simp [less, hi, hj, decode, ne]
    have := coord_nonneg S D a
    linarith
  · obtain ⟨b,t⟩ := (isRoot_iff S H ht h j).mp hj
    have ne := mt (isRoot_iff S H ht h i).mpr hi
    rw [decode_of_rep v t]
    simp [less, hi, hj, decode, ne]
    have := coord_nonneg S D b
    linarith
  · have ni := mt (isRoot_iff S H ht h i).mpr hi
    have nj := mt (isRoot_iff S H ht h j).mpr hj
    simp [less, hi, hj, decode, ni, nj]
    constructor <;> intro e <;> (norm_cast at *; omega)

private theorem addr_work (H : Heap) (h i j : ℕ) : (H.lessAddr h i j).2 = 3*h+2 := by
  induction h generalizing i j with
  | zero => rfl
  | succ h ih =>
    simp only [Heap.lessAddr]
    split <;> simp [ih, Nat.mul_succ, Nat.add_assoc]

theorem work (H : Heap) (h i j : ℕ) : (less H h i j).work ≤ 3*h+6 := by
  unfold less
  split
  · split <;> simp [addr_work]
  · simp

end SortingAdversary.Continuous.PolylogAddressOrder
