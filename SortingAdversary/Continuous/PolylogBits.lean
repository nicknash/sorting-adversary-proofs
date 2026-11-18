import Std

/-!
# Exact operations on shared blocks of bits

A reference at height `h` denotes a block of `2^h` bits, most significant
half first. The interface below specifies splitting, interning two existing
blocks, and comparing references. The code never turns a block into a large
integer. Its natural-number interpretation is used only in the proofs.

Costs count block primitives: a split, an intern, a reference comparison,
a leaf read/write, or a lookup of a precomputed uniform block. They do not
count the internal operations of an interning dictionary.
-/

namespace SortingAdversary.Continuous.PolylogBits

/-- The inverse laws express canonical interning: splitting after interning
recovers the children, and a pair of children has only one reference. -/
structure Store where
  Ref : Nat → Type
  read : Ref 0 → Bool
  leaf : Bool → Ref 0
  split : {h : Nat} → Ref (h+1) → Ref h × Ref h
  join : {h : Nat} → Ref h → Ref h → Ref (h+1)
  same : {h : Nat} → Ref h → Ref h → Bool
  read_leaf : ∀ b, read (leaf b) = b
  leaf_read : ∀ a, leaf (read a) = a
  split_join : ∀ {h} (l r : Ref h), split (join l r) = (l, r)
  join_split : ∀ {h} (a : Ref (h+1)), join (split a).1 (split a).2 = a
  same_iff : ∀ {h} (a b : Ref h), same a b = true ↔ a = b

/-- Extensional block values, used to interpret a concrete heap. -/
def Block : Nat → Type
  | 0 => Bool
  | h+1 => Block h × Block h

private def blockDecEq : (h : Nat) → DecidableEq (Block h)
  | 0 => inferInstanceAs (DecidableEq Bool)
  | h+1 =>
    letI := blockDecEq h
    inferInstanceAs (DecidableEq (Block h × Block h))

def blockStore : Store where
  Ref := Block
  read a := a
  leaf b := b
  split a := a
  join a b := (a, b)
  same {h} a b := @decide (a = b) (blockDecEq h a b)
  read_leaf _ := rfl
  leaf_read _ := rfl
  split_join _ _ := rfl
  join_split _ := rfl
  same_iff {h} a b := by letI := blockDecEq h; simp

variable (S : Store)

/-- Two uniform blocks per height can be built bottom up with one intern
per block. The child is shared between both halves. -/
def filled : (h : Nat) → Bool → S.Ref h
  | 0, b => S.leaf b
  | h+1, b => let t := filled h b; S.join t t

/-- Uniform references are cached for the queried heights. -/
structure Uniform (S : Store) where
  get : (h : Nat) → Bool → S.Ref h
  correct : ∀ h b, get h b = filled S h b

/-- The number of different values of a block of this height. -/
def radix : Nat → Nat
  | 0 => 2
  | h+1 => radix h * radix h

def value : (h : Nat) → S.Ref h → Nat
  | 0, a => (S.read a).toNat
  | h+1, a => value h (S.split a).1 * radix h + value h (S.split a).2

private theorem high_lt {a b c d r : Nat} (ha : a < c) (hb : b < r) :
    a*r+b < c*r+d := by
  have H := Nat.mul_le_mul_right r (Nat.succ_le_of_lt ha)
  rw [Nat.succ_mul] at H
  omega

theorem value_lt (h : Nat) (a : S.Ref h) : value S h a < radix h := by
  induction h with
  | zero => cases e : S.read a <;> simp [value, radix, e]
  | succ h ih =>
    exact Nat.lt_of_lt_of_le
      (high_lt (d := 0) (ih (S.split a).1) (ih (S.split a).2)) (by simp [radix])

theorem value_injective (h : Nat) {a b : S.Ref h}
    (hab : value S h a = value S h b) : a = b := by
  induction h with
  | zero =>
    have hb : S.read a = S.read b := by
      cases ea : S.read a <;> cases eb : S.read b <;> simp_all [value]
    rw [← S.leaf_read a, ← S.leaf_read b, hb]
  | succ h ih =>
    change value S h (S.split a).1 * _ + value S h (S.split a).2 =
      value S h (S.split b).1 * _ + value S h (S.split b).2 at hab
    have left : value S h (S.split a).1 = value S h (S.split b).1 := by
      rcases Nat.lt_trichotomy (value S h (S.split a).1) (value S h (S.split b).1)
        with lt | eq | gt
      · have := high_lt (d := value S h (S.split b).2) lt (value_lt S h (S.split a).2)
        omega
      · exact eq
      · have := high_lt (d := value S h (S.split a).2) gt (value_lt S h (S.split b).2)
        omega
    rw [left] at hab
    have right : value S h (S.split a).2 = value S h (S.split b).2 := by omega
    calc
      a = S.join (S.split a).1 (S.split a).2 := (S.join_split a).symm
      _ = S.join (S.split b).1 (S.split b).2 := by rw [ih left, ih right]
      _ = b := S.join_split b

/-- Return strict numerical comparison and the number of primitives used.
Equal high halves can be skipped by one comparison of their references. -/
def less : (h : Nat) → S.Ref h → S.Ref h → Bool × Nat
  | 0, a, b => (!S.read a && S.read b, 2)
  | h+1, a, b =>
    let x := S.split a
    let y := S.split b
    let t := if S.same x.1 y.1 then less h x.2 y.2 else less h x.1 y.1
    (t.1, t.2+3)

theorem less_correct (h : Nat) (a b : S.Ref h) :
    (less S h a b).1 = true ↔ value S h a < value S h b := by
  induction h with
  | zero => cases ea : S.read a <;> cases eb : S.read b <;> simp [less, value, ea, eb]
  | succ h ih =>
    by_cases e : S.same (S.split a).1 (S.split b).1 = true
    · have eq := (S.same_iff _ _).mp e
      simp [less, e, value, ih]
      rw [eq]
      simp
    · have ne : value S h (S.split a).1 ≠ value S h (S.split b).1 := by
        intro he
        exact e ((S.same_iff _ _).mpr (value_injective S h he))
      simp [less, e, ih, value]
      constructor
      · intro hl
        exact high_lt hl (value_lt S h _)
      · intro hl
        apply Nat.lt_of_not_ge
        intro hge
        have hgt : value S h (S.split b).1 < value S h (S.split a).1 := by omega
        have := high_lt (d := value S h (S.split a).2) hgt (value_lt S h (S.split b).2)
        omega

theorem less_work (h : Nat) (a b : S.Ref h) : (less S h a b).2 = 3*h+2 := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [less]
    split <;> simp [ih, Nat.mul_succ, Nat.add_assoc]

/-- A leaf address, proceeding from the most significant address bit. -/
inductive Position : Nat → Type
  | here : Position 0
  | high {h} : Position h → Position (h+1)
  | low {h} : Position h → Position (h+1)

def bitAt : {h : Nat} → Position h → S.Ref h → Bool
  | _, .here, a => S.read a
  | _, .high p, a => bitAt p (S.split a).1
  | _, .low p, a => bitAt p (S.split a).2

theorem bitAt_filled {h} (p : Position h) (b : Bool) : bitAt S p (filled S h b) = b := by
  induction p with
  | here => exact S.read_leaf b
  | high p ih => simpa [filled, bitAt, S.split_join] using ih
  | low p ih => simpa [filled, bitAt, S.split_join] using ih

/-- Does the second position lie at or before the cut? -/
def retained : {h : Nat} → Position h → Position h → Bool
  | _, .here, .here => true
  | _, .high p, .high q => retained p q
  | _, .high _, .low _ => false
  | _, .low _, .high _ => true
  | _, .low p, .low q => retained p q

/-- Clear the suffix strictly after the given position, interning one new
node per level. -/
def truncate (U : Uniform S) : {h : Nat} → Position h → S.Ref h → S.Ref h × Nat
  | _, .here, a => (a, 0)
  | _, @Position.high h p, a =>
    let t := truncate U p (S.split a).1
    (S.join t.1 (U.get h false), t.2+3)
  | _, .low p, a =>
    let x := S.split a
    let t := truncate U p x.2
    (S.join x.1 t.1, t.2+2)

theorem truncate_correct (U : Uniform S) {h} (p q : Position h) (a : S.Ref h) :
    bitAt S q (truncate S U p a).1 = (retained p q && bitAt S q a) := by
  induction p with
  | here => cases q; rfl
  | high p ih =>
    cases q <;> simp [retained, truncate, bitAt, S.split_join, U.correct, bitAt_filled, ih]
  | low p ih =>
    cases q <;> simp [retained, truncate, bitAt, S.split_join, ih]

theorem truncate_work (U : Uniform S) {h} (p : Position h) (a : S.Ref h) :
    (truncate S U p a).2 ≤ 3*h := by
  induction p with
  | here => exact Nat.le_refl 0
  | high p ih =>
    simp only [truncate, Nat.mul_succ]
    have := ih (S.split a).1
    omega
  | low p ih =>
    simp only [truncate, Nat.mul_succ]
    have := ih (S.split a).2
    omega

@[simp] theorem value_join {h} (l r : S.Ref h) :
    value S (h+1) (S.join l r) = value S h l * radix h + value S h r := by
  simp [value, S.split_join]

@[simp] theorem value_zero (h : Nat) : value S h (filled S h false) = 0 := by
  induction h with
  | zero => simp [filled, value, S.read_leaf]
  | succ h ih => simp [filled, ih]

theorem value_ones (h : Nat) : value S h (filled S h true) + 1 = radix h := by
  induction h with
  | zero => simp [filled, value, radix, S.read_leaf]
  | succ h ih =>
    simp only [filled, value_join, radix]
    rw [Nat.add_assoc, ih, ← Nat.succ_mul]
    exact congrArg (· * radix h) ih

/-- Increase a block by one, wrapping on overflow. A whole suffix of ones is
cleared by replacing one reference. Only one child is visited at each level. -/
def bump (U : Uniform S) : (h : Nat) → S.Ref h → S.Ref h × Nat
  | 0, a => (S.leaf (!S.read a), 2)
  | h+1, a =>
    let x := S.split a
    if S.same x.2 (U.get h true) then
      let t := bump U h x.1
      (S.join t.1 (U.get h false), t.2+5)
    else
      let t := bump U h x.2
      (S.join x.1 t.1, t.2+4)

theorem bump_of_ne_ones (U : Uniform S) (h : Nat) (a : S.Ref h)
    (ha : a ≠ filled S h true) :
    value S h (bump S U h a).1 = value S h a + 1 := by
  induction h with
  | zero =>
    cases e : S.read a with
    | false => simp [bump, value, e, S.read_leaf]
    | true => exact False.elim (ha (by rw [← S.leaf_read a, e]; rfl))
  | succ h ih =>
    by_cases e : S.same (S.split a).2 (U.get h true) = true
    · have hr := (S.same_iff _ _).mp e
      rw [U.correct] at hr
      have hl : (S.split a).1 ≠ filled S h true := by
        intro he
        apply ha
        rw [← S.join_split a, he, hr]
        rfl
      simp only [bump, if_pos e, value_join]
      rw [U.correct, value_zero, Nat.add_zero]
      change _ = value S h (S.split a).1 * radix h + value S h (S.split a).2 + 1
      rw [ih _ hl, Nat.add_mul, Nat.one_mul, hr, Nat.add_assoc, value_ones]
    · have hr : (S.split a).2 ≠ filled S h true := by
        intro hr
        exact e ((S.same_iff _ _).mpr (by rw [U.correct, hr]))
      simp only [bump, if_neg e, value_join, ih _ hr]
      change _ = value S h (S.split a).1 * radix h + value S h (S.split a).2 + 1
      omega

theorem bump_work (U : Uniform S) (h : Nat) (a : S.Ref h) :
    (bump S U h a).2 ≤ 5*h+2 := by
  induction h with
  | zero => exact Nat.le_refl _
  | succ h ih =>
    simp only [bump]
    split
    · have := ih (S.split a).1
      omega
    · have := ih (S.split a).2
      omega

/-- The weight of one unit in the addressed bit, counting from the right. -/
def weight : {h : Nat} → Position h → Nat
  | _, .here => 1
  | _, @Position.high h p => weight p * radix h
  | _, .low p => weight p

structure Addition (S : Store) (h : Nat) where
  result : S.Ref h
  carry : Bool
  work : Nat

/-- Add a power of two and return overflow. A carry from the low half either
clears an all-one high half immediately, or ends after a single call to
`bump` on a non-full block. -/
def addUnit (U : Uniform S) : {h : Nat} → Position h → S.Ref h → Addition S h
  | _, .here, a =>
    let b := S.read a
    ⟨S.leaf (!b), b, 2⟩
  | _, .high p, a =>
    let x := S.split a
    let t := addUnit U p x.1
    ⟨S.join t.result x.2, t.carry, t.work+2⟩
  | _, @Position.low h p, a =>
    let x := S.split a
    let t := addUnit U p x.2
    if t.carry then
      if S.same x.1 (U.get h true) then
        ⟨S.join (U.get h false) t.result, true, t.work+5⟩
      else
        let z := bump S U h x.1
        ⟨S.join z.1 t.result, false, t.work+z.2+4⟩
    else ⟨S.join x.1 t.result, false, t.work+2⟩

theorem addUnit_correct (U : Uniform S) {h} (p : Position h) (a : S.Ref h) :
    value S h (addUnit S U p a).result +
      (if (addUnit S U p a).carry then radix h else 0) = value S h a + weight p := by
  induction p with
  | here => cases e : S.read a <;> simp [addUnit, value, radix, weight, e, S.read_leaf]
  | @high h p ih =>
    have H := ih (S.split a).1
    have E := congrArg (· * radix h) H
    simp only [Nat.add_mul] at E
    cases e : (addUnit S U p (S.split a).1).carry <;>
      simp [addUnit, value, S.split_join, weight, radix, e] at E ⊢ <;> omega
  | @low h p ih =>
    have H := ih (S.split a).2
    cases e : (addUnit S U p (S.split a).2).carry with
    | false =>
      simp [e] at H
      simp [addUnit, e, value, S.split_join, weight, H, Nat.add_assoc]
    | true =>
      simp [e] at H
      by_cases f : S.same (S.split a).1 (U.get h true) = true
      · have hf := (S.same_iff _ _).mp f
        rw [U.correct] at hf
        have F := congrArg (· * radix h) (value_ones S h)
        simp only [Nat.add_mul, Nat.one_mul] at F
        simp only [addUnit, e, f, if_true, value_join]
        simp [U.correct, value, weight, radix, hf] <;> omega
      · have hn : (S.split a).1 ≠ filled S h true := by
          intro he
          exact f ((S.same_iff _ _).mpr (by rw [U.correct, he]))
        have hb := bump_of_ne_ones S U h (S.split a).1 hn
        simp [addUnit, e, f, value, S.split_join, weight, hb, Nat.add_mul] <;> omega

/-- At most one nontrivial carry propagation takes place. If the result
carries out of this block, none of its ancestor calls to `bump` was needed. -/
theorem addUnit_work (U : Uniform S) {h} (p : Position h) (a : S.Ref h) :
    (addUnit S U p a).work ≤ 10*h+2 ∧
      ((addUnit S U p a).carry = true → (addUnit S U p a).work ≤ 5*h+2) := by
  induction p with
  | here => simp [addUnit]
  | @high h p ih =>
    obtain ⟨H, C⟩ := ih (S.split a).1
    simp only [addUnit]
    constructor
    · omega
    · intro c
      have := C c
      omega
  | @low h p ih =>
    obtain ⟨H, C⟩ := ih (S.split a).2
    cases e : (addUnit S U p (S.split a).2).carry with
    | false => simp [addUnit, e] <;> omega
    | true =>
      have := C e
      have := bump_work S U h (S.split a).1
      by_cases f : S.same (S.split a).1 (U.get h true) = true <;>
        simp [addUnit, e, f] <;> omega

/-- Height and two child addresses, most significant half first. -/
abbrev Key := Nat × Nat × Nat

attribute [local instance] lexOrd

/-- The forward and inverse indices are balanced search trees. Addresses 0
and 1 are reserved for the leaf bits. The inverse index avoids resizing a
contiguous array on the worst-case insertion. -/
structure Heap where
  next : Nat
  address : Std.TreeMap Key Nat
  record : Std.TreeMap Nat Key

def Heap.empty : Heap := ⟨2, ∅, ∅⟩

structure Heap.Valid (H : Heap) : Prop where
  inverse : ∀ (k : Key) (i : Nat), H.address[k]? = some i ↔ H.record[i]? = some k
  bounds : ∀ (i : Nat) (k : Key), H.record[i]? = some k → 2 ≤ i ∧ i < H.next
  reserved : 2 ≤ H.next
  address_size : H.address.size ≤ H.next
  record_size : H.record.size ≤ H.next

theorem Heap.empty_valid : Heap.empty.Valid := by
  constructor <;> simp [Heap.empty]

def Heap.intern (H : Heap) (k : Key) : Heap × Nat :=
  match H.address[k]? with
  | some i => (H, i)
  | none => (⟨H.next+1, H.address.insert k H.next, H.record.insert H.next k⟩, H.next)

theorem Heap.intern_valid (H : Heap) (hv : H.Valid) (k : Key) : (H.intern k).1.Valid := by
  cases e : H.address[k]? with
  | some i => simpa [intern, e] using hv
  | none =>
    simp only [intern, e]
    have hn : H.record[H.next]? = none := by
      cases g : H.record[H.next]? with
      | none => rfl
      | some j => have := hv.bounds _ _ g; omega
    constructor
    · intro j i
      simp only [Std.TreeMap.getElem?_insert]
      by_cases kj : k = j <;> by_cases ni : H.next = i
      · subst j; subst i; simp
      · subst j; simp [ni]
        intro eq
        have := (hv.inverse k i).2 eq
        simp [e] at this
      · subst i; simp [kj]
        intro eq
        have := (hv.inverse j H.next).1 eq
        simp [hn] at this
      · simpa [kj, ni] using hv.inverse j i
    · intro i j g
      by_cases ni : H.next = i
      · subst i; exact ⟨hv.reserved, Nat.lt_succ_self _⟩
      · simp [Std.TreeMap.getElem?_insert, ni] at g
        obtain ⟨lo, hi⟩ := hv.bounds _ _ g
        exact ⟨lo, Nat.lt_succ_of_lt hi⟩
    · exact Nat.le_succ_of_le hv.reserved
    · exact Nat.le_trans Std.TreeMap.size_insert_le (Nat.add_le_add_right hv.address_size 1)
    · exact Nat.le_trans Std.TreeMap.size_insert_le (Nat.add_le_add_right hv.record_size 1)

theorem Heap.intern_record (H : Heap) (hv : H.Valid) (k : Key) :
    (H.intern k).1.record[(H.intern k).2]? = some k := by
  cases e : H.address[k]? with
  | some i => simpa [intern, e] using (hv.inverse _ _).1 e
  | none => simp [intern, e]

/-- Persistence: interning a pair leaves every allocated record readable
at its old address. -/
theorem Heap.intern_preserves (H : Heap) (hv : H.Valid) (k j : Key) (i : Nat)
    (hi : H.record[i]? = some j) : (H.intern k).1.record[i]? = some j := by
  cases e : H.address[k]? with
  | some i => simpa [intern, e] using hi
  | none =>
    have := (hv.bounds _ _ hi).2
    have ne : H.next ≠ i := by omega
    simp [intern, e, Std.TreeMap.getElem?_insert, ne, hi]

theorem Heap.intern_growth (H : Heap) (hv : H.Valid) (k : Key) :
    (H.intern k).1.next ≤ H.next+1 ∧ (H.intern k).2 < (H.intern k).1.next := by
  cases e : H.address[k]? with
  | none => simp [intern, e]
  | some i =>
    have hi := (hv.bounds _ _ ((hv.inverse _ _).1 e)).2
    simp [intern, e, hi]

/-- An allocated address represents its two children's concatenation. At
height zero, the addresses of the two bits are fixed. -/
inductive Represents (S : Store) (H : Heap) : {h : Nat} → Nat → S.Ref h → Prop
  | leaf (b : Bool) : Represents S H b.toNat (S.leaf b)
  | node {h i l r} {a b : S.Ref h} :
    H.record[i]? = some (h+1, l, r) →
    Represents S H l a → Represents S H r b → Represents S H i (S.join a b)

/-- Old block values survive a call to the concrete interner. -/
theorem Represents.persist {S : Store} {H : Heap} {h i} {a : S.Ref h}
    (r : Represents S H i a) (hv : H.Valid) (k : Key) :
    Represents S (H.intern k).1 i a := by
  induction r with
  | leaf b => exact .leaf b
  | node g _ _ il ir => exact .node (H.intern_preserves hv _ _ _ g) il ir

theorem Represents.intern_join {S : Store} {H : Heap} {h l r} {a b : S.Ref h}
    (hv : H.Valid) (left : Represents S H l a) (right : Represents S H r b) :
    Represents S (H.intern (h+1, l, r)).1 (H.intern (h+1, l, r)).2 (S.join a b) :=
  .node (H.intern_record hv _) (left.persist hv _) (right.persist hv _)

private theorem rep_leaf {H : Heap} {i} {a : S.Ref 0} (r : Represents S H i a) :
    i = (S.read a).toNat := by
  cases r with | leaf b => simp [S.read_leaf]

def Heap.children (H : Heap) (i : Nat) : Nat × Nat :=
  ((H.record[i]?).getD (0, 0, 0)).2

private theorem rep_node {H : Heap} {h i} {a : S.Ref (h+1)} (r : Represents S H i a) :
    H.record[i]? = some (h+1, H.children i) ∧
    Represents S H (H.children i).1 (S.split a).1 ∧
    Represents S H (H.children i).2 (S.split a).2 := by
  cases r with
  | node g l r => simpa [Heap.children, g, S.split_join] using And.intro g (And.intro l r)

/-- Exact equality of addresses is equivalent to equality of the entire
represented bit block, at every reachable height. -/
theorem Represents.same_iff {S : Store} {H : Heap} (hv : H.Valid) {h i j} {a b : S.Ref h}
    (x : Represents S H i a) (y : Represents S H j b) : i = j ↔ a = b := by
  induction h generalizing i j with
  | zero =>
    rw [rep_leaf S x, rep_leaf S y]
    constructor
    · intro he
      have hb : S.read a = S.read b := by
        cases ea : S.read a <;> cases eb : S.read b <;> simp_all
      rw [← S.leaf_read a, ← S.leaf_read b, hb]
    · rintro rfl; rfl
  | succ h ih =>
    obtain ⟨xi, xl, xr⟩ := rep_node S x
    obtain ⟨yj, yl, yr⟩ := rep_node S y
    constructor
    · rintro rfl
      have hl := (ih xl yl).1 rfl
      have hr := (ih xr yr).1 rfl
      calc
        a = S.join (S.split a).1 (S.split a).2 := (S.join_split a).symm
        _ = S.join (S.split b).1 (S.split b).2 := by rw [hl, hr]
        _ = b := S.join_split b
    · rintro rfl
      have hl := (ih xl yl).2 rfl
      have hr := (ih xr yr).2 rfl
      have he : H.children i = H.children j := Prod.ext hl hr
      have ai := (hv.inverse _ _).2 xi
      have aj := (hv.inverse _ _).2 yj
      rw [he, aj] at ai
      simpa using ai.symm

/-- Read-only comparison on concrete addresses, with the same primitive
charges as `less`. -/
def Heap.lessAddr (H : Heap) : Nat → Nat → Nat → Bool × Nat
  | 0, a, b => (decide (a < b), 2)
  | h+1, a, b =>
    let x := H.children a
    let y := H.children b
    let t := if x.1 = y.1 then H.lessAddr h x.2 y.2 else H.lessAddr h x.1 y.1
    (t.1, t.2+3)

theorem Heap.lessAddr_refines {H : Heap} (hv : H.Valid) {h i j} {a b : S.Ref h}
    (x : Represents S H i a) (y : Represents S H j b) :
    H.lessAddr h i j = less S h a b := by
  induction h generalizing i j with
  | zero =>
    rw [rep_leaf S x, rep_leaf S y]
    cases ea : S.read a <;> cases eb : S.read b <;> simp [lessAddr, less, ea, eb]
  | succ h ih =>
    obtain ⟨_, xl, xr⟩ := rep_node S x
    obtain ⟨_, yl, yr⟩ := rep_node S y
    have e := (xl.same_iff hv yl)
    have es := S.same_iff (S.split a).1 (S.split b).1
    by_cases eq : (H.children i).1 = (H.children j).1
    · simp [lessAddr, less, eq, es.2 (e.1 eq), ih xr yr]
    · have ne : ¬ S.same (S.split a).1 (S.split b).1 = true := fun hsame => eq (e.2 (es.1 hsame))
      simp [lessAddr, less, eq, ne, ih xl yl]

/-- Every positively tagged record represents a block of its declared height. -/
def Heap.Typed (H : Heap) : Prop :=
  ∀ (S : Store) (h i l r : Nat), H.record[i]? = some (h+1,l,r) →
    ∃ a : S.Ref (h+1), Represents S H i a

theorem Heap.empty_typed : Heap.empty.Typed := by
  intro S h i l r e
  simp [empty] at e

theorem Represents.transfer {S : Store} (T : Store) {H : Heap} {h i} {a : S.Ref h}
    (r : Represents S H i a) : ∃ b : T.Ref h, Represents T H i b := by
  induction r with
  | leaf b => exact ⟨_, .leaf b⟩
  | node g _ _ il ir =>
    obtain ⟨_, l⟩ := il
    obtain ⟨_, r⟩ := ir
    exact ⟨_, .node g l r⟩

private theorem intern_typed {S : Store} {H : Heap} {h l r} {a b : S.Ref h}
    (hv : H.Valid) (ht : H.Typed) (left : Represents S H l a) (right : Represents S H r b) :
    (H.intern (h+1,l,r)).1.Typed := by
  intro T d i x y g
  let k : Key := (h+1,l,r)
  change (H.intern k).1.record[i]? = some (d+1,x,y) at g
  cases e : H.address[k]? with
  | some j =>
    have old : H.record[i]? = some (d+1,x,y) := by simpa [Heap.intern, e] using g
    obtain ⟨v, rep⟩ := ht T d i x y old
    exact ⟨v, rep.persist hv k⟩
  | none =>
    by_cases ni : H.next = i
    · subst i
      have key : k = (d+1,x,y) := by simpa [Heap.intern, e] using g
      obtain rfl : h = d := Nat.succ.inj (congrArg Prod.fst key)
      obtain ⟨l', rl⟩ := left.transfer T
      obtain ⟨r', rr⟩ := right.transfer T
      have result := rl.intern_join hv rr
      have pos : (H.intern k).2 = H.next := by simp [Heap.intern, e]
      exact ⟨_, pos ▸ result⟩
    · have old : H.record[i]? = some (d+1,x,y) := by
        simpa [Heap.intern, e, Std.TreeMap.getElem?_insert, ni] using g
      obtain ⟨v, rep⟩ := ht T d i x y old
      exact ⟨v, rep.persist hv k⟩

/-- Monotone growth of the concrete heap, including preservation of tags. -/
structure Heap.Extends (H' H : Heap) : Prop where
  records : ∀ (i : Nat) (k : Key), H.record[i]? = some k → H'.record[i]? = some k
  typed : H.Typed → H'.Typed

theorem Heap.Extends.refl (H : Heap) : H.Extends H := ⟨fun _ _ h => h, id⟩

theorem Heap.Extends.trans {A B C : Heap} (bc : C.Extends B) (ab : B.Extends A) :
    C.Extends A := ⟨fun _ _ h => bc.records _ _ (ab.records _ _ h), fun t => bc.typed (ab.typed t)⟩

theorem Represents.lift {S : Store} {H H' : Heap} {h i} {a : S.Ref h}
    (r : Represents S H i a) (extends_ : H'.Extends H) : Represents S H' i a := by
  induction r with
  | leaf b => exact .leaf b
  | node g _ _ il ir => exact .node (extends_.records _ _ g) il ir

/-- A runtime address tagged, in the proof, with the block it represents. -/
structure Cell (S : Store) (H : Heap) {h : Nat} (a : S.Ref h) where
  addr : Nat
  rep : Represents S H addr a

variable {S} {H H' : Heap} {h : Nat}

def Cell.lift {a : S.Ref h} (c : Cell S H a) (e : H'.Extends H) : Cell S H' a :=
  ⟨c.addr, c.rep.lift e⟩

def Cell.left {a : S.Ref (h+1)} (c : Cell S H a) : Cell S H (S.split a).1 :=
  ⟨(H.children c.addr).1, (rep_node S c.rep).2.1⟩

def Cell.right {a : S.Ref (h+1)} (c : Cell S H a) : Cell S H (S.split a).2 :=
  ⟨(H.children c.addr).2, (rep_node S c.rep).2.2⟩

/-- The concrete result of a persistent operation. Only the heap and the
allocated address carry runtime data. -/
structure Write (S : Store) (H : Heap) {h : Nat} (a : S.Ref h) where
  heap : Heap
  valid : heap.Valid
  growth : heap.Extends H
  cell : Cell S heap a

def Write.unchanged {a : S.Ref h} (v : H.Valid) (c : Cell S H a) : Write S H a :=
  ⟨H, v, .refl H, c⟩

def Write.after {a : S.Ref h} (w : Write S H' a) (e : H'.Extends H) :
    Write S H a := ⟨w.heap, w.valid, w.growth.trans e, w.cell⟩

def Cell.join {a b : S.Ref h} (v : H.Valid) (l : Cell S H a) (r : Cell S H b) :
    Write S H (S.join a b) :=
  let k := (h+1, l.addr, r.addr)
  let t := H.intern k
  ⟨t.1, H.intern_valid v k,
    ⟨fun i j e => H.intern_preserves v k j i e, fun ht => intern_typed v ht l.rep r.rep⟩,
    ⟨t.2, l.rep.intern_join v r.rep⟩⟩

/-- A bounded table of uniform references. -/
structure Cached (S : Store) (H : Heap) (height : Nat) where
  lookup : Nat → Bool → Nat
  spec : ∀ {d}, d ≤ height → ∀ b, Represents S H (lookup d b) (filled S d b)

def Cached.lift {height} (c : Cached S H height) (e : H'.Extends H) :
    Cached S H' height := ⟨c.lookup, fun d b => (c.spec d b).lift e⟩

def Cached.cell {height d} (c : Cached S H height) (hd : d ≤ height) (b : Bool) :
    Cell S H (filled S d b) := ⟨_, c.spec hd b⟩

/-- The mathematical lookup table used in the specification. -/
def uniformSpec (S : Store) : Uniform S := ⟨filled S, fun _ _ => rfl⟩

@[simp] theorem uniformSpec_get (S : Store) (h : Nat) (b : Bool) :
    (uniformSpec S).get h b = filled S h b := rfl

/-- Truncate on actual heap addresses. The dependent return type proves
that the address returned in the extended heap denotes the specified block. -/
def truncateAddr {cap} (v : H.Valid) (cache : Cached S H cap) : {h : Nat} → (p : Position h) →
    h ≤ cap → {a : S.Ref h} → Cell S H a → Write S H (truncate S (uniformSpec S) p a).1
  | _, .here, _, _, c => .unchanged v c
  | _, @Position.high d p, hd, _, c =>
    let hd' := Nat.le_trans (Nat.le_succ d) hd
    let x := truncateAddr v cache p hd' c.left
    let z := (cache.cell hd' false).lift x.growth
    (x.cell.join x.valid z).after x.growth
  | _, @Position.low d p, hd, _, c =>
    let hd' := Nat.le_trans (Nat.le_succ d) hd
    let x := truncateAddr v cache p hd' c.right
    ((c.left.lift x.growth).join x.valid x.cell).after x.growth

private def Write.cast {a b : S.Ref h} (w : Write S H a) (e : a = b) : Write S H b :=
  ⟨w.heap, w.valid, w.growth, ⟨w.cell.addr, e ▸ w.cell.rep⟩⟩

def Cell.bit {a : S.Ref 0} (c : Cell S H a) : Bool := c.addr != 0

private theorem Cell.bit_eq {a : S.Ref 0} (c : Cell S H a) : c.bit = S.read a := by
  simp only [Cell.bit, rep_leaf S c.rep]
  cases S.read a <;> decide

def Cell.flipped {a : S.Ref 0} (c : Cell S H a) : Cell S H (S.leaf (!S.read a)) :=
  ⟨(!c.bit).toNat, by rw [c.bit_eq]; exact .leaf _⟩

/-- Concrete carry propagation. All tests use word addresses. -/
def bumpAddr {cap} (v : H.Valid) (cache : Cached S H cap) :
    (h : Nat) → h ≤ cap → {a : S.Ref h} → Cell S H a →
      Write S H (bump S (uniformSpec S) h a).1
  | 0, _, _, c => .unchanged v c.flipped
  | h+1, hd, _, c =>
    let h' := Nat.le_trans (Nat.le_succ h) hd
    let o := cache.cell h' true
    if e : c.right.addr = o.addr then
      let x := bumpAddr v cache h h' c.left
      let z := (cache.cell h' false).lift x.growth
      ((x.cell.join x.valid z).after x.growth).cast (by
        have f := (S.same_iff _ _).2 ((c.right.rep.same_iff v o.rep).1 e)
        simp [bump, f])
    else
      let x := bumpAddr v cache h h' c.right
      (((c.left.lift x.growth).join x.valid x.cell).after x.growth).cast (by
        have f : S.same _ _ ≠ true := fun eq =>
          e ((c.right.rep.same_iff v o.rep).2 ((S.same_iff _ _).1 eq))
        simp [bump, f])

structure AddWrite (S : Store) (H : Heap) {h : Nat} (a : Addition S h) where
  out : Write S H a.result
  carry : Bool
  correct : carry = a.carry

/-- Concrete addition and overflow on the interning heap. Only cells on the
address path and the first non-full carry branch are rebuilt. -/
def addUnitAddr {cap} (v : H.Valid) (cache : Cached S H cap) :
    {h : Nat} → (p : Position h) → h ≤ cap → {a : S.Ref h} → Cell S H a →
      AddWrite S H (addUnit S (uniformSpec S) p a)
  | _, .here, _, _, c => ⟨.unchanged v c.flipped, c.bit, c.bit_eq⟩
  | _, @Position.high d p, hd, _, c =>
    let hd' := Nat.le_trans (Nat.le_succ d) hd
    let t := addUnitAddr v cache p hd' c.left
    let r := c.right.lift t.out.growth
    ⟨(t.out.cell.join t.out.valid r).after t.out.growth, t.carry, t.correct⟩
  | _, @Position.low d p, hd, _, c =>
    let hd' := Nat.le_trans (Nat.le_succ d) hd
    let t := addUnitAddr v cache p hd' c.right
    let l := c.left.lift t.out.growth
    if e : t.carry = true then
      let o := cache.cell hd' true
      if f : c.left.addr = o.addr then
        let z := (cache.cell hd' false).lift t.out.growth
        let out := (z.join t.out.valid t.out.cell).after t.out.growth
        have ce := t.correct.symm.trans e
        have le := (S.same_iff _ _).2 ((c.left.rep.same_iff v o.rep).1 f)
        ⟨out.cast (by simp [addUnit, ce, le]),
          true, by simp [addUnit, ce, le]⟩
      else
        let x := bumpAddr t.out.valid (cache.lift t.out.growth) d hd' l
        let out := (x.cell.join x.valid (t.out.cell.lift x.growth)).after
          (x.growth.trans t.out.growth)
        have ce := t.correct.symm.trans e
        have le : S.same _ _ ≠ true := fun eq =>
          f ((c.left.rep.same_iff v o.rep).2 ((S.same_iff _ _).1 eq))
        ⟨out.cast (by simp [addUnit, ce, le]),
          false, by simp [addUnit, ce, le]⟩
    else
      let out := (l.join t.out.valid t.out.cell).after t.out.growth
      have ce : (addUnit S (uniformSpec S) p _).carry ≠ true := fun eq =>
        e (t.correct.trans eq)
      ⟨out.cast (by simp only [addUnit, if_neg ce]), false, by simp only [addUnit, if_neg ce]⟩

/-- The uniform-reference table has one zero and one all-ones entry per
height. Its initialization performs exactly two interning calls per level. -/
structure Initialized (S : Store) (cap : Nat) where
  heap : Heap
  valid : heap.Valid
  typed : heap.Typed
  table : Array (Nat × Nat)
  size : table.size = cap + 1
  rep : ∀ d, d ≤ cap → ∀ b : Bool, Represents S heap
    (if b then table[d]!.2 else table[d]!.1) (filled S d b)
  allocated : heap.next ≤ 2*cap+2

def initializeCache (S : Store) : (cap : Nat) → Initialized S cap
  | 0 =>
    ⟨Heap.empty, Heap.empty_valid, Heap.empty_typed, #[(0,1)], rfl,
      by
        intro d hd b
        obtain rfl : d = 0 := by omega
        cases b with
        | false => simpa [filled] using Represents.leaf (S := S) (H := Heap.empty) false
        | true => simpa [filled] using Represents.leaf (S := S) (H := Heap.empty) true,
      by decide⟩
  | d+1 =>
    let prev := initializeCache S d
    let zz := prev.table[d]!.1
    let oo := prev.table[d]!.2
    let zeroKey : Key := (d+1, zz, zz)
    let onesKey : Key := (d+1, oo, oo)
    let z := prev.heap.intern zeroKey
    let H := z.1.intern onesKey
    have zv := prev.heap.intern_valid prev.valid zeroKey
    have pz : Represents S prev.heap zz (filled S d false) := prev.rep d (by omega) false
    have po : Represents S prev.heap oo (filled S d true) := prev.rep d (by omega) true
    have ht := intern_typed prev.valid prev.typed pz pz
    have ho := po.persist prev.valid zeroKey
    ⟨H.1, z.1.intern_valid zv onesKey, intern_typed zv ht ho ho, prev.table.push (z.2, H.2),
      by simp [prev.size],
      by
        intro k hk b
        by_cases eq : k = d+1
        · subst k
          have T : (prev.table.push (z.2, H.2))[d+1]! = (z.2,H.2) := by
            rw [← prev.size]; simp
          rw [T]
          cases b with
          | false => exact (pz.intern_join prev.valid pz).persist zv onesKey
          | true => exact (po.persist prev.valid zeroKey).intern_join zv (po.persist prev.valid zeroKey)
        · have kd : k ≤ d := by omega
          have ks : k < prev.table.size := by rw [prev.size]; omega
          have T : (prev.table.push (z.2, H.2))[k]! = prev.table[k]! := by
            rw [getElem!_pos (prev.table.push (z.2, H.2)) k (by simpa using Nat.lt_succ_of_lt ks),
              getElem!_pos prev.table k ks]
            exact Array.getElem_push_lt ks
          rw [T]
          exact ((prev.rep k kd b).persist prev.valid zeroKey).persist zv onesKey,
      by
        have h₁ := (prev.heap.intern_growth prev.valid zeroKey).1
        have h₂ := (z.1.intern_growth zv onesKey).1
        have h₃ := prev.allocated
        change H.1.next ≤ 2*(d+1)+2
        change H.1.next ≤ z.1.next+1 at h₂
        change z.1.next ≤ prev.heap.next+1 at h₁
        omega⟩

def Initialized.cache {cap} (I : Initialized S cap) : Cached S I.heap cap :=
  ⟨fun d b => if b then I.table[d]!.2 else I.table[d]!.1, fun hd b => I.rep _ hd b⟩

/-- Index of a bit counted from the right, starting at zero. -/
def place : {h : Nat} → Position h → Nat
  | _, .here => 0
  | _, @Position.high d p => place p + 2^d
  | _, .low p => place p

def atBit : (h i : Nat) → Position h
  | 0, _ => .here
  | d+1, i =>
    let w := 1 <<< d
    if i < w then .low (atBit d i) else .high (atBit d (i-w))

theorem place_atBit (h i : Nat) (hi : i < 2^h) : place (atBit h i) = i := by
  induction h generalizing i with
  | zero => simp [place, atBit]; simpa [eq_comm] using hi
  | succ h ih =>
    rw [Nat.pow_succ] at hi
    by_cases hw : i < 2^h
    · simp [atBit, Nat.shiftLeft_eq, hw, place, ih _ hw]
    · have hu : i-2^h < 2^h := by omega
      simp [atBit, Nat.shiftLeft_eq, hw, place, ih _ hu]
      omega

theorem radix_eq (h : Nat) : radix h = 2^(2^h) := by
  induction h with
  | zero => rfl
  | succ h ih => simp [radix, ih, Nat.pow_succ, Nat.mul_two, Nat.pow_add]

theorem weight_eq {h} (p : Position h) : weight p = 2^(place p) := by
  induction p with
  | here => rfl
  | high p ih => simp [place, weight, ih, radix_eq, Nat.pow_add]
  | low p ih => exact ih

theorem weight_dvd_radix {h} (p : Position h) : weight p ∣ radix h := by
  induction p with
  | here => exact ⟨2, rfl⟩
  | @high h p ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k, ?_⟩
    change radix h * radix h = weight p * radix h * k
    calc radix h * radix h = (weight p*k) * radix h := congrArg (· * radix h) hk
         _ = _ := by ac_rfl
  | @low h p ih => exact Nat.dvd_trans ih (Nat.dvd_mul_right (radix h) _)

/-- The quotient and remainder of truncation, as statements about full integer
values. This supplies the bridge from address-based copying to the anchor formula. -/
theorem truncate_division (S : Store) (U : Uniform S) {h} (p : Position h) (a : S.Ref h) :
    ∃ q r, value S h (truncate S U p a).1 = weight p * q ∧
      value S h a = value S h (truncate S U p a).1 + r ∧ r < weight p := by
  induction p with
  | here => exact ⟨value S 0 a, 0, by simp [truncate, weight], rfl, by decide⟩
  | @high h p ih =>
    obtain ⟨q, r, hq, hr, hlt⟩ := ih (S.split a).1
    refine ⟨q, r*radix h + value S h (S.split a).2, ?_, ?_, ?_⟩
    · simp [truncate, weight, U.correct, hq]
      ac_rfl
    · change value S h (S.split a).1 * _ + _ = _
      simp [truncate, U.correct, hr, Nat.add_mul, Nat.add_assoc]
    · simpa [weight] using high_lt (d := 0) hlt (value_lt S h (S.split a).2)
  | @low h p ih =>
    obtain ⟨q, r, hq, hr, hlt⟩ := ih (S.split a).2
    obtain ⟨k, hk⟩ := weight_dvd_radix p
    refine ⟨value S h (S.split a).1 * k + q, r, ?_, ?_, hlt⟩
    · simp [truncate, weight, hq, hk, Nat.mul_add]; ac_rfl
    · change value S h (S.split a).1 * _ + _ = _
      simp [truncate, hr, Nat.add_assoc]

theorem value_truncate (S : Store) (U : Uniform S) {h} (p : Position h) (a : S.Ref h) :
    value S h (truncate S U p a).1 = value S h a / weight p * weight p := by
  obtain ⟨q, r, hq, hr, hl⟩ := truncate_division S U p a
  have w : 0 < weight p := by omega
  rw [hr, hq, Nat.mul_add_div w, Nat.div_eq_of_lt hl, Nat.add_zero, Nat.mul_comm]

structure Advanced (S : Store) (h : Nat) where
  result : S.Ref h
  wraps : Nat
  work : Nat

/-- Add the same unit a small number of times, tracking overflow exactly. -/
def advance (S : Store) (U : Uniform S) {h} (p : Position h) (a : S.Ref h) :
    Nat → Advanced S h
  | 0 => ⟨a, 0, 0⟩
  | j+1 =>
    let t := advance S U p a j
    let z := addUnit S U p t.result
    ⟨z.result, t.wraps + z.carry.toNat, t.work + z.work⟩

theorem advance_correct (S : Store) (U : Uniform S) {h} (p : Position h) (a : S.Ref h) (j : Nat) :
    value S h (advance S U p a j).result + (advance S U p a j).wraps * radix h =
      value S h a + j * weight p := by
  induction j with
  | zero => simp [advance]
  | succ j ih =>
    have hs := addUnit_correct S U p (advance S U p a j).result
    cases e : (addUnit S U p (advance S U p a j).result).carry <;>
      simp [e, advance, Nat.add_mul] at hs ⊢ <;> omega

theorem advance_work (S : Store) (U : Uniform S) {h} (p : Position h) (a : S.Ref h) (j : Nat) :
    (advance S U p a j).work ≤ j * (10*h+2) := by
  induction j with
  | zero => simp [advance]
  | succ j ih =>
    change _ + _ ≤ (j+1) * (10*h+2)
    rw [Nat.succ_mul j]
    exact Nat.add_le_add ih (addUnit_work S U p _).1

def advanceAddr {cap} (v : H.Valid) (cache : Cached S H cap) {h} (p : Position h)
    (hd : h ≤ cap) {a : S.Ref h} (c : Cell S H a) :
    (j : Nat) → Write S H (advance S (uniformSpec S) p a j).result
  | 0 => .unchanged v c
  | j+1 =>
    let t := advanceAddr v cache p hd c j
    let z := addUnitAddr t.valid (cache.lift t.growth) p hd t.cell
    z.out.after t.growth

@[simp] private theorem after_heap {a : S.Ref h} (w : Write S H' a) (e : H'.Extends H) :
    (w.after e).heap = w.heap := rfl

@[simp] private theorem cast_heap {a b : S.Ref h} (w : Write S H a) (e : a = b) :
    (w.cast e).heap = w.heap := rfl

private theorem join_growth {a b : S.Ref h} (v : H.Valid) (l : Cell S H a) (r : Cell S H b) :
    (l.join v r).heap.next ≤ H.next + 1 := (H.intern_growth v _).1

theorem truncateAddr_growth {cap} (v : H.Valid) (cache : Cached S H cap) {h} (p : Position h)
    (hd : h ≤ cap) {a : S.Ref h} (c : Cell S H a) :
    (truncateAddr v cache p hd c).heap.next ≤ H.next + h := by
  induction p with
  | here => exact Nat.le_refl _
  | @high d p ih =>
    have d' := Nat.le_trans (Nat.le_succ d) hd
    have hrec := ih d' c.left
    let t := truncateAddr v cache p d' c.left
    have m := join_growth t.valid t.cell ((cache.cell d' false).lift t.growth)
    simp only [truncateAddr, after_heap]
    exact Nat.le_trans m (Nat.add_le_add_right hrec 1)
  | @low d p ih =>
    have d' := Nat.le_trans (Nat.le_succ d) hd
    have hrec := ih d' c.right
    let t := truncateAddr v cache p d' c.right
    have m := join_growth t.valid (c.left.lift t.growth) t.cell
    simp only [truncateAddr, after_heap]
    exact Nat.le_trans m (Nat.add_le_add_right hrec 1)

theorem bumpAddr_growth {cap} (v : H.Valid) (cache : Cached S H cap) (h : Nat)
    (hd : h ≤ cap) {a : S.Ref h} (c : Cell S H a) :
    (bumpAddr v cache h hd c).heap.next ≤ H.next + h := by
  induction h with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have d' := Nat.le_trans (Nat.le_succ d) hd
    simp only [bumpAddr]
    split
    · let t := bumpAddr v cache d d' c.left
      have m := join_growth t.valid t.cell ((cache.cell d' false).lift t.growth)
      exact Nat.le_trans m (Nat.add_le_add_right (ih d' c.left) 1)
    · let t := bumpAddr v cache d d' c.right
      have m := join_growth t.valid (c.left.lift t.growth) t.cell
      exact Nat.le_trans m (Nat.add_le_add_right (ih d' c.right) 1)

theorem addUnitAddr_growth {cap} (v : H.Valid) (cache : Cached S H cap) {h} (p : Position h)
    (hd : h ≤ cap) {a : S.Ref h} (c : Cell S H a) :
    let t := addUnitAddr v cache p hd c
    t.out.heap.next ≤ H.next + 2*h ∧ (t.carry = true → t.out.heap.next ≤ H.next + h) := by
  induction p with
  | here => exact ⟨Nat.le_refl _, fun _ => Nat.le_refl _⟩
  | @high d p ih =>
    have d' := Nat.le_trans (Nat.le_succ d) hd
    let t := addUnitAddr v cache p d' c.left
    obtain ⟨a,b⟩ := ih d' c.left
    have m := join_growth t.out.valid t.out.cell (c.right.lift t.out.growth)
    change t.out.heap.next ≤ H.next+2*d at a
    change (t.carry = true → t.out.heap.next ≤ H.next+d) at b
    refine ⟨Nat.le_trans m (by omega), fun e => Nat.le_trans m ?_⟩
    have := b e
    omega
  | @low d p ih =>
    have d' := Nat.le_trans (Nat.le_succ d) hd
    let t := addUnitAddr v cache p d' c.right
    obtain ⟨a,b⟩ := ih d' c.right
    change t.out.heap.next ≤ H.next+2*d at a
    change (t.carry = true → t.out.heap.next ≤ H.next+d) at b
    simp only [addUnitAddr]
    split
    next e =>
      have e' := b e
      split
      · have m := join_growth t.out.valid ((cache.cell d' false).lift t.out.growth) t.out.cell
        exact ⟨Nat.le_trans m (by omega), fun _ => Nat.le_trans m (by omega)⟩
      · let x := bumpAddr t.out.valid (cache.lift t.out.growth) d d' (c.left.lift t.out.growth)
        have xb := bumpAddr_growth t.out.valid (cache.lift t.out.growth) d d' (c.left.lift t.out.growth)
        change x.heap.next ≤ t.out.heap.next+d at xb
        have m := join_growth x.valid x.cell (t.out.cell.lift x.growth)
        exact ⟨Nat.le_trans m (by omega), fun e => Bool.noConfusion e⟩
    next _ =>
      have m := join_growth t.out.valid (c.left.lift t.out.growth) t.out.cell
      exact ⟨Nat.le_trans m (by omega), fun e => Bool.noConfusion e⟩

theorem advanceAddr_growth {cap} (v : H.Valid) (cache : Cached S H cap) {h} (p : Position h)
    (hd : h ≤ cap) {a : S.Ref h} (c : Cell S H a) (j : Nat) :
    (advanceAddr v cache p hd c j).heap.next ≤ H.next + j*(2*h) := by
  induction j with
  | zero => simp [advanceAddr, Write.unchanged]
  | succ j ih =>
    let t := advanceAddr v cache p hd c j
    have m := (addUnitAddr_growth t.valid (cache.lift t.growth) p hd t.cell).1
    exact Nat.le_trans m (by
      change t.heap.next ≤ H.next + j*(2*h) at ih
      rw [Nat.succ_mul j]
      omega)

end SortingAdversary.Continuous.PolylogBits
