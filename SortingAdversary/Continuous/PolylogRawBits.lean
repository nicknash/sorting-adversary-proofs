import SortingAdversary.Continuous.PolylogBits

/-!
# Shared-block writes with raw address arguments

These programs take only machine addresses, an interning heap and the
uniform-block table. The simulation theorems identify their returned heaps,
addresses and carries with the typed implementations. No logical block value
is constructed at runtime.
-/

namespace SortingAdversary.Continuous.PolylogRawBits

open PolylogBits

structure Output where
  heap : Heap
  addr : Nat

def erase {S : Store} {H : Heap} {h} {a : S.Ref h} (w : Write S H a) : Output :=
  ⟨w.heap, w.cell.addr⟩

def join (H : Heap) (h i j : Nat) : Output :=
  let x := H.intern (h+1,i,j)
  ⟨x.1, x.2⟩

abbrev Table := Nat → Bool → Nat

def truncate (cache : Table) (H : Heap) : {h : Nat} → Position h → Nat → Output
  | _, .here, i => ⟨H,i⟩
  | _, @Position.high d p, i =>
    let t := truncate cache H p (H.children i).1
    join t.heap d t.addr (cache d false)
  | _, @Position.low d p, i =>
    let x := H.children i
    let t := truncate cache H p x.2
    join t.heap d x.1 t.addr

def bump (cache : Table) (H : Heap) : Nat → Nat → Output
  | 0, i => ⟨H, (!(i != 0)).toNat⟩
  | d+1, i =>
    let x := H.children i
    if x.2 = cache d true then
      let t := bump cache H d x.1
      join t.heap d t.addr (cache d false)
    else
      let t := bump cache H d x.2
      join t.heap d x.1 t.addr

def addUnit (cache : Table) (H : Heap) : {h : Nat} → Position h → Nat → Output × Bool
  | _, .here, i => (⟨H, (!(i != 0)).toNat⟩, i != 0)
  | _, @Position.high d p, i =>
    let x := H.children i
    let t := addUnit cache H p x.1
    (join t.1.heap d t.1.addr x.2, t.2)
  | _, @Position.low d p, i =>
    let x := H.children i
    let t := addUnit cache H p x.2
    if t.2 then
      if x.1 = cache d true then (join t.1.heap d (cache d false) t.1.addr, true)
      else
        let z := bump cache t.1.heap d x.1
        (join z.heap d z.addr t.1.addr, false)
    else (join t.1.heap d x.1 t.1.addr, false)

def advance (cache : Table) (H : Heap) {h} (p : Position h) (i : Nat) : Nat → Output
  | 0 => ⟨H,i⟩
  | j+1 => let t := advance cache H p i j; (addUnit cache t.heap p t.addr).1

variable {S : Store} {H : Heap} {cap h : Nat}

theorem truncate_eq (v : H.Valid) (cache : Cached S H cap) (p : Position h)
    (hd : h ≤ cap) {a : S.Ref h} (c : Cell S H a) :
    truncate cache.lookup H p c.addr = erase (truncateAddr v cache p hd c) := by
  induction p with
  | here => rfl
  | @high d p ih =>
    change join _ _ _ _ = _
    rw [show truncate cache.lookup H p (H.children c.addr).1 = _ from ih (by omega) c.left]
    rfl
  | @low d p ih =>
    change join _ _ _ _ = _
    rw [show truncate cache.lookup H p (H.children c.addr).2 = _ from ih (by omega) c.right]
    rfl

theorem bump_eq (v : H.Valid) (cache : Cached S H cap) (h : Nat)
    (hd : h ≤ cap) {a : S.Ref h} (c : Cell S H a) :
    bump cache.lookup H h c.addr = erase (bumpAddr v cache h hd c) := by
  induction h with
  | zero => simp [bump, bumpAddr, erase, Write.unchanged, Cell.flipped, Cell.bit]
  | succ d ih =>
    simp only [bump, bumpAddr]
    by_cases e : (H.children c.addr).2 = cache.lookup d true
    · have cond : c.right.addr = (cache.cell (by omega : d ≤ cap) true).addr := e
      simp only [if_pos e, dif_pos cond]
      rw [show bump cache.lookup H d (H.children c.addr).1 = _ from ih (by omega) c.left]
      rfl
    · have cond : c.right.addr ≠ (cache.cell (by omega : d ≤ cap) true).addr := e
      simp only [if_neg e, dif_neg cond]
      rw [show bump cache.lookup H d (H.children c.addr).2 = _ from ih (by omega) c.right]
      rfl

theorem addUnit_eq (v : H.Valid) (cache : Cached S H cap) (p : Position h)
    (hd : h ≤ cap) {a : S.Ref h} (c : Cell S H a) :
    addUnit cache.lookup H p c.addr =
      (erase (addUnitAddr v cache p hd c).out, (addUnitAddr v cache p hd c).carry) := by
  induction p with
  | here => simp [addUnit, addUnitAddr, erase, Write.unchanged, Cell.flipped, Cell.bit]
  | @high d p ih =>
    simp only [addUnit, addUnitAddr]
    rw [show addUnit cache.lookup H p (H.children c.addr).1 = _ from ih (by omega) c.left]
    rfl
  | @low d p ih =>
    have hd' : d ≤ cap := by omega
    simp only [addUnit, addUnitAddr]
    rw [show addUnit cache.lookup H p (H.children c.addr).2 = _ from ih hd' c.right]
    let t := addUnitAddr v cache p hd' c.right
    by_cases e : t.carry = true
    · dsimp only [t] at e
      simp only [if_pos e, dif_pos e]
      by_cases f : (H.children c.addr).1 = cache.lookup d true
      · have cond : c.left.addr = (cache.cell hd' true).addr := f
        simp only [if_pos f, dif_pos cond]; rfl
      · have cond : c.left.addr ≠ (cache.cell hd' true).addr := f
        simp only [if_neg f, dif_neg cond]
        have be := bump_eq t.out.valid (cache.lift t.out.growth) d hd' (c.left.lift t.out.growth)
        change bump cache.lookup t.out.heap d (H.children c.addr).1 = _ at be
        change (join (bump cache.lookup t.out.heap d (H.children c.addr).1).heap d
          (bump cache.lookup t.out.heap d (H.children c.addr).1).addr t.out.cell.addr, false) = _
        rw [be]; rfl
    · dsimp only [t] at e
      simp only [if_neg e, dif_neg e]; rfl

theorem advance_eq (v : H.Valid) (cache : Cached S H cap) (p : Position h)
    (hd : h ≤ cap) {a : S.Ref h} (c : Cell S H a) (j : Nat) :
    advance cache.lookup H p c.addr j = erase (advanceAddr v cache p hd c j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    let t := advanceAddr v cache p hd c j
    simp only [advance, ih]
    change (addUnit (cache.lift t.growth).lookup t.heap p t.cell.addr).1 = _
    rw [addUnit_eq t.valid]; rfl

end SortingAdversary.Continuous.PolylogRawBits
