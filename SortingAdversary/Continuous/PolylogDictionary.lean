import SortingAdversary.Continuous.PolylogBits
import Std.Data.DTreeMap.Internal.Model

/-!
# Worst-case dictionary paths and block addresses

These bounds concern the balanced search trees actually used by the shared
block heap. A lookup compares the key at each visited node; an insertion
also performs at most one root rebalance at each visited node. Keys are an
address or a triple of words. The proof uses the library's balance invariant.
-/

namespace SortingAdversary.Continuous.PolylogDictionary

open Std.DTreeMap.Internal PolylogBits

variable {α β : Type}

private def depth {γ : α → Type} : Impl α γ → Nat
  | .leaf => 0
  | .inner _ _ _ l r => max (depth l) (depth r) + 1

/-- A deepest child, used only to prove the shape bound. -/
private def child {γ : α → Type} : Impl α γ → Impl α γ
  | .leaf => .leaf
  | .inner _ _ _ l r => if depth l ≤ depth r then r else l

private theorem child_bound {γ : α → Type} (t : Impl α γ) (hb : t.Balanced) :
    (child t).Balanced ∧ 4*(child t).size ≤ 3*t.size ∧ depth t ≤ depth (child t)+1 := by
  cases hb with
  | leaf => exact ⟨.leaf, Nat.le_refl 0, Nat.zero_le _⟩
  | @inner sz k v l r hl hr bal szEq =>
    unfold Impl.BalancedAtRoot at bal
    simp only [delta] at bal
    simp only [child, depth, Impl.size_inner]
    split <;> (first | exact ⟨hr, by omega, by omega⟩ | exact ⟨hl, by omega, by omega⟩)

private theorem depth_le_of_size {γ : α → Type} (k : Nat) (t : Impl α γ)
    (hb : t.Balanced) (hs : t.size < 2^k) : depth t ≤ 3*k := by
  induction k generalizing t with
  | zero =>
    cases hb with
    | leaf => exact Nat.le_refl 0
    | inner _ _ _ e => simp only [Impl.size_inner, Nat.pow_zero] at hs; omega
  | succ k ih =>
    obtain ⟨b₁, s₁, d₁⟩ := child_bound t hb
    obtain ⟨b₂, s₂, d₂⟩ := child_bound (child t) b₁
    obtain ⟨b₃, s₃, d₃⟩ := child_bound (child (child t)) b₂
    rw [Nat.pow_succ] at hs
    have small : (child (child (child t))).size < 2^k := by omega
    have := ih _ b₃ small
    omega

private theorem size_lt_two (n : Nat) : n < 2^(n.log2+1) := by
  exact Nat.lt_log2_self

/-- Lookup together with its number of key comparisons. -/
def lookup [Ord α] (k : α) : Impl α (fun _ => β) → Option β × Nat
  | .leaf => (none, 0)
  | .inner _ k' v l r =>
    match compare k k' with
    | .lt => let t := lookup k l; (t.1,t.2+1)
    | .gt => let t := lookup k r; (t.1,t.2+1)
    | .eq => (some v, 1)

/-- Insertion; the counter bounds key comparisons and the number of local
rebalancing operations separately. -/
def insert [Ord α] (k : α) (v : β) :
    Impl α (fun _ => β) → Impl α (fun _ => β) × Nat
  | .leaf => (.inner 1 k v .leaf .leaf, 0)
  | .inner sz k' v' l r =>
    match compare k k' with
    | .lt => let t := insert k v l; (Impl.balanceL! k' v' t.1 r, t.2+1)
    | .gt => let t := insert k v r; (Impl.balanceR! k' v' l t.1, t.2+1)
    | .eq => (.inner sz k v l r, 1)

private theorem lookup_spec [Ord α] (k : α) (t : Impl α (fun _ => β)) :
    (lookup k t).1 = Impl.Const.get? t k ∧ (lookup k t).2 ≤ depth t := by
  induction t with
  | leaf => exact ⟨rfl, Nat.le_refl 0⟩
  | inner _ k' _ l r il ir =>
    cases e : compare k k' <;> simp [lookup, Impl.Const.get?, e, depth, il.1, ir.1] <;> omega

private theorem insert_spec [Ord α] (k : α) (v : β) (t : Impl α (fun _ => β)) :
    (insert k v t).1 = Impl.insert! k v t ∧ (insert k v t).2 ≤ depth t := by
  induction t with
  | leaf => exact ⟨rfl, Nat.le_refl 0⟩
  | inner _ k' _ l r il ir =>
    cases e : compare k k' <;> simp [insert, Impl.insert!, e, depth, il.1, ir.1] <;> omega

theorem lookup_map [Ord α] (m : Std.TreeMap α β) (k : α) :
    (lookup k m.inner.inner).1 = m[k]? ∧
    (lookup k m.inner.inner).2 ≤ 3*(m.size.log2+1) := by
  have H := lookup_spec k m.inner.inner
  exact ⟨H.1, Nat.le_trans H.2 (depth_le_of_size _ _ m.inner.wf.balanced (size_lt_two _))⟩

theorem insert_map [Ord α] (m : Std.TreeMap α β) (k : α) (v : β) :
    (insert k v m.inner.inner).1 = (m.insert k v).inner.inner ∧
    (insert k v m.inner.inner).2 ≤ 3*(m.size.log2+1) := by
  have H := insert_spec k v m.inner.inner
  exact ⟨H.1.trans Impl.insert_eq_insert!.symm,
    Nat.le_trans H.2 (depth_le_of_size _ _ m.inner.wf.balanced (size_lt_two _))⟩

/-- A sequence of concrete interning calls; input keys can be those recorded
from any adaptive execution. -/
def allocate : Heap → List Key → Heap
  | H, [] => H
  | H, k :: ks => allocate (H.intern k).1 ks

theorem allocate_bound (H : Heap) (hv : H.Valid) (ks : List Key) :
    (allocate H ks).Valid ∧ (allocate H ks).next ≤ H.next + ks.length := by
  induction ks generalizing H with
  | nil => exact ⟨hv, by simp [allocate]⟩
  | cons k ks ih =>
    obtain ⟨v, e⟩ := ih _ (H.intern_valid hv k)
    have := (H.intern_growth hv k).1
    exact ⟨v, by simp only [allocate, List.length_cons]; omega⟩

/-- Every allocated address fits in a word of logarithmic length in the
initial allocation plus the number of interning calls. -/
theorem address_lt_pow (H : Heap) (hv : H.Valid) (ks : List Key) (i : Nat) (k : Key)
    (hi : (allocate H ks).record[i]? = some k) :
    i < 2^((H.next + ks.length).log2+1) := by
  obtain ⟨v, size⟩ := allocate_bound H hv ks
  exact Nat.lt_trans (Nat.lt_of_lt_of_le (v.bounds _ _ hi).2 size) (size_lt_two _)

attribute [local instance] lexOrd

/-- Both dictionaries of a concrete interning heap grow by at most one
record per request, even when all keys are distinct. -/
theorem dictionary_sizes (H : Heap) (ks : List Key) :
    (allocate H ks).address.size ≤ H.address.size + ks.length ∧
    (allocate H ks).record.size ≤ H.record.size + ks.length := by
  induction ks generalizing H with
  | nil => simp [allocate]
  | cons k ks ih =>
    obtain ⟨ha, hr⟩ := ih (H.intern k).1
    change (allocate (H.intern k).1 ks).address.size ≤ _ ∧
      (allocate (H.intern k).1 ks).record.size ≤ _
    apply And.intro <;> (first | apply Nat.le_trans ha | apply Nat.le_trans hr) <;>
      cases e : H.address[k]? <;> simp [Heap.intern, e] <;>
      first | omega | exact Nat.le_trans (Nat.add_le_add_right Std.TreeMap.size_insert_le _) (by omega)

/-- Key comparisons in the forward lookup and the two conditional inserts.
One comparison per internal node also bounds the number of rebalances. -/
def internComparisons (H : Heap) (k : Key) : Nat :=
  let t := lookup k H.address.inner.inner
  match t.1 with
  | some _ => t.2
  | none => t.2 + (insert k H.next H.address.inner.inner).2 +
      (insert H.next k H.record.inner.inner).2

theorem internComparisons_le (H : Heap) (k : Key) :
    internComparisons H k ≤ 6*(H.address.size.log2+1) + 3*(H.record.size.log2+1) := by
  have a := (lookup_map H.address k).2
  have b := (insert_map H.address k H.next).2
  have c := (insert_map H.record H.next k).2
  simp only [internComparisons]
  split <;> omega

private theorem log2_mono {x y : Nat} (e : x ≤ y) : x.log2 ≤ y.log2 := by
  by_cases hz : x = 0
  · simp [hz]
  · have hy : y ≠ 0 := by omega
    exact (Nat.le_log2 hy).2 (Nat.le_trans (Nat.log2_self_le hz) e)

theorem internComparisons_allocated (H : Heap) (hv : H.Valid) (k : Key) :
    internComparisons H k ≤ 9*(H.next.log2+1) := by
  have := internComparisons_le H k
  have := log2_mono hv.address_size
  have := log2_mono hv.record_size
  omega

end SortingAdversary.Continuous.PolylogDictionary
