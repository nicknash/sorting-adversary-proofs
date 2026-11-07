import SortingAdversary.Optimal.TreeRoutingBase
import Mathlib.Data.List.Nodup

/-!
# Replace exactly the child that answered a delegated query

The ancestor stores the new public relation but keeps its numerical count.
All other children retain their internal public order. The exact product
identity transfers the answering subtree's retained fraction to the root.
-/

namespace SortingAdversary.Optimal.PoolTree.Tree

open PoolState WeakMaps WeakMaps.WeakSystem ControllerRouting Safety

variable {n : ℕ}

theorem Parts.unique_key {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) {a b : ℕ × Tree n} (ha : a ∈ children) (hb : b ∈ children)
    (he : a.1 = b.1) : a = b := List.inj_on_of_nodup_map h.keys ha hb he

def replaceChildren (key : ℕ) (next : Tree n) (children : List (ℕ × Tree n)) :
    List (ℕ × Tree n) := children.map (fun a => (a.1, if a.1 = key then next else a.2))

@[simp] theorem replaceChildren_keys (key : ℕ) (next : Tree n) (children : List (ℕ × Tree n)) :
    (replaceChildren key next children).map Prod.fst = children.map Prod.fst := by
  simp [replaceChildren, Function.comp_def]

theorem replacement_parts {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (target : ℕ × Tree n) (ht : target ∈ children)
    (next : Tree n) (hn : next.WellFormed)
    (hm : next.pool.members = target.2.pool.members) :
    Parts p (replaceChildren target.1 next children) := by
  refine ⟨by simpa using h.keys, ?_, ?_, h.separated, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact h.bounds b hb
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    by_cases he : b.1 = target.1
    · simp only [if_pos he, hm]
      exact h.occupied target ht
    · simpa only [if_neg he] using h.occupied b hb
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    by_cases he : b.1 = target.1
    · simpa only [if_pos he] using hn
    · simpa only [if_neg he] using h.children_ok b hb
  · intro a ha x
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    by_cases he : b.1 = target.1
    · rw [if_pos he, hm, he]
      exact h.members target ht x
    · simpa only [if_neg he] using h.members b hb x
  · intro x hx key hpin
    obtain ⟨child, hc⟩ := h.covered x hx key hpin
    exact ⟨if key = target.1 then next else child,
      List.mem_map.mpr ⟨(key, child), hc, rfl⟩⟩

def delegatedNode (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (target : ℕ × Tree n) (ht : target ∈ children)
    (a b : Fin n) (ha : a ∈ target.2.pool.members) (hb : b ∈ target.2.pool.members)
    (hba : p.system.edge b a ≠ true) (next : Tree n) : Tree n :=
  .node identity (addComparison p a b ((h.members target ht a).mp ha).1
    ((h.members target ht b).mp hb).1
    (retaining_invariant p a b hba (same_child_retains h target ht a b ha hb)))
    (replaceChildren target.1 next children)

theorem delegatedNode_wellFormed
    (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (target : ℕ × Tree n) (ht : target ∈ children)
    (a b : Fin n) (ha : a ∈ target.2.pool.members) (hb : b ∈ target.2.pool.members)
    (hba : p.system.edge b a ≠ true) (next : Tree n) (hn : next.WellFormed)
    (hm : next.pool.members = target.2.pool.members) :
    (delegatedNode identity p children h target ht a b ha hb hba next).WellFormed := by
  exact stopNode_wellFormed identity p _ (replacement_parts h target ht next hn hm)
    a b _ _ _

theorem delegatedNode_coherent
    (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (ho : (Tree.node identity p children).Coherent)
    (target : ℕ × Tree n) (ht : target ∈ children)
    (a b : Fin n) (ha : a ∈ target.2.pool.members) (hb : b ∈ target.2.pool.members)
    (hba : p.system.edge b a ≠ true) (next : Tree n) (hn : next.Coherent)
    (hm : next.pool.members = target.2.pool.members)
    (he : next.pool.system.edge = (closedAdd target.2.pool.system a b).edge) :
    (delegatedNode identity p children h target ht a b ha hb hba next).Coherent := by
  refine .node _ _ _ ?_ ?_
  · intro child hc
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hc
    by_cases hk : old.1 = target.1
    · simpa only [if_pos hk] using hn
    · simpa only [if_neg hk] using ho.children old hold
  · intro child hc x hx y hy
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hc
    by_cases hk : old.1 = target.1
    · simp only [if_pos hk, hm] at hx hy
      change (if old.1 = target.1 then next else old.2).pool.system.edge x y = _
      rw [if_pos hk, he]
      exact same_child_closedAdd ho target ht a b ha hb x hx y hy
    · simp only [if_neg hk] at hx hy
      change (if old.1 = target.1 then next else old.2).pool.system.edge x y = _
      rw [if_neg hk]
      exact (ho.restriction old hold x hx y hy).trans
        (other_child_unchanged h target ht a b ha hb old hold hk x hx y hy).symm

theorem replaceChildren_unchanged (key : ℕ) (next : Tree n) (children : List (ℕ × Tree n))
    (h : ∀ a ∈ children, a.1 ≠ key) : replaceChildren key next children = children := by
  unfold replaceChildren
  induction children with
  | nil => rfl
  | cons a rest ih =>
    rw [List.map_cons]
    simp only [if_neg (h a (by simp)), Prod.mk.eta]
    rw [ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem replaceChildren_count_identity
    (children : List (ℕ × Tree n)) (hk : (children.map Prod.fst).Nodup)
    (target : ℕ × Tree n) (ht : target ∈ children) (next : Tree n) :
    ((replaceChildren target.1 next children).map (fun a => a.2.count)).prod * target.2.count =
      (children.map (fun a => a.2.count)).prod * next.count := by
  obtain ⟨before, after, heq, _⟩ := List.eq_append_cons_of_mem ht
  subst children
  have hbefore : ∀ a ∈ before, a.1 ≠ target.1 := by
    intro a ha he
    have hnodup := hk
    simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at hnodup
    exact hnodup.2.2 a.1 (List.mem_map.mpr ⟨a, ha, rfl⟩) target.1
      (List.mem_cons_self) he
  have hafter : ∀ a ∈ after, a.1 ≠ target.1 := by
    intro a ha he
    have hnodup := hk
    simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at hnodup
    exact hnodup.2.1.1 (he ▸ List.mem_map.mpr ⟨a, ha, rfl⟩)
  have hreplace : replaceChildren target.1 next (before ++ target :: after) =
      before ++ (target.1, next) :: after := by
    simp only [replaceChildren, List.map_append, List.map_cons, ite_true]
    change replaceChildren target.1 next before ++
      (target.1, next) ::
        replaceChildren target.1 next after = _
    rw [replaceChildren_unchanged _ _ _ hbefore, replaceChildren_unchanged _ _ _ hafter]
  rw [hreplace]
  simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  ac_rfl

theorem delegatedNode_count_identity
    (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (target : ℕ × Tree n) (ht : target ∈ children)
    (a b : Fin n) (ha : a ∈ target.2.pool.members) (hb : b ∈ target.2.pool.members)
    (hba : p.system.edge b a ≠ true) (next : Tree n) :
    (delegatedNode identity p children h target ht a b ha hb hba next).count * target.2.count =
      (Tree.node identity p children).count * next.count := by
  rw [delegatedNode, count, count]
  change (closedAdd p.system a b).count * _ * _ = _
  rw [retaining_count p a b (same_child_retains h target ht a b ha hb),
    Nat.mul_assoc, replaceChildren_count_identity children h.keys target ht next]
  ac_rfl

theorem delegatedNode_retention
    (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (target : ℕ × Tree n) (ht : target ∈ children)
    (a b : Fin n) (ha : a ∈ target.2.pool.members) (hb : b ∈ target.2.pool.members)
    (hba : p.system.edge b a ≠ true) (next : Tree n) (charge : ℚ)
    (hr : (target.2.count : ℚ) ≤ charge * next.count) :
    ((Tree.node identity p children).count : ℚ) ≤
      charge * (delegatedNode identity p children h target ht a b ha hb hba next).count := by
  have hp : (0 : ℚ) < target.2.count := by exact_mod_cast target.2.count_pos
  have hi : ((delegatedNode identity p children h target ht a b ha hb hba next).count : ℚ) *
      target.2.count = ((Tree.node identity p children).count : ℚ) * next.count := by
    exact_mod_cast delegatedNode_count_identity identity p children h target ht a b ha hb hba next
  apply (mul_le_mul_iff_left₀ hp).mp
  have hh := mul_le_mul_of_nonneg_right hr
    (Nat.cast_nonneg (Tree.node identity p children).count : (0 : ℚ) ≤ _)
  calc
    ((Tree.node identity p children).count : ℚ) * target.2.count ≤
        charge * (((Tree.node identity p children).count : ℚ) * next.count) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
    _ = (charge * (delegatedNode identity p children h target ht a b ha hb hba next).count) *
        target.2.count := by rw [← hi]; ring

end SortingAdversary.Optimal.PoolTree.Tree
