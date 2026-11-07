import SortingAdversary.Optimal.TreePromotion
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Exact product accounting for a physical tree promotion

The parent loss and the destination's independent birthday multiplier are
proved for the mutated recursive tree itself, including all old descendants.
-/

namespace SortingAdversary.Optimal.PoolTree.Tree

open PoolState WeakMaps WeakMaps.WeakSystem

variable {n : ℕ}

theorem count_pos (t : Tree n) : 0 < t.count := by
  cases t with
  | node identity p children =>
    rw [count]
    apply Nat.mul_pos p.count_pos
    apply List.prod_pos
    intro k hk
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hk
    exact count_pos a.2
termination_by sizeOf t
decreasing_by
  have hh := List.sizeOf_lt_of_mem ha
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at hh
  omega

@[simp] theorem freshChild_count (n identity : ℕ) (v : Fin n) :
    (freshChild n identity v).count = 2 := by
  rw [freshChild, admitRoot_count, empty_count]
  simp [admitRoot, empty, pool, Pool.admission, emptyPool, Pool.admitSized]

def childMultiplier {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (a : ℕ × Tree n) (ha : a ∈ children) : ℕ :=
  if ColourTransport.extend r.embed a.1 = r.destination.val
  then (a.2.admitRoot v (h.child_unused hv a ha)).pool.palette + 1 else 1

theorem childMultiplier_pos {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (a : ℕ × Tree n) (ha : a ∈ children) : 0 < childMultiplier h v hv c r a ha := by
  unfold childMultiplier
  split <;> omega

theorem promotedChild_count {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (a : ℕ × Tree n) (ha : a ∈ children) :
    (promotedChild h v hv c r a ha).count = a.2.count * childMultiplier h v hv c r a ha := by
  unfold promotedChild childMultiplier
  split
  · exact admitRoot_count _ _ _
  · exact (Nat.mul_one _).symm

def oldBirthMultiplier {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c) : ℕ :=
  (children.attach.map (fun a => childMultiplier h v hv c r a.val a.property)).prod

theorem oldBirthMultiplier_pos {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c) :
    0 < oldBirthMultiplier h v hv c r := by
  apply List.prod_pos
  intro k hk
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hk
  exact childMultiplier_pos h v hv c r a.val a.property

theorem promotedChildren_count {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c) :
    ((promotedChildren h v hv c r).map (fun a => a.2.count)).prod =
      (children.map (fun a => a.2.count)).prod * oldBirthMultiplier h v hv c r := by
  simp only [promotedChildren, List.map_map, Function.comp_def, promotedChild_count]
  rw [List.prod_map_mul]
  have he : (children.attach.map (fun a => a.val.2.count)) =
      children.map (fun a => a.2.count) :=
    List.attach_map_val (l := children) (f := fun a => a.2.count)
  rw [he]
  rfl

/-- The actual child-birth multiplier, including a newly allocated child. -/
def birthMultiplier {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c) : ℕ :=
  oldBirthMultiplier h v hv c r * (if destinationExists r children = true then 1 else 2)

theorem birthMultiplier_pos {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c) :
    0 < birthMultiplier h v hv c r := by
  apply Nat.mul_pos (oldBirthMultiplier_pos h v hv c r)
  split <;> omega

theorem birthday_le_multiplier {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (a : ℕ × Tree n) (ha : a ∈ children)
    (hs : ColourTransport.extend r.embed a.1 = r.destination.val) :
    a.2.pool.members.card + 1 ≤ birthMultiplier h v hv c r := by
  have hc : a.2.pool.members.card + 1 ≤ childMultiplier h v hv c r a ha := by
    rw [childMultiplier, if_pos hs]
    have hcap := (a.2.admitRoot v (h.child_unused hv a ha)).pool.capacity
    rw [admitRoot_members, Finset.card_insert_of_notMem (h.child_unused hv a ha)] at hcap
    exact hcap
  have hp : childMultiplier h v hv c r a ha ≤ oldBirthMultiplier h v hv c r := by
    apply List.single_le_prod
    · intro k hk
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hk
      exact childMultiplier_pos h v hv c r b.val b.property
    · exact List.mem_map.mpr ⟨⟨a, ha⟩, List.mem_attach _ _, rfl⟩
  have hex := (destinationExists_iff r children).mpr ⟨a, ha, hs⟩
  simpa [birthMultiplier, hex] using hc.trans hp

theorem promotedNode_count (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (freshIdentity : ℕ) :
    (promotedNode identity p children h v hv c r freshIdentity).count =
      r.system.count * (children.map (fun a => a.2.count)).prod * birthMultiplier h v hv c r := by
  unfold promotedNode birthMultiplier
  split
  · rw [count, promotedChildren_count]
    simp only [Pool.installPromotion]
    simp only [Nat.mul_one, Nat.mul_assoc]
  · rw [count, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]
    rw [promotedChildren_count, freshChild_count]
    simp only [Pool.installPromotion]
    ac_rfl

/-- A signed birthday credit applies to the exact new global potential. -/
theorem promotion_price_with_birthday
    (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (freshIdentity A birthday : ℕ) (hA : p.system.count ≤ A * r.system.count)
    (hb : birthday ≤ birthMultiplier h v hv c r) :
    birthday * (Tree.node identity p children).count ≤
      A * (promotedNode identity p children h v hv c r freshIdentity).count := by
  rw [count, promotedNode_count]
  calc
    birthday * (p.system.count * (children.map (fun a => a.2.count)).prod) ≤
        birthMultiplier h v hv c r *
          ((A * r.system.count) * (children.map (fun a => a.2.count)).prod) :=
      Nat.mul_le_mul hb (Nat.mul_le_mul_right _ hA)
    _ = A * (r.system.count * (children.map (fun a => a.2.count)).prod *
        birthMultiplier h v hv c r) := by ac_rfl

@[simp] theorem promotedNode_members
    (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (freshIdentity : ℕ) :
    (promotedNode identity p children h v hv c r freshIdentity).pool.members = p.members := by
  unfold promotedNode
  split <;> rfl

@[simp] theorem promotedNode_edges
    (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (freshIdentity : ℕ) :
    (promotedNode identity p children h v hv c r freshIdentity).pool.system.edge = p.system.edge := by
  have hp : (promotedNode identity p children h v hv c r freshIdentity).pool =
      p.installPromotion v hv c r := by
    unfold promotedNode
    split <;> rfl
  exact (congrArg (fun q : Pool n => q.system.edge) hp).trans r.edges

end SortingAdversary.Optimal.PoolTree.Tree
