import SortingAdversary.Optimal.StoredTree
import SortingAdversary.Optimal.TreePromotionCount

/-!
# Concrete sparse-data parent/child promotion

This is the runtime mutation corresponding to `PoolTree.Tree.promotedNode`.
Erasure commutes exactly with the complete update, so all structural and
counting theorems apply to the actual stored tree.
-/

namespace SortingAdversary.Optimal.StoredTree

open PoolState WeakMaps WeakMaps.WeakSystem
variable {n : ℕ}

theorem child_unused {p : Pool n} {children : List (ℕ × StoredTree n)}
    (h : PoolTree.Tree.Parts p (erasedChildren children)) (v : Fin n)
    (hv : p.pins v = none) (a : ℕ × StoredTree n) (ha : a ∈ children) :
    v ∉ a.2.pool.members := by
  have hh := h.child_unused hv (a.1, a.2.erase) (List.mem_map.mpr ⟨a, ha, rfl⟩)
  simpa only [erase_pool] using hh

def promotedChild {p : Pool n} {children : List (ℕ × StoredTree n)}
    (h : PoolTree.Tree.Parts p (erasedChildren children))
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c) (a : ℕ × StoredTree n) (ha : a ∈ children) :
    StoredTree n :=
  if ColourTransport.extend r.embed a.1 = r.destination.val
  then a.2.admitRoot v (child_unused h v hv a ha) else a.2

def promotedChildren {p : Pool n} {children : List (ℕ × StoredTree n)}
    (h : PoolTree.Tree.Parts p (erasedChildren children))
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c) : List (ℕ × StoredTree n) :=
  children.attach.map (fun a =>
    (ColourTransport.extend r.embed a.val.1, promotedChild h v hv c r a.val a.property))

theorem erase_promotedChild {p : Pool n} {children : List (ℕ × StoredTree n)}
    (h : PoolTree.Tree.Parts p (erasedChildren children))
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c) (a : ℕ × StoredTree n) (ha : a ∈ children) :
    (promotedChild h v hv c r a ha).erase =
      PoolTree.Tree.promotedChild h v hv c r (a.1, a.2.erase) (List.mem_map.mpr ⟨a, ha, rfl⟩) := by
  by_cases hs : ColourTransport.extend r.embed a.1 = r.destination.val
  · simp only [promotedChild, PoolTree.Tree.promotedChild, if_pos hs, erase_admitRoot]
  · simp only [promotedChild, PoolTree.Tree.promotedChild, if_neg hs]

theorem erased_promotedChildren {p : Pool n} {children : List (ℕ × StoredTree n)}
    (h : PoolTree.Tree.Parts p (erasedChildren children))
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c) :
    erasedChildren (promotedChildren h v hv c r) = PoolTree.Tree.promotedChildren h v hv c r := by
  apply List.ext_getElem
  · simp [erasedChildren, promotedChildren, PoolTree.Tree.promotedChildren]
  · intro i hi hj
    have hi0 : i < children.length := by
      simpa only [erasedChildren, promotedChildren, List.length_map, List.length_attach] using hi
    simp only [erasedChildren, promotedChildren, PoolTree.Tree.promotedChildren,
      List.getElem_map, List.getElem_attach]
    exact congrArg (fun t => (ColourTransport.extend r.embed children[i].1, t))
      (erase_promotedChild h v hv c r children[i] (List.getElem_mem _))

def promotedNode (identity : ℕ) (p : Pool n) (children : List (ℕ × StoredTree n))
    (h : PoolTree.Tree.Parts p (erasedChildren children))
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c)
    (d : LocalData (p.installPromotion v hv c r)) (freshIdentity : ℕ) : StoredTree n :=
  let next := p.installPromotion v hv c r
  let oldChildren := promotedChildren h v hv c r
  if PoolTree.Tree.destinationExists r (erasedChildren children) = true
  then .node identity next d oldChildren
  else .node identity next d (oldChildren ++ [(r.destination.val, freshChild n freshIdentity v)])

theorem erase_promotedNode (identity : ℕ) (p : Pool n) (children : List (ℕ × StoredTree n))
    (h : PoolTree.Tree.Parts p (erasedChildren children))
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c)
    (d : LocalData (p.installPromotion v hv c r)) (freshIdentity : ℕ) :
    (promotedNode identity p children h v hv c r d freshIdentity).erase =
      PoolTree.Tree.promotedNode identity p (erasedChildren children) h v hv c r freshIdentity := by
  by_cases he : PoolTree.Tree.destinationExists r (erasedChildren children) = true
  · simp only [promotedNode, PoolTree.Tree.promotedNode, he, ite_true]
    rw [erase]
    exact congrArg (PoolTree.Tree.node identity _) (erased_promotedChildren h v hv c r)
  · simp only [promotedNode, PoolTree.Tree.promotedNode, if_neg he]
    rw [erase]
    change PoolTree.Tree.node identity _
      (erasedChildren (promotedChildren h v hv c r ++ [(r.destination.val, freshChild n freshIdentity v)])) = _
    simp only [erasedChildren, List.map_append, List.map_singleton, erase_freshChild]
    exact congrArg (PoolTree.Tree.node identity _)
      (congrArg (fun cs => cs ++ [(r.destination.val, PoolTree.Tree.freshChild n freshIdentity v)])
        (erased_promotedChildren h v hv c r))

end SortingAdversary.Optimal.StoredTree
