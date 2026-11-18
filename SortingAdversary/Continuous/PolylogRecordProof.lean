import SortingAdversary.Continuous.PolylogMutation
import SortingAdversary.Continuous.PolylogRepair
import SortingAdversary.Continuous.PolylogAligned

/-!
# Recording an answer in the physical machine

The new comparison event is exactly the change in the reference graph. It
therefore suffices to discover the same repair using the two sparse cones.
Recording consumes no new dyadic addresses or hierarchy nodes.
-/

namespace SortingAdversary.Continuous.PolylogCompare

open Controller
open PolylogStorage (route_value)
variable {n t b D k : ℕ}

open TreeState (Routing)
open Optimal.PrimitiveWork (Result)

def newArc (q : Query n) (a : Answer) : Routing ℕ → Option (Fin n × Fin n)
  | .coordinates => if a = .less then some (q.left,q.right) else some (q.right,q.left)
  | _ => none

def record (k : ℕ) (m : Memory n t b) (q : Query n) (a : Answer) :
    Result (Memory n t b × Option (Fin n × Fin n)) :=
  let r := PolylogStorage.route m.spatial q
  let z := PolylogMutation.recordState m.less m.spatial k m.zero m.one q a
  ⟨(⟨z.value,m.heap,m.valid,m.typed,m.cache,m.zero,m.one⟩,newArc q a r.value),
    r.work+z.work+2⟩

theorem record_represents {m : Memory n t b} {nodes : List (List ℕ)} {M : Controller.Memory n}
    (hm : m.Represents D nodes M) (ready : Ready k M) (cap : n ≤ 2^t)
    (q : Query n) (a : Answer) (post : Admissible k (recorded M q a)) :
    (record k m q a).value.1.Represents D nodes (recorded M q a) := by
  exact ⟨PolylogMutation.recordState_represents m.less (m.decode D) (m.less_correct D)
    (m.decode_injective D) hm.spatial ready.admissible m.zero m.one hm.zero_value hm.one_value
    cap q a post.toGeometric, hm.zero_value,hm.one_value,hm.paths_nonneg,hm.paths_bounded⟩

theorem record_edge {m : Memory n t b} {nodes : List (List ℕ)} {M : Controller.Memory n}
    (hm : m.Represents D nodes M) (q : Query n) (a : Answer) :
    (recorded M q a).tree.system.edge =
      match (record k m q a).value.2 with
      | none => M.tree.system.edge
      | some (x,y) => Optimal.SparseRepairGraph.addRow M.tree.system.edge x y := by
  rw [recorded_edge]
  change (TreeState.recordSystem M.tree.system (TreeState.route (M.tree.location q.left)
    (M.tree.location q.right)) q.left q.right a).edge =
    match newArc q a (PolylogStorage.route m.spatial q).value with
    | none => M.tree.system.edge
    | some (x,y) => Optimal.SparseRepairGraph.addRow M.tree.system.edge x y
  rw [← route_value hm.spatial (m.decode_injective D) q]
  cases (PolylogStorage.route m.spatial q).value <;> cases a <;> rfl

theorem record_choose {m : Memory n t b} {nodes : List (List ℕ)} {M : Controller.Memory n}
    (hm : m.Represents D nodes M) (ready : Ready k M) (cap : n ≤ 2^t)
    (q : Query n) (a : Answer) (post : Admissible k (recorded M q a)) :
    (PolylogRepair.choose (record k m q a).value.1.spatial.graph k (record k m q a).value.2).value =
      PolylogRepair.reserved (recorded M q a).tree.system.edge k :=
  PolylogRepair.choose_value _ k _ M (recorded M q a) ready post
    (record_represents hm ready cap q a post).spatial.graph (record_edge hm q a)

@[simp] theorem recorded_depth (M : Controller.Memory n) (q : Query n) (a : Answer) :
    totalDepth (recorded M q a) = totalDepth M := rfl

theorem recorded_grid {M : Controller.Memory n} {F : ℕ} (grid : M.OnGrid F)
    (q : Query n) (a : Answer) : (recorded M q a).OnGrid F :=
  grid.record q a (answerOrder M q a)

theorem record_sized_at {A j : ℕ} {m : Memory n t b}
    (hs : PolylogResources.Sized A b j m.spatial.directory m.heap) (q : Query n) (a : Answer) :
    let r := (record k m q a).value.1
    PolylogResources.Sized A b j r.spatial.directory r.heap := hs

theorem record_work {m : Memory n t b} {nodes : List (List ℕ)} {M : Controller.Memory n}
    (hs : m.Represents D nodes M) (ready : Ready k M) (q : Query n) (a : Answer) :
    (record k m q a).work ≤ PolylogMutation.coreBudget t k (ArbitraryLabels.pathHeight k) (3*b+6) +
      2*(t*(8*t+9))+32*t+36 := by
  have c := PolylogMutation.recordState_work m.less (3*b+6) (PolylogAddressOrder.work m.heap b)
    m.spatial k m.zero m.one
    (PolylogMutation.bounded_of_degree hs.spatial.graph k ready.noLoop ready.admissible.degree) q a
  have r := PolylogStorage.route_work m.spatial q
  dsimp only [record]; omega

theorem record_aligned {A : ℕ} {m : Memory n t b} {M : Controller.Memory n}
    (align : Aligned D A m M) (ready : Ready k M) (cap : n ≤ 2^t)
    (q : Query n) (a : Answer) (post : Admissible k (recorded M q a)) :
    Aligned D A (record k m q a).value.1 (recorded M q a) := by
  obtain ⟨nodes, hm⟩ := align.storage
  refine ⟨⟨nodes,record_represents hm ready cap q a post⟩, ?_, ?_⟩
  · exact recorded_grid align.grid q a
  · exact record_sized_at align.sized q a

theorem record_choose_aligned {A : ℕ} {m : Memory n t b} {M : Controller.Memory n}
    (align : Aligned D A m M) (ready : Ready k M) (cap : n ≤ 2^t)
    (q : Query n) (a : Answer) (post : Admissible k (recorded M q a)) :
    (PolylogRepair.choose (record k m q a).value.1.spatial.graph k (record k m q a).value.2).value =
      PolylogRepair.reserved (recorded M q a).tree.system.edge k := by
  obtain ⟨nodes,hm⟩ := align.storage
  exact record_choose hm ready cap q a post

end SortingAdversary.Continuous.PolylogCompare
