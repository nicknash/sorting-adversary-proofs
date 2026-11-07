import SortingAdversary.Optimal.MeasuredControllerTypes
import SortingAdversary.Optimal.RepresentationTreeReplay
import SortingAdversary.Optimal.ComparedWork

/-! # Proof-only comparison context for the measured stopping executor -/

namespace SortingAdversary.Optimal.MeasuredStop

open WidthRepair PoolState PoolTree.Tree StoredRouting RecursiveController
open ControllerRouting Safety LocalOracle RepresentationWork MeasuredController

variable {n : ℕ} {p : Parameters}

structure Context (p : Parameters) (n : ℕ) where
  identity : ℕ
  before : State n
  children : List (ℕ × StoredTree n)
  wellFormed : (StoredRepair.node identity before children).erase.WellFormed
  coherent : (StoredRepair.node identity before children).erase.Coherent
  normal : AllNodes (ready p) (StoredRepair.node identity before children)
  x : Fin n
  y : Fin n
  hx : x ∈ before.pool.members
  hy : y ∈ before.pool.members
  hxy : before.pool.system.edge x y ≠ true
  hyx : before.pool.system.edge y x ≠ true
  hstop : ¬ ∃ c, before.pool.pins x = some c ∧ before.pool.pins y = some c

namespace Context

abbrev node (c : Context p n) := StoredRepair.node c.identity c.before c.children

theorem localReady (c : Context p n) :
    PassiveLocalState.Ready p.repair.scale p.repair.D p.repair.H c.before.pool
      ⟨c.before.rows, c.before.order⟩ :=
  ((allNodes_node (ready p) c.identity c.before.pool
    ⟨c.before.rows, c.before.order⟩ c.children).mp c.normal).1

noncomputable def estimates (c : Context p n) :=
  NormalizedBounds.estimates c.localReady p.repair.d p.height_old p.degree_old
    p.error p.error_pos p.comparison_minimum c.x c.y
    (distinct_of_reverse_unknown c.before.pool c.x c.y c.hyx)

noncomputable def sign (c : Context p n) :=
  chooseStoppingSign c.before.pool c.x c.y c.hxy c.hyx c.hstop p.error p.error_pos.le c.estimates

abbrev Sign (c : Context p n) := StoppingSign c.before.pool c.x c.y p.error

abbrev first (c : Context p n) (s : c.Sign) := firstLabel c.x c.y s.forward
abbrev second (c : Context p n) (s : c.Sign) := secondLabel c.x c.y s.forward

theorem first_member (c : Context p n) (s : c.Sign) : c.first s ∈ c.before.pool.members :=
  PoolTree.Tree.first_member c.before.pool c.x c.y c.hx c.hy s.forward

theorem second_member (c : Context p n) (s : c.Sign) : c.second s ∈ c.before.pool.members :=
  PoolTree.Tree.second_member c.before.pool c.x c.y c.hx c.hy s.forward

theorem reverse_unknown (c : Context p n) (s : c.Sign) :
    c.before.pool.system.edge (c.second s) (c.first s) ≠ true :=
  PoolTree.Tree.reverse_unknown c.before.pool c.x c.y c.hxy c.hyx s.forward

theorem distinct (c : Context p n) (s : c.Sign) : c.first s ≠ c.second s :=
  distinct_of_reverse_unknown c.before.pool _ _ (c.reverse_unknown s)

theorem updated (c : Context p n) (s : c.Sign) :
    Invariant (closedAdd c.before.pool.system (c.first s) (c.second s)) c.before.pool.pins :=
  safe_update c.before.pool.invariant (c.reverse_unknown s) s.safe s.feasible

noncomputable def next (c : Context p n) (s : c.Sign) : State n :=
  compared c.before (c.first s) (c.second s) (c.first_member s) (c.second_member s)
    (c.distinct s) (c.updated s)

noncomputable def graph (c : Context p n) (s : c.Sign) :
    SparseBounds (c.next s).rows p.repair.scale.H p.repair.d :=
  NormalizedBounds.afterComparisonBounds c.localReady (c.first s) (c.second s)
    (c.first_member s) (c.second_member s) (c.distinct s) (c.updated s) (c.reverse_unknown s)
    p.repair.scale.H p.repair.d p.height_budget p.degree_budget

theorem comparable (c : Context p n) (s : c.Sign) :
    ComparableBound (c.next s) p.repair.scale.width.B :=
  fun x => (comparableBound_of_sparse (c.next s) p.repair.scale.H p.repair.d (c.graph s) x).trans
    p.comparable_budget

theorem next_erase (c : Context p n) (s : c.Sign) :
    (StoredRepair.node c.identity (c.next s) c.children).erase =
      stopNode c.identity c.before.pool (StoredTree.erasedChildren c.children)
        (c.first s) (c.second s) (c.first_member s) (c.second_member s) (c.updated s) := by
  rw [StoredRepair.erase_node]
  rfl

theorem next_wellFormed (c : Context p n) (s : c.Sign) :
    (StoredRepair.node c.identity (c.next s) c.children).erase.WellFormed := by
  rw [c.next_erase s]
  exact stopNode_wellFormed c.identity c.before.pool _
    (parts (by simpa only [StoredRepair.erase_node] using c.wellFormed))
    (c.first s) (c.second s) (c.first_member s) (c.second_member s) (c.updated s)

theorem next_coherent (c : Context p n) (s : c.Sign) :
    (StoredRepair.node c.identity (c.next s) c.children).erase.Coherent := by
  rw [c.next_erase s]
  exact stopNode_coherent c.identity c.before.pool _
    (parts (by simpa only [StoredRepair.erase_node] using c.wellFormed))
    (by simpa only [StoredRepair.erase_node] using c.coherent)
    (c.first s) (c.second s) (c.first_member s) (c.second_member s) (c.updated s) s.safe.1

theorem next_bounded (c : Context p n) (s : c.Sign) (hb : PoolPalette.TreeBounded c.node.erase) :
    PoolPalette.TreeBounded (StoredRepair.node c.identity (c.next s) c.children).erase := by
  rw [c.next_erase s]
  exact stopNode_bounded c.identity c.before.pool _ (c.first s) (c.second s)
    (c.first_member s) (c.second_member s) (c.updated s)
    (by simpa only [node, StoredRepair.erase_node] using hb)

noncomputable def reference (c : Context p n) (counter : ℕ) :=
  RecursiveController.stop p c.node c.wellFormed c.coherent c.normal c.x c.y c.hx c.hy
    c.hxy c.hyx c.hstop counter

def castGraph {s t : State n} (h : s = t) (g : SparseBounds t.rows H d) :
    SparseBounds s.rows H d := h.symm ▸ g

@[simp] theorem castGraph_rank {s t : State n} (h : s = t) (g : SparseBounds t.rows H d) :
    (castGraph h g).rank = g.rank := by cases h; rfl

theorem castComparable {s t : State n} (h : s = t) (g : ComparableBound t B) :
    ComparableBound s B := h.symm ▸ g


theorem sparseBounds_ext {s : State n} {H d : ℕ}
    (first second : SparseBounds s.rows H d) (h : first.rank = second.rank) : first = second := by
  cases first
  cases second
  dsimp only at h
  cases h
  rfl

theorem completed_actual (c : Context p n) (counter : ℕ)
    (s : c.Sign) (hs : s = c.sign)
    (u : State n) (hu : u = c.next s)
    (g : SparseBounds u.rows p.repair.scale.H p.repair.d)
    (hg : g = castGraph hu (c.graph s))
    (hB : ComparableBound u p.repair.scale.width.B)
    (normalized : StructuralNormalize.Result u p.repair)
    (hn : normalized = StructuralNormalize.normalize u p.repair g hB)
    (hw : (StoredRepair.node c.identity u c.children).erase.WellFormed)
    (ho : (StoredRepair.node c.identity u c.children).erase.Coherent)
    (children : List (ℕ × StoredTree n))
    (hc : children = (StoredRepair.replayTrace c.identity normalized.trace c.children hw ho counter).children)
    (nextCounter : ℕ)
    (hk : nextCounter = (StoredRepair.replayTrace c.identity normalized.trace c.children hw ho counter).counter) :
    (⟨s.forward, StoredRepair.node c.identity normalized.final children, nextCounter⟩ : Core n) =
      Core.ofAnswered (c.reference counter) := by
  subst u
  subst g
  subst normalized
  subst children
  subst nextCounter
  subst s
  rfl

end Context

end SortingAdversary.Optimal.MeasuredStop
