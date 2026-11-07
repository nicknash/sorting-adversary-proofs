import SortingAdversary.Optimal.NormalizedBounds
import SortingAdversary.Optimal.StoredReady
import SortingAdversary.Optimal.StructuralNormalize

/-!
# The concrete recursive comparison controller

Every unknown query descends to its actual stopping node, evaluates the local
dynamic programs, selects the safe larger branch, performs the complete width
and structural normalization, and replays those exact promotions into the
stored child tree. All local-oracle and normalization hypotheses are derived
from maintained invariants and the scalar parameter package.
-/

namespace SortingAdversary.Optimal.RecursiveController

open PoolState WeakMaps WeakMaps.WeakSystem WidthRepair ControllerRouting Safety
open PoolTree.Tree PoolPalette PassiveLocalState StoredRouting NormalizedBounds

variable {n : ℕ}

structure Parameters where
  repair : StructuralNormalize.Parameters
  error : ℚ
  error_pos : 0 < error
  error_small : error < 1 / 2
  height_budget : 2 * repair.H ≤ repair.scale.H
  degree_budget : repair.D + 1 ≤ repair.d
  comparable_budget : (repair.d + 1) ^ (repair.scale.H + 1) ≤ repair.scale.width.B
  comparison_minimum : LocalParameters.minimumWidth repair.scale.H
    (LocalAccuracy.influenceSize repair.scale.H repair.d) repair.scale.R error ≤ repair.scale.width.W₀

def ready (p : Parameters) : LocalProperty n := Ready p.repair.scale p.repair.D p.repair.H

theorem Parameters.height_old (p : Parameters) : p.repair.H ≤ p.repair.scale.H := by
  have := p.height_budget
  omega

theorem Parameters.degree_old (p : Parameters) : p.repair.D ≤ p.repair.d := by
  have := p.degree_budget
  omega

def compared (s : State n) (a b : Fin n) (ha : a ∈ s.pool.members) (hb : b ∈ s.pool.members)
    (hne : a ≠ b) (hi : Invariant (closedAdd s.pool.system a b) s.pool.pins) : State n :=
  added s.pool ⟨s.rows, s.order⟩ a b ha hb hne hi

/-- The actual local execution retained for whole-run accounting. The
comparison state is computed from the recorded parent and oriented query. -/
structure RepairRecord (p : Parameters) (n : ℕ) where
  identity : ℕ
  before : State n
  first : Fin n
  second : Fin n
  first_member : first ∈ before.pool.members
  second_member : second ∈ before.pool.members
  distinct : first ≠ second
  updated : Invariant (closedAdd before.pool.system first second) before.pool.pins
  children : List (ℕ × StoredTree n)
  wellFormed : (StoredRepair.node identity
    (compared before first second first_member second_member distinct updated) children).erase.WellFormed
  coherent : (StoredRepair.node identity
    (compared before first second first_member second_member distinct updated) children).erase.Coherent
  counter : ℕ
  result : StructuralNormalize.Result
    (compared before first second first_member second_member distinct updated) p.repair

def RepairRecord.replay {p : Parameters} (r : RepairRecord p n) :=
  StoredRepair.replayTrace r.identity r.result.trace r.children r.wellFormed r.coherent r.counter

def RepairRecord.final {p : Parameters} (r : RepairRecord p n) : StoredTree n :=
  StoredRepair.node r.identity r.result.final r.replay.children

/-- The fully instantiated stopping program: no counting or repair callback
is left in this definition. The remaining arguments are raw state proofs. -/
def stop (p : Parameters) : Stopper (ready (n := n) p) (RepairRecord p n) :=
  fun t hw ho normal a b ha hb hab hba hstop counter =>
    match t with
    | .node identity q d children =>
      let s := state q d
      have hq : (PoolTree.Tree.node identity q (StoredTree.erasedChildren children)).WellFormed := by
        simpa only [StoredTree.erase, StoredTree.erasedChildren] using hw
      have hco : (PoolTree.Tree.node identity q (StoredTree.erasedChildren children)).Coherent := by
        simpa only [StoredTree.erase, StoredTree.erasedChildren] using ho
      have hn := (allNodes_node (ready p) identity q d children).mp normal
      let estimates := NormalizedBounds.estimates hn.1 p.repair.d p.height_old p.degree_old
        p.error p.error_pos p.comparison_minimum a b (distinct_of_reverse_unknown q a b hba)
      let sign := chooseStoppingSign q a b hab hba hstop p.error p.error_pos.le estimates
      let first := firstLabel a b sign.forward
      let second := secondLabel a b sign.forward
      let hf := PoolTree.Tree.first_member q a b ha hb sign.forward
      let hs := PoolTree.Tree.second_member q a b ha hb sign.forward
      let hr := reverse_unknown q a b hab hba sign.forward
      let hne := distinct_of_reverse_unknown q first second hr
      let hi := safe_update q.invariant hr sign.safe sign.feasible
      let nextState := compared s first second hf hs hne hi
      let graph := afterComparisonBounds hn.1 first second hf hs hne hi hr
        p.repair.scale.H p.repair.d p.height_budget p.degree_budget
      have hB : ComparableBound nextState p.repair.scale.width.B :=
        fun x => (comparableBound_of_sparse nextState p.repair.scale.H p.repair.d graph x).trans
          p.comparable_budget
      let normalized := StructuralNormalize.normalize nextState p.repair graph hB
      have hnext : (StoredRepair.node identity nextState children).erase =
          PoolTree.Tree.stopNode identity q (StoredTree.erasedChildren children) first second hf hs hi := by
        rw [StoredRepair.erase_node]
        rfl
      have hw' : (StoredRepair.node identity nextState children).erase.WellFormed := by
        rw [hnext]
        exact stopNode_wellFormed identity q _ (parts hq) first second hf hs hi
      have ho' : (StoredRepair.node identity nextState children).erase.Coherent := by
        rw [hnext]
        exact stopNode_coherent identity q _ (parts hq) hco first second hf hs hi sign.safe.1
      let record : RepairRecord p n := {
        identity := identity
        before := s
        first := first
        second := second
        first_member := hf
        second_member := hs
        distinct := hne
        updated := hi
        children := children
        wellFormed := hw'
        coherent := ho'
        counter := counter
        result := normalized }
      let replay := record.replay
      { forward := sign.forward
        next := record.final
        counter := replay.counter
        payload := record
        charge := (1 / (1 / 2 - p.error)) * replay.charge
        wellFormed := replay.wellFormed
        coherent := replay.coherent
        bounded := by
          intro hbnd
          apply replay.bounded
          rw [hnext]
          exact stopNode_bounded identity q _ first second hf hs hi
            (by simpa only [StoredTree.erase, StoredTree.erasedChildren] using hbnd)
        ready := by
          rw [RepairRecord.final, StoredRepair.node, allNodes_node]
          refine ⟨⟨normalized.normal, normalized.degree, normalized.height⟩, ?_⟩
          exact StoredReady.replayTrace_children_ready p.repair.scale p.repair.D p.repair.H
            p.repair.degree_pos p.repair.path_two identity normalized.trace children hw' ho' counter hn.2
        members := normalized.trace.members
        edges := normalized.trace.public_edges
        retention := by
          have hprice := stopNode_retention identity q (StoredTree.erasedChildren children)
            first second hf hs hi (1 / 2 - p.error) (by have := p.error_small; linarith) sign.retention
          have hrp := replay.retention
          rw [hnext] at hrp
          have hfactor : (0 : ℚ) ≤ 1 / (1 / 2 - p.error) := by
            have := p.error_small
            positivity
          rw [StoredTree.erase]
          exact hprice.trans (by
            simpa only [mul_assoc, RepairRecord.final] using mul_le_mul_of_nonneg_left hrp hfactor) }

/-- Routing preserves all normalized local states and has the actual complete
stopping executor above as its only leaf operation. -/
def answerUnknown (p : Parameters) (t : StoredTree n)
    (hw : t.erase.WellFormed) (ho : t.erase.Coherent) (normal : AllNodes (ready p) t)
    (a b : Fin n) (ha : a ∈ t.pool.members) (hb : b ∈ t.pool.members)
    (hab : t.pool.system.edge a b ≠ true) (hba : t.pool.system.edge b a ≠ true) (counter : ℕ) :
    Answered (ready p) (RepairRecord p n) t a b :=
  routeUnknown (stop p) (ready_delegation_stable p.repair.scale p.repair.D p.repair.H)
    (fun _ _ _ record => record) t hw ho normal a b ha hb hab hba counter

end SortingAdversary.Optimal.RecursiveController
