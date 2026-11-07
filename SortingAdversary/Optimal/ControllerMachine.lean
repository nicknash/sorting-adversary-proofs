import SortingAdversary.Optimal.RecursiveController
import SortingAdversary.Optimal.OnlineMachine

/-!
# A complete stateful adversary with a physical-comparison cutoff

Known comparisons consume one physical step without numerical maintenance.
Unknown comparisons invoke the concrete recursive controller. Matrices are
materialized between physical steps. At the cutoff, a concrete extension of
the current public order is fixed and supplies every subsequent answer.
-/

namespace SortingAdversary.Optimal.ControllerMachine

open PoolState WeakMaps WeakMaps.WeakSystem PoolTree.Tree PoolPalette
open RecursiveController StoredRouting PublicLegality SparseClosure

variable {n : ℕ}

theorem node_mpr {q p : Pool n} (hp : q = p) (identity : ℕ) (d : LocalData p)
    (children : List (ℕ × StoredTree n)) :
    StoredTree.node identity q ((congrArg LocalData hp).mpr d) children =
      StoredTree.node identity p d children := by
  cases hp
  rfl

theorem materialize_eq (t : StoredTree n) : t.materialize = t := by
  cases t with
  | node identity p d children =>
    rw [StoredTree.materialize]
    apply (node_mpr (Materialize.pool_eq p) identity d _).trans
    congr 1
    have he : children.map (fun a => (a.1, a.2.materialize)) = children.map id := by
      apply List.map_congr_left
      intro a ha
      rw [materialize_eq a.2]
      rfl
    simpa using he
termination_by sizeOf t
decreasing_by
  have h := List.sizeOf_lt_of_mem ha
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

structure Active (p : Parameters) (n : ℕ) where
  tree : StoredTree n
  counter : ℕ
  wellFormed : tree.erase.WellFormed
  coherent : tree.erase.Coherent
  bounded : TreeBounded tree.erase
  normal : AllNodes (ready p) tree
  full : tree.pool.members = Finset.univ

def initialActive (p : Parameters) (N : ℕ) : Active p (N + 2) where
  tree := StoredTree.initial N
  counter := 1
  wellFormed := by simpa only [StoredTree.erase_initial] using initial_wellFormed N
  coherent := by simpa only [StoredTree.erase_initial] using initial_coherent N
  bounded := by simpa only [StoredTree.erase_initial] using initial_bounded N
  normal := StoredReady.initial_ready p.repair.scale p.repair.D p.repair.H
    p.repair.degree_pos p.repair.path_two N
  full := rfl

def Active.install {p : Parameters} (s : Active p n) {a b : Fin n}
    (r : StoredRouting.Answered (ready p) (RepairRecord p n) s.tree a b) : Active p n where
  tree := r.next.materialize
  counter := r.counter
  wellFormed := by simpa only [StoredTree.erase_materialize] using r.wellFormed
  coherent := by simpa only [StoredTree.erase_materialize] using r.coherent
  bounded := by simpa only [StoredTree.erase_materialize] using r.bounded s.bounded
  normal := by rw [materialize_eq]; exact r.ready
  full := by rw [materialize_eq, r.members]; exact s.full

def answerOfBool (forward : Bool) : Answer := if forward then .less else .greater

@[simp] theorem earlier_answerOfBool (q : Query n) (forward : Bool) :
    earlier ⟨q, answerOfBool forward⟩ = firstLabel q.left q.right forward := by
  cases forward <;> rfl

@[simp] theorem later_answerOfBool (q : Query n) (forward : Bool) :
    later ⟨q, answerOfBool forward⟩ = secondLabel q.left q.right forward := by
  cases forward <;> rfl

structure Response {p : Parameters} (s : Active p n) (q : Query n) where
  answer : Answer
  next : Active p n
  record : Option (RepairRecord p n)
  charge : ℚ
  monotone : ∀ x y, s.tree.pool.system.edge x y = true → next.tree.pool.system.edge x y = true
  answered : next.tree.pool.system.edge (earlier ⟨q, answer⟩) (later ⟨q, answer⟩) = true
  retention : (s.tree.erase.count : ℚ) ≤ charge * next.tree.erase.count

def respond {p : Parameters} (s : Active p n) (q : Query n) : Response s q :=
  if hless : s.tree.pool.system.edge q.left q.right = true then
    ⟨.less, s, none, 1, fun _ _ h => h, hless, by simp⟩
  else if hgreater : s.tree.pool.system.edge q.right q.left = true then
    ⟨.greater, s, none, 1, fun _ _ h => h, hgreater, by simp⟩
  else
    let result := answerUnknown p s.tree s.wellFormed s.coherent s.normal q.left q.right
      (by rw [s.full]; exact Finset.mem_univ _) (by rw [s.full]; exact Finset.mem_univ _)
      hless hgreater s.counter
    { answer := answerOfBool result.forward
      next := s.install result
      record := some result.payload
      charge := result.charge
      monotone := by
        intro x y hxy
        change result.next.materialize.pool.system.edge x y = true
        rw [materialize_eq, result.edges]
        exact (Safety.closedAdd_edge _ _ _ _ _).mpr (Or.inl hxy)
      answered := by
        change result.next.materialize.pool.system.edge _ _ = true
        rw [materialize_eq, result.edges, earlier_answerOfBool, later_answerOfBool]
        exact (Safety.closedAdd_edge _ _ _ _ _).mpr (Or.inr
          ⟨s.tree.pool.invariant.closed.refl _, s.tree.pool.invariant.closed.refl _⟩)
      retention := by
        change (s.tree.erase.count : ℚ) ≤ result.charge * result.next.materialize.erase.count
        rw [StoredTree.erase_materialize]
        exact result.retention }

structure Frozen (n : ℕ) where
  ranks : Vector (Fin n) n
  injective : Function.Injective (fun x : Fin n => ranks[x])

def Frozen.rows (f : Frozen n) : Rows (Fin n) := fun x y => decide (f.ranks[x] ≤ f.ranks[y])

theorem Frozen.ordered (f : Frozen n) : PublicOrder.IsOrder f.rows where
  refl x := by simp [Frozen.rows]
  trans x y z hxy hyz := by
    exact decide_eq_true (le_trans (of_decide_eq_true hxy) (of_decide_eq_true hyz))
  antisymm x y hxy hyx := f.injective (le_antisymm (of_decide_eq_true hxy) (of_decide_eq_true hyx))

def freeze {p : Parameters} (s : Active p n) : Frozen n where
  ranks := Vector.ofFn (PublicOrder.extensionRank s.tree.pool.system.edge)
  injective := by
    simpa using PublicOrder.extensionRank_injective s.tree.pool.system.edge

theorem freeze_monotone {p : Parameters} (s : Active p n) (x y : Fin n)
    (hxy : s.tree.pool.system.edge x y = true) : (freeze s).rows x y = true := by
  apply decide_eq_true
  simp only [freeze, Fin.getElem_fin, Vector.getElem_ofFn]
  by_cases he : x = y
  · subst y
    exact le_rfl
  · exact (PublicOrder.extensionRank_strict
      ⟨s.tree.pool.invariant.closed.refl, s.tree.pool.invariant.closed.trans, s.tree.pool.invariant.antisymm⟩
      hxy he).le

def Frozen.answer (f : Frozen n) (q : Query n) : Answer :=
  if f.ranks[q.left] < f.ranks[q.right] then .less else .greater

theorem Frozen.answered (f : Frozen n) (q : Query n) :
    f.rows (earlier ⟨q, f.answer q⟩) (later ⟨q, f.answer q⟩) = true := by
  unfold Frozen.answer
  split
  · rename_i h
    exact decide_eq_true h.le
  · rename_i h
    exact decide_eq_true (le_of_not_gt h)

structure State (p : Parameters) (n : ℕ) where
  clock : ℕ
  mode : Sum (Active p n) (Frozen n)

def State.rows {p : Parameters} (s : State p n) : Rows (Fin n) :=
  match s.mode with | .inl a => a.tree.pool.system.edge | .inr f => f.rows

theorem State.ordered {p : Parameters} (s : State p n) : PublicOrder.IsOrder s.rows := by
  cases hm : s.mode with
  | inl a =>
    simp only [State.rows, hm]
    exact ⟨a.tree.pool.invariant.closed.refl, a.tree.pool.invariant.closed.trans,
      a.tree.pool.invariant.antisymm⟩
  | inr f => simpa only [State.rows, hm] using f.ordered

/-- The cutoff is expressed in physical calls, including redundant ones. -/
def step {p : Parameters} (cutoff : ℕ) (s : State p n) (q : Query n) : Answer × State p n :=
  match s.mode with
  | .inl a =>
      if s.clock < cutoff then
        let result := respond a q
        (result.answer, ⟨s.clock + 1, .inl result.next⟩)
      else
        let f := freeze a
        (f.answer q, ⟨s.clock + 1, .inr f⟩)
  | .inr f => (f.answer q, ⟨s.clock + 1, .inr f⟩)

theorem step_clock {p : Parameters} (cutoff : ℕ) (s : State p n) (q : Query n) :
    (step cutoff s q).2.clock = s.clock + 1 := by
  unfold step
  split
  · split <;> rfl
  · rfl

theorem step_monotone {p : Parameters} (cutoff : ℕ) (s : State p n) (q : Query n)
    (x y : Fin n) (hxy : s.rows x y = true) : (step cutoff s q).2.rows x y = true := by
  cases hm : s.mode with
  | inl a =>
    have ha : a.tree.pool.system.edge x y = true := by simpa only [State.rows, hm] using hxy
    by_cases hc : s.clock < cutoff
    · simpa only [step, hm, if_pos hc, State.rows] using (respond a q).monotone x y ha
    · simpa only [step, hm, if_neg hc, State.rows] using freeze_monotone a x y ha
  | inr f => simpa only [step, hm, State.rows] using hxy

theorem step_answered {p : Parameters} (cutoff : ℕ) (s : State p n) (q : Query n) :
    (step cutoff s q).2.rows (earlier ⟨q, (step cutoff s q).1⟩)
      (later ⟨q, (step cutoff s q).1⟩) = true := by
  cases hm : s.mode with
  | inl a =>
    by_cases hc : s.clock < cutoff
    · simpa only [step, hm, if_pos hc, State.rows] using (respond a q).answered
    · simpa only [step, hm, if_neg hc, State.rows] using (freeze a).answered q
  | inr f => simpa only [step, hm, State.rows] using f.answered q

def machine (p : Parameters) (N cutoff : ℕ) : OnlineMachine.Machine (N + 2) where
  State := State p (N + 2)
  initial := ⟨0, .inl (initialActive p N)⟩
  step := step cutoff
  rows := State.rows
  ordered := State.ordered
  monotone := step_monotone cutoff
  answered := step_answered cutoff

theorem consistent (p : Parameters) (N cutoff : ℕ) (t : DecisionTree (N + 2)) :
    ∃ π : Ranking (N + 2), Compatible π (t.run (machine p N cutoff).strategy []).observations :=
  (machine p N cutoff).strategy_consistent t

end SortingAdversary.Optimal.ControllerMachine
