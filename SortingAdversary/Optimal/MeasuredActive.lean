import SortingAdversary.Optimal.MeasuredControllerTypes
import SortingAdversary.Optimal.ControllerMachine

/-!
# Measured responses of the active online machine

Known comparisons read cached public rows. Unknown comparisons invoke the
measured recursive router and retain only its next tree and identity counter.
The accounting payload and rational product are absent from this runtime.
-/

namespace SortingAdversary.Optimal.MeasuredController

open RepresentationWork RecursiveController StoredRouting

variable {n : ℕ} {p : Parameters}

abbrev AnswerExecutor (p : Parameters) (n : ℕ) :=
  @RouteExecutor n (ready p) (RepairRecord p n) (RecursiveController.stop p)
    (PassiveLocalState.ready_delegation_stable p.repair.scale p.repair.D p.repair.H)
    (fun _ _ _ record => record)

structure Active (p : Parameters) (n : ℕ) where
  state : ControllerMachine.Active p n
  access : TreeAccess state.tree
  cached : access.Bound 2

def Active.initial (p : Parameters) (N : ℕ) : Active p (N + 2) :=
  ⟨ControllerMachine.initialActive p N, TreeAccess.initial N, TreeAccess.initial_bound N⟩

def installed {s : ControllerMachine.Active p n} {a b : Fin n}
    {reference : Answered (ready p) (RepairRecord p n) s.tree a b}
    (out : Output (Core.ofAnswered reference)) : ControllerMachine.Active p n where
  tree := out.core.next
  counter := out.core.counter
  wellFormed := by
    have h := congrArg Core.next out.actual
    change out.core.next = reference.next at h
    rw [h]
    exact reference.wellFormed
  coherent := by
    have h := congrArg Core.next out.actual
    change out.core.next = reference.next at h
    rw [h]
    exact reference.coherent
  bounded := by
    have h := congrArg Core.next out.actual
    change out.core.next = reference.next at h
    rw [h]
    exact reference.bounded s.bounded
  normal := by
    have h := congrArg Core.next out.actual
    change out.core.next = reference.next at h
    rw [h]
    exact reference.ready
  full := by
    have h := congrArg Core.next out.actual
    change out.core.next = reference.next at h
    rw [h, reference.members]
    exact s.full

theorem installed_eq {s : ControllerMachine.Active p n} {a b : Fin n}
    {reference : Answered (ready p) (RepairRecord p n) s.tree a b}
    (out : Output (Core.ofAnswered reference)) : installed out = s.install reference := by
  unfold installed ControllerMachine.Active.install
  have ht := congrArg Core.next out.actual
  have hc := congrArg Core.counter out.actual
  dsimp only [Core.ofAnswered] at ht hc
  simp only [ControllerMachine.materialize_eq, ht, hc]

def Active.install (s : Active p n) {a b : Fin n}
    {reference : Answered (ready p) (RepairRecord p n) s.state.tree a b}
    (out : Output (Core.ofAnswered reference)) : Active p n :=
  ⟨installed out, out.access, out.cached⟩

structure Response (s : Active p n) (q : Query n) where
  answer : Answer
  next : Active p n
  answer_eq : answer = (ControllerMachine.respond s.state q).answer
  next_eq : next.state = (ControllerMachine.respond s.state q).next

def respond (executor : AnswerExecutor p n) (s : Active p n) (q : Query n) :
    PrimitiveWork.Result (Response s q) :=
  let rows := s.access.root
  let first := rows.publicRow q.left q.right
  if hl : first.value = true then
    have hless : s.state.tree.pool.system.edge q.left q.right = true :=
      (rows.publicRow_value q.left q.right).symm.trans hl
    ⟨⟨.less, s, by simp only [ControllerMachine.respond, dif_pos hless],
      by simp only [ControllerMachine.respond, dif_pos hless]⟩, first.work + 4⟩
  else
    have hless : s.state.tree.pool.system.edge q.left q.right ≠ true :=
      fun h => hl ((rows.publicRow_value q.left q.right).trans h)
    let second := rows.publicRow q.right q.left
    if hg : second.value = true then
      have hgreater : s.state.tree.pool.system.edge q.right q.left = true :=
        (rows.publicRow_value q.right q.left).symm.trans hg
      ⟨⟨.greater, s, by simp only [ControllerMachine.respond, dif_neg hless, dif_pos hgreater],
        by simp only [ControllerMachine.respond, dif_neg hless, dif_pos hgreater]⟩,
        first.work + second.work + 6⟩
    else
      have hgreater : s.state.tree.pool.system.edge q.right q.left ≠ true :=
        fun h => hg ((rows.publicRow_value q.right q.left).trans h)
      let result := executor s.state.tree s.access s.cached s.state.wellFormed s.state.coherent s.state.normal
        q.left q.right (by rw [s.state.full]; exact Finset.mem_univ _)
        (by rw [s.state.full]; exact Finset.mem_univ _) hless hgreater s.state.counter
      let next := s.install result.value
      ⟨⟨ControllerMachine.answerOfBool result.value.core.forward, next, by
        have h := congrArg Core.forward result.value.actual
        change result.value.core.forward = (answerUnknown p s.state.tree _ _ _ q.left q.right _ _
          hless hgreater s.state.counter).forward at h
        simp only [ControllerMachine.respond, dif_neg hless, dif_neg hgreater, h], by
        have h := installed_eq result.value
        simpa only [next, Active.install, ControllerMachine.respond, dif_neg hless, dif_neg hgreater,
          RecursiveController.answerUnknown] using h⟩,
        first.work + second.work + result.work + 24⟩

def AnswerBound (executor : AnswerExecutor p n) (work : ℕ) : Prop :=
  ∀ (t : StoredTree n) (access : TreeAccess t) (cached : access.Bound 2)
    (hw : t.erase.WellFormed) (ho : t.erase.Coherent) (normal : AllNodes (ready p) t)
    (a b : Fin n) (ha : a ∈ t.pool.members) (hb : b ∈ t.pool.members)
    (hab : t.pool.system.edge a b ≠ true) (hba : t.pool.system.edge b a ≠ true) (counter : ℕ),
    PoolPalette.TreeBounded t.erase →
      (executor t access cached hw ho normal a b ha hb hab hba counter).work ≤ work

theorem respond_work_le (executor : AnswerExecutor p n) (bound : ℕ) (hbound : AnswerBound executor bound)
    (s : Active p n) (q : Query n) : (respond executor s q).work ≤ bound + 28 := by
  have ha := s.access.root_bound s.cached
  have hfirst := ha.publicRow q.left q.right
  have hsecond := ha.publicRow q.right q.left
  unfold respond
  dsimp only
  split
  · dsimp only; omega
  · split
    · dsimp only; omega
    · rename_i hl hg
      have hless : s.state.tree.pool.system.edge q.left q.right ≠ true :=
        fun h => hl ((s.access.root.publicRow_value q.left q.right).trans h)
      have hgreater : s.state.tree.pool.system.edge q.right q.left ≠ true :=
        fun h => hg ((s.access.root.publicRow_value q.right q.left).trans h)
      have hr := hbound s.state.tree s.access s.cached s.state.wellFormed s.state.coherent s.state.normal
        q.left q.right (by rw [s.state.full]; exact Finset.mem_univ _)
        (by rw [s.state.full]; exact Finset.mem_univ _) hless hgreater s.state.counter s.state.bounded
      dsimp only
      omega

end SortingAdversary.Optimal.MeasuredController
