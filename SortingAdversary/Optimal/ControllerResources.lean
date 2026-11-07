import SortingAdversary.Optimal.MeasuredMachine
import SortingAdversary.Optimal.LedgerRun

/-!
# Polynomial allocator and tree resources on actual reachable executions

One primitive repair can create at most one child. The real normalizer has
at most `n+n²` primitive steps, so the actual allocator counter has a fixed
polynomial bound before freezing. The proof below follows actual responses
and the bounded machine's replay; no resource invariant is supplied by the
caller. Immutable identities use the already proved chronological ledger.
-/

namespace SortingAdversary.Optimal.ControllerResources

open WidthRepair RecursiveController ControllerMachine ControllerRun
open PoolTree.Tree PoolTreeAccounting PoolTreeTraversal TreeChronology

variable {n : ℕ}

theorem replayStep_counter_le (identity : ℕ) {s t : WidthRepair.State n} (step : Step s t)
    (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ) :
    (StoredRepair.replayStep identity step children hw ho counter).counter ≤ counter + 1 := by
  cases step with
  | pin update =>
    change nextIdentityAfter update.result (StoredTree.erasedChildren children) counter ≤ counter + 1
    unfold nextIdentityAfter
    split <;> omega
  | lowerCut => exact Nat.le_succ counter
  | upperCut => exact Nat.le_succ counter

theorem replayTrace_counter_le (identity : ℕ) {s t : WidthRepair.State n} (trace : Trace s t)
    (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ) :
    (StoredRepair.replayTrace identity trace children hw ho counter).counter ≤ counter + trace.length := by
  induction trace generalizing children counter with
  | nil => exact le_rfl
  | cons head tail ih =>
    let first := StoredRepair.replayStep identity head children hw ho counter
    have hh := replayStep_counter_le identity head children hw ho counter
    have ht := ih first.children first.wellFormed first.coherent first.counter
    change (StoredRepair.replayTrace identity tail first.children first.wellFormed
      first.coherent first.counter).counter ≤ counter + (tail.length + 1)
    change first.counter ≤ counter + 1 at hh
    omega

theorem stop_counter_le (p : Parameters) (t : StoredTree n)
    (hw : t.erase.WellFormed) (ho : t.erase.Coherent)
    (normal : StoredRouting.AllNodes (ready p) t)
    (a b : Fin n) (ha : a ∈ t.pool.members) (hb : b ∈ t.pool.members)
    (hab : t.pool.system.edge a b ≠ true) (hba : t.pool.system.edge b a ≠ true)
    (hstop : ¬ ∃ c, t.pool.pins a = some c ∧ t.pool.pins b = some c) (counter : ℕ) :
    (RecursiveController.stop p t hw ho normal a b ha hb hab hba hstop counter).counter ≤
      counter + (n + n * n) := by
  cases t with
  | node identity q d children =>
    let answer := RecursiveController.stop p (.node identity q d children) hw ho normal
      a b ha hb hab hba hstop counter
    let record := answer.payload
    have ht := replayTrace_counter_le record.identity record.result.trace record.children
      record.wellFormed record.coherent record.counter
    have hl := record.result.steps_le_quadratic
    change record.replay.counter ≤ counter + (n + n * n)
    change record.replay.counter ≤ record.counter + record.result.trace.length at ht
    have hc : record.counter = counter := rfl
    omega

/-- The recursive child descent never advances the global allocator. -/
theorem route_counter_le {P : StoredRouting.LocalProperty n} {Payload : Type*}
    (stop : StoredRouting.Stopper P Payload) (stable : StoredRouting.DelegationStable P)
    (delegate : ℕ → Fin n → Fin n → Payload → Payload) (B : ℕ)
    (hstop : ∀ t hw ho normal a b ha hb hab hba hs counter,
      (stop t hw ho normal a b ha hb hab hba hs counter).counter ≤ counter + B)
    (t : StoredTree n) (hw : t.erase.WellFormed) (ho : t.erase.Coherent)
    (normal : StoredRouting.AllNodes P t)
    (a b : Fin n) (ha : a ∈ t.pool.members) (hb : b ∈ t.pool.members)
    (hab : t.pool.system.edge a b ≠ true) (hba : t.pool.system.edge b a ≠ true) (counter : ℕ) :
    (StoredRouting.routeUnknown stop stable delegate t hw ho normal a b ha hb hab hba counter).counter ≤
      counter + B := by
  cases t with
  | node identity q d children =>
    rw [StoredRouting.routeUnknown.eq_1]
    split
    next found => exact hstop _ _ _ _ _ _ _ _ _ _ _ _
    next child found =>
      have hsize : sizeOf child.val.2 < sizeOf (StoredTree.node identity q d children) := by
        have hh := List.sizeOf_lt_of_mem child.property
        rcases child with ⟨⟨key, subtree⟩, hm⟩
        simp only [Prod.mk.sizeOf_spec] at hh
        simp only [StoredTree.node.sizeOf_spec]
        omega
      exact route_counter_le stop stable delegate B hstop child.val.2 _ _ _ a b _ _ _ _ counter
termination_by sizeOf t
decreasing_by
  subst t
  exact hsize

theorem answerUnknown_counter_le (p : Parameters) (t : StoredTree n)
    (hw : t.erase.WellFormed) (ho : t.erase.Coherent)
    (normal : StoredRouting.AllNodes (ready p) t)
    (a b : Fin n) (ha : a ∈ t.pool.members) (hb : b ∈ t.pool.members)
    (hab : t.pool.system.edge a b ≠ true) (hba : t.pool.system.edge b a ≠ true) (counter : ℕ) :
    (answerUnknown p t hw ho normal a b ha hb hab hba counter).counter ≤ counter + (n + n * n) :=
  route_counter_le (RecursiveController.stop p) _ _ (n + n * n) (stop_counter_le p)
    t hw ho normal a b ha hb hab hba counter

theorem respond_counter_le {p : Parameters} (s : ControllerMachine.Active p n) (q : Query n) :
    (ControllerMachine.respond s q).next.counter ≤ s.counter + (n + n * n) := by
  by_cases hl : s.tree.pool.system.edge q.left q.right = true
  · erw [ControllerMachine.respond, dif_pos hl]
    exact Nat.le_add_right ..
  · by_cases hg : s.tree.pool.system.edge q.right q.left = true
    · erw [ControllerMachine.respond, dif_neg hl, dif_pos hg]
      exact Nat.le_add_right ..
    · erw [ControllerMachine.respond, dif_neg hl, dif_neg hg]
      exact answerUnknown_counter_le p s.tree s.wellFormed s.coherent s.normal q.left q.right
        _ _ hl hg s.counter

theorem activeRun_counter_le {p : Parameters} {s final : ControllerMachine.Active p n}
    {observations : History n} (run : ActiveRun p s observations final) :
    final.counter ≤ s.counter + observations.length * (n + n * n) := by
  induction run with
  | nil => simp
  | cons s q tail ih =>
    have hs := respond_counter_le s q
    simp only [List.length_cons]
    nlinarith

theorem activeRun_append {p : Parameters} {s middle final : ControllerMachine.Active p n}
    {first second : History n} (head : ActiveRun p s first middle) (tail : ActiveRun p middle second final) :
    ActiveRun p s (first ++ second) final := by
  induction head with
  | nil => exact tail
  | cons s q rest ih => exact .cons s q (ih tail)

/-- Histories supplied to a strategy may contain arbitrary recorded
answers. This witness uses the responses actually computed during replay. -/
def Reached (p : Parameters) (N cutoff : ℕ) : BoundedControllerMachine.State p (N + 2) cutoff → Prop
  | .active clock state => ∃ observations,
      ActiveRun p (initialActive p N) observations state ∧ observations.length = clock.val
  | .frozen _ => True

theorem reached_step (p : Parameters) (N cutoff : ℕ)
    (state : BoundedControllerMachine.State p (N + 2) cutoff) (q : Query (N + 2))
    (h : Reached p N cutoff state) : Reached p N cutoff (BoundedControllerMachine.step state q).2 := by
  cases state with
  | active clock state =>
    obtain ⟨observations, run, hlen⟩ := h
    by_cases hc : clock.val < cutoff
    · simp only [BoundedControllerMachine.step, dif_pos hc, Reached]
      refine ⟨observations ++ [⟨q, (ControllerMachine.respond state q).answer⟩],
        activeRun_append run (.cons state q (.nil _)), ?_⟩
      simp only [List.length_append, List.length_cons, List.length_nil, zero_add, hlen]
    · simp only [BoundedControllerMachine.step, dif_neg hc, Reached]
  | frozen frozen => exact True.intro

theorem replay_reached (p : Parameters) (N cutoff : ℕ) (past : History (N + 2)) :
    Reached p N cutoff ((BoundedControllerMachine.machine p N cutoff).replay past) := by
  induction past with
  | nil => exact ⟨[], .nil _, rfl⟩
  | cons observation past ih =>
    rw [OnlineMachine.Machine.replay_cons]
    exact reached_step p N cutoff _ observation.query ih

def counterBound (n : ℕ) : ℕ := 1 + 2 * n * (n + 2) * (n + n * n)

theorem cutoff_le (n : ℕ) : UniformAdversary.cutoff n ≤ 2 * n * (n + 2) := by
  have h := Nat.log_le_self 2 (n + 1)
  exact Nat.mul_le_mul_left (2 * n) (by simpa only [Parameters.logCap] using Nat.add_le_add_right h 1)

theorem reached_resources (p : Parameters) (N cutoff : ℕ)
    (clock : Fin (cutoff + 1)) (state : ControllerMachine.Active p (N + 2))
    (h : Reached p N cutoff (.active clock state)) :
    state.counter ≤ 1 + cutoff * ((N + 2) + (N + 2) * (N + 2)) ∧
      Allocated state.tree.erase state.counter := by
  obtain ⟨observations, run, hlen⟩ := h
  refine ⟨?_, (LedgerRun.initial_spec p N run).allocated⟩
  have hc := activeRun_counter_le run
  have ht : observations.length ≤ cutoff := by rw [hlen]; exact Nat.le_of_lt_succ clock.isLt
  have hm := Nat.mul_le_mul_right ((N + 2) + (N + 2) * (N + 2)) ht
  change state.counter ≤ 1 + observations.length * _ at hc
  omega

theorem reached_uniform_counter (p : Parameters) (N : ℕ)
    (clock : Fin (UniformAdversary.cutoff (N + 2) + 1))
    (state : ControllerMachine.Active p (N + 2))
    (h : Reached p N (UniformAdversary.cutoff (N + 2)) (.active clock state)) :
    state.counter ≤ counterBound (N + 2) := by
  apply (reached_resources p N _ clock state h).1.trans
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (cutoff_le (N + 2))) 1

theorem reached_uniform_identity (p : Parameters) (N : ℕ)
    (clock : Fin (UniformAdversary.cutoff (N + 2) + 1))
    (state : ControllerMachine.Active p (N + 2))
    (h : Reached p N (UniformAdversary.cutoff (N + 2)) (.active clock state))
    (identity : ℕ) (hi : identity ∈ TreeChronology.identities state.tree.erase) :
    identity < counterBound (N + 2) :=
  ((reached_resources p N _ clock state h).2.below identity hi).trans_le
    (reached_uniform_counter p N clock state h)

theorem measured_replay_reached (p : Parameters) (N cutoff : ℕ)
    (executor : MeasuredController.AnswerExecutor p (N + 2)) (past : History (N + 2)) :
    Reached p N cutoff
      (MeasuredController.erase ((MeasuredController.machine p N cutoff executor).replay past)) := by
  rw [MeasuredController.replay_erase]
  exact replay_reached p N cutoff past

theorem measured_replay_resources (p : Parameters) (N : ℕ)
    (executor : MeasuredController.AnswerExecutor p (N + 2)) (past : History (N + 2))
    (clock : Fin (UniformAdversary.cutoff (N + 2) + 1))
    (state : MeasuredController.Active p (N + 2))
    (he : (MeasuredController.machine p N (UniformAdversary.cutoff (N + 2)) executor).replay past =
      .active clock state) :
    state.state.counter ≤ counterBound (N + 2) ∧
      Allocated state.state.tree.erase state.state.counter := by
  have h := measured_replay_reached p N (UniformAdversary.cutoff (N + 2)) executor past
  rw [he] at h
  exact ⟨reached_uniform_counter p N clock state.state h,
    (reached_resources p N _ clock state.state h).2⟩

theorem measured_replay_identity (p : Parameters) (N : ℕ)
    (executor : MeasuredController.AnswerExecutor p (N + 2)) (past : History (N + 2))
    (clock : Fin (UniformAdversary.cutoff (N + 2) + 1))
    (state : MeasuredController.Active p (N + 2))
    (he : (MeasuredController.machine p N (UniformAdversary.cutoff (N + 2)) executor).replay past =
      .active clock state)
    (identity : ℕ) (hi : identity ∈ TreeChronology.identities state.state.tree.erase) :
    identity < counterBound (N + 2) := by
  have h := measured_replay_resources p N executor past clock state he
  exact (h.2.below identity hi).trans_le h.1

theorem active_nodes {p : Parameters} (state : ControllerMachine.Active p n) (hn : 0 < n) :
    state.tree.erase.nodes + 1 ≤ 2 * n := by
  have hnonempty : state.tree.erase.pool.members.Nonempty := by
    rw [StoredTree.erase_pool, state.full]
    exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have h := nodes_add_one_le_twice_members state.wellFormed hnonempty
  simpa only [StoredTree.erase_pool, state.full, Finset.card_univ, Fintype.card_fin] using h

theorem active_palette {p : Parameters} (state : ControllerMachine.Active p n)
    (entry : ℕ × PoolState.Pool n) (he : entry ∈ storedPools state.tree.erase) :
    entry.2.palette ≤ 2 * n + 1 := by
  have hp := (state.bounded entry he).twice
  have hm : entry.2.members.card ≤ n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ entry.2.members
  omega

theorem active_storedPools {p : Parameters} (state : ControllerMachine.Active p n) (hn : 0 < n) :
    (storedPools state.tree.erase).length + 1 ≤ 2 * n := by
  rw [storedPools_length state.wellFormed]
  exact active_nodes state hn

theorem counterBound_polynomial (n : ℕ) : counterBound n ≤ 20 * (n + 1) ^ 4 := by
  unfold counterBound
  ring_nf
  gcongr <;> norm_num <;> omega

end SortingAdversary.Optimal.ControllerResources
