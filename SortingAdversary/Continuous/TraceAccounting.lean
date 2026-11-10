import SortingAdversary.Continuous.QueriedCompression
import SortingAdversary.Continuous.ArcBudget

/-!
# Accounting derived from concrete tree executions

Actions below perform the actual refinement, answer recording, and
normalization operations. Their gains and losses are computed from the actual
volumes before and after the action. Path batches aggregate those individual
gains by their distinct reduced anchors. The global volume identity, path
weight identity, and arc credits are derived by induction on execution.
-/

namespace SortingAdversary.Continuous.TraceAccounting

noncomputable section

open FiniteAveraging OrderRegion TreeState MeasureTheory Set
open scoped BigOperators

variable {n : ℕ}

structure Move (n : ℕ) where
  item : Fin n
  anchor : DyadicAnchor
  order : List (Fin n)

def Move.apply (m : Move n) (s : State n ℝ) : State n ℝ :=
  TreeState.normalize (refineAt s m.item (m.anchor.coordinate : ℝ)) m.order

def Move.paths (m : Move n) (p : Fin n → List DyadicAnchor) : Fin n → List DyadicAnchor :=
  Function.update p m.item (p m.item ++ [m.anchor])

noncomputable def Move.gain (m : Move n) (s : State n ℝ) : ℝ :=
  log2 (nodeVolume (m.apply s).system) - log2 (nodeVolume s.system)

def applyMoves : State n ℝ → List (Move n) → State n ℝ
  | s, [] => s
  | s, m :: ms => applyMoves (m.apply s) ms

def movePaths : (Fin n → List DyadicAnchor) → List (Move n) → Fin n → List DyadicAnchor
  | p, [] => p
  | p, m :: ms => movePaths (m.paths p) ms

noncomputable def gainRecords : State n ℝ → List (Move n) → List (DyadicAnchor × ℝ)
  | _, [] => []
  | s, m :: ms => (m.anchor, m.gain s) :: gainRecords (m.apply s) ms

noncomputable def gainsAt : List (DyadicAnchor × ℝ) → DyadicAnchor → ℝ
  | [], _ => 0
  | (d, g) :: rs, c => (if c = d then g else 0) + gainsAt rs c

theorem gainRecords_anchors (s : State n ℝ) (ms : List (Move n)) :
    (gainRecords s ms).map Prod.fst = ms.map Move.anchor := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih => simp only [gainRecords, List.map_cons, ih]

theorem gainsAt_sum (rs : List (DyadicAnchor × ℝ)) (S : Finset DyadicAnchor)
    (hs : ∀ r ∈ rs, r.1 ∈ S) : ∑ c ∈ S, gainsAt rs c = (rs.map Prod.snd).sum := by
  classical
  induction rs with
  | nil => simp [gainsAt]
  | cons r rs ih =>
    have hr := hs r (by simp)
    have ht := ih (fun z hz => hs z (by simp [hz]))
    simp only [gainsAt, Finset.sum_add_distrib, List.map_cons, List.sum_cons]
    rw [Finset.sum_ite_eq' S r.1, if_pos hr, ht]

theorem gainRecords_sum (s : State n ℝ) (ms : List (Move n)) :
    ((gainRecords s ms).map Prod.snd).sum =
      log2 (nodeVolume (applyMoves s ms).system) - log2 (nodeVolume s.system) := by
  induction ms generalizing s with
  | nil => simp [gainRecords, applyMoves]
  | cons m ms ih =>
    simp only [gainRecords, List.map_cons, List.sum_cons, ih, Move.gain, applyMoves]
    ring

noncomputable def pathEvent (s : State n ℝ) (ms : List (Move n)) : RefinementEvent :=
  .path (ms.map Move.anchor).toFinset (gainsAt (gainRecords s ms))

theorem pathEvent_gain (s : State n ℝ) (ms : List (Move n)) :
    (pathEvent s ms).gain =
      log2 (nodeVolume (applyMoves s ms).system) - log2 (nodeVolume s.system) := by
  change (∑ c ∈ (ms.map Move.anchor).toFinset, gainsAt (gainRecords s ms) c) = _
  rw [gainsAt_sum, gainRecords_sum]
  intro r hr
  apply List.mem_toFinset.mpr
  rw [← gainRecords_anchors s ms]
  exact List.mem_map.mpr ⟨r, hr, rfl⟩

theorem movePaths_weight (k : ℝ) (p : Fin n → List DyadicAnchor) (ms : List (Move n)) :
    pathsWeight k (movePaths p ms) =
      pathsWeight k p * ((ms.map Move.anchor).map (fun c => anchorWeight k c.1)).prod := by
  induction ms generalizing p with
  | nil => simp [movePaths]
  | cons m ms ih =>
    rw [movePaths, ih]
    rw [show pathsWeight k (m.paths p) = pathsWeight k p * anchorWeight k m.anchor.1 from
      pathsWeight_append k p m.item m.anchor]
    simp only [List.map_cons, List.prod_cons]
    ring

theorem pathEvent_weight (k : ℝ) (s : State n ℝ) (p : Fin n → List DyadicAnchor)
    (ms : List (Move n)) (hn : (ms.map Move.anchor).Nodup) :
    pathsWeight k (movePaths p ms) = pathsWeight k p * (pathEvent s ms).weightProduct k := by
  rw [movePaths_weight]
  change pathsWeight k p * ((ms.map Move.anchor).map (fun c => anchorWeight k c.1)).prod =
    pathsWeight k p * ∏ c ∈ (ms.map Move.anchor).toFinset, anchorWeight k c.1
  rw [List.prod_toFinset _ hn]

theorem move_arc_le (m : Move n) (s : State n ℝ) :
    (ArcBudget.arcs (m.apply s).system).card ≤ (ArcBudget.arcs s.system).card := by
  simpa only [Move.apply, TreeState.normalize, refineAt, ArcBudget.arcs_normalize] using
    ArcBudget.reset_arc_le s.system m.item (m.anchor.coordinate : ℝ)

theorem move_arc_identity (m : Move n) (s : State n ℝ) :
    (ArcBudget.arcs (m.apply s).system).card + (ArcBudget.incident s.system m.item).card =
      (ArcBudget.arcs s.system).card := by
  simpa only [Move.apply, TreeState.normalize, refineAt, ArcBudget.arcs_normalize] using
    ArcBudget.reset_arc_identity s.system m.item (m.anchor.coordinate : ℝ)

theorem applyMoves_arc_le (s : State n ℝ) (ms : List (Move n)) :
    (ArcBudget.arcs (applyMoves s ms).system).card ≤ (ArcBudget.arcs s.system).card := by
  induction ms generalizing s with
  | nil => exact le_rfl
  | cons m ms ih => exact (ih (m.apply s)).trans (move_arc_le m s)

inductive Action (n : ℕ) where
  | selection (move : Move n)
  | degree (move : Move n)
  | path (moves : List (Move n))
  | answer (query : Query n) (answer : Answer) (order : List (Fin n))

structure Frame (n : ℕ) where
  state : State n ℝ
  paths : Fin n → List DyadicAnchor
  history : History n
  log : AccountingLog

def initialFrame (n : ℕ) : Frame n := ⟨initial n, fun _ => [], [], ⟨[], []⟩⟩

def Action.nextState (s : State n ℝ) : Action n → State n ℝ
  | .selection m | .degree m => m.apply s
  | .path ms => applyMoves s ms
  | .answer q a order => TreeState.normalize (record s q a) order

def Action.nextPaths (p : Fin n → List DyadicAnchor) : Action n → Fin n → List DyadicAnchor
  | .selection m | .degree m => m.paths p
  | .path ms => movePaths p ms
  | .answer _ _ _ => p

def Action.nextHistory (h : History n) : Action n → History n
  | .answer q a _ => ⟨q, a⟩ :: h
  | _ => h

noncomputable def Action.nextLog (s : State n ℝ) (L : AccountingLog) : Action n → AccountingLog
  | .selection m => ⟨.selection m.anchor (m.gain s) :: L.events, L.losses⟩
  | .degree m => ⟨.degree m.anchor (m.gain s) :: L.events, L.losses⟩
  | .path ms => ⟨pathEvent s ms :: L.events, L.losses⟩
  | .answer q a order => ⟨L.events,
      (log2 (nodeVolume s.system) -
        log2 (nodeVolume (TreeState.normalize (record s q a) order).system)) :: L.losses⟩

noncomputable def execute (F : Frame n) (a : Action n) : Frame n :=
  ⟨a.nextState F.state, a.nextPaths F.paths, a.nextHistory F.history, a.nextLog F.state F.log⟩

noncomputable def run (F : Frame n) (actions : List (Action n)) : Frame n := actions.foldl execute F

/-- The local numeric obligations at the actual states where actions occur.
Every gain here is computed from the displayed concrete mutation. -/
def Action.Valid (k : ℕ) (F : Frame n) : Action n → Prop
  | .selection m => (RefinementEvent.selection m.anchor (m.gain F.state)).Valid k
  | .degree m => (RefinementEvent.degree m.anchor (m.gain F.state)).Valid k ∧
      k ≤ (ArcBudget.incident F.state.system m.item).card
  | .path ms => (ms.map Move.anchor).Nodup ∧ (pathEvent F.state ms).Valid k
  | .answer q a order => log2 (nodeVolume F.state.system) -
      log2 (nodeVolume (TreeState.normalize (record F.state q a) order).system) ≤ answerLoss k

def Valid (k : ℕ) : Frame n → List (Action n) → Prop
  | _, [] => True
  | F, a :: actions => a.Valid k F ∧ Valid k (execute F a) actions

theorem execute_logVolume (F : Frame n) (a : Action n) :
    (execute F a).log.logVolume = F.log.logVolume +
      (log2 (nodeVolume (execute F a).state.system) - log2 (nodeVolume F.state.system)) := by
  cases a <;>
    simp only [execute, Action.nextLog, Action.nextState, AccountingLog.logVolume,
      AccountingLog.totalGain, List.map_cons, List.sum_cons]
  all_goals first | rw [pathEvent_gain] | skip
  all_goals try simp only [RefinementEvent.gain, Move.gain]
  all_goals ring

theorem execute_weight {k : ℕ} (F : Frame n) (a : Action n) (ha : a.Valid k F)
    (hw : pathsWeight k F.paths = F.log.weightProduct k) :
    pathsWeight k (execute F a).paths = (execute F a).log.weightProduct k := by
  cases a with
  | selection m =>
    simp only [execute, Action.nextPaths, Action.nextLog, AccountingLog.weightProduct,
      List.map_cons, List.prod_cons, RefinementEvent.weightProduct]
    rw [show pathsWeight k (m.paths F.paths) = _ from pathsWeight_append k F.paths m.item m.anchor]
    rw [hw]
    exact mul_comm _ _
  | degree m =>
    simp only [execute, Action.nextPaths, Action.nextLog, AccountingLog.weightProduct,
      List.map_cons, List.prod_cons, RefinementEvent.weightProduct]
    rw [show pathsWeight k (m.paths F.paths) = _ from pathsWeight_append k F.paths m.item m.anchor]
    rw [hw]
    exact mul_comm _ _
  | path ms =>
    change pathsWeight k (movePaths F.paths ms) = _
    rw [pathEvent_weight k F.state F.paths ms ha.1, hw]
    exact mul_comm _ _
  | answer q a order => exact hw

theorem execute_arc_budget {k : ℕ} (F : Frame n) (a : Action n) (ha : a.Valid k F)
    (hbudget : (ArcBudget.arcs F.state.system).card + k * F.log.degreeRepairs ≤ F.log.comparisons) :
    (ArcBudget.arcs (execute F a).state.system).card + k * (execute F a).log.degreeRepairs ≤
      (execute F a).log.comparisons := by
  cases a with
  | selection m =>
    have hm := move_arc_le m F.state
    simp only [execute, Action.nextState, Action.nextLog, AccountingLog.degreeRepairs,
      AccountingLog.comparisons, RefinementEvent.degrees, List.map_cons, List.sum_cons,
      zero_add] at hbudget ⊢
    omega
  | degree m =>
    have hm := move_arc_identity m F.state
    have hd := ha.2
    simp only [execute, Action.nextState, Action.nextLog, AccountingLog.degreeRepairs,
      AccountingLog.comparisons, RefinementEvent.degrees, List.map_cons, List.sum_cons,
      Nat.mul_add, Nat.mul_one] at hbudget ⊢
    omega
  | path ms =>
    have hm := applyMoves_arc_le F.state ms
    simp only [execute, Action.nextState, Action.nextLog, AccountingLog.degreeRepairs,
      AccountingLog.comparisons, pathEvent, RefinementEvent.degrees, List.map_cons, List.sum_cons,
      zero_add] at hbudget ⊢
    omega
  | answer q a order =>
    have hm := ArcBudget.record_arc_le F.state q a
    simp only [execute, Action.nextState, Action.nextLog, TreeState.normalize,
      ArcBudget.arcs_normalize, AccountingLog.degreeRepairs, AccountingLog.comparisons,
      List.length_cons] at hbudget ⊢
    omega

/-- These equalities are established below from the empty initial frame and
preserved by actual execution; they are not inputs to the final prefix theorem. -/
def Bookkept (k : ℕ) (F : Frame n) : Prop :=
  log2 (nodeVolume F.state.system) = F.log.logVolume ∧
  pathsWeight k F.paths = F.log.weightProduct k ∧
  (ArcBudget.arcs F.state.system).card + k * F.log.degreeRepairs ≤ F.log.comparisons ∧
  (∀ e ∈ F.log.events, e.Valid k) ∧
  (∀ a ∈ F.log.losses, a ≤ answerLoss k) ∧ F.log.comparisons = F.history.length

theorem execute_bookkept {k : ℕ} (F : Frame n) (a : Action n) (ha : a.Valid k F)
    (hF : Bookkept k F) : Bookkept k (execute F a) := by
  rcases hF with ⟨hv, hw, hb, he, hl, hn⟩
  refine ⟨?_, execute_weight F a ha hw, execute_arc_budget F a ha hb, ?_, ?_, ?_⟩
  · have hd := execute_logVolume F a
    rw [← hv] at hd
    linarith
  · cases a with
    | selection m =>
      intro e hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ha
      · exact he e hmem
    | degree m =>
      intro e hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ha.1
      · exact he e hmem
    | path ms =>
      intro e hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ha.2
      · exact he e hmem
    | answer q a order => exact he
  · cases a with
    | selection m => exact hl
    | degree m => exact hl
    | path ms => exact hl
    | answer q a order =>
      intro b hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ha
      · exact hl b hmem
  · cases a <;> simp only [execute, Action.nextLog, Action.nextHistory,
      AccountingLog.comparisons, List.length_cons] at hn ⊢ <;> omega

theorem initial_volume (n : ℕ) : nodeVolume (initial n : State n ℝ).system = 1 := by
  have hr : region (initial n : State n ℝ).system = Set.univ.pi (fun _ => Ioo (0 : ℝ) 1) := by
    ext X
    simp [region, initial, System.StrictlyFeasible, mem_univ_pi]
  unfold nodeVolume
  rw [hr]
  change ((Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))
    (Set.univ.pi (fun _ => Ioo (0 : ℝ) 1))).toReal = 1
  rw [Measure.pi_pi]
  simp

theorem initial_bookkept (k n : ℕ) : Bookkept k (initialFrame n) := by
  simp [Bookkept, initialFrame, initial_volume, pathsWeight_initial, AccountingLog.logVolume,
    AccountingLog.totalGain, AccountingLog.weightProduct, AccountingLog.degreeRepairs,
    AccountingLog.comparisons, ArcBudget.initial_arcs]

theorem run_bookkept {k : ℕ} (F : Frame n) (actions : List (Action n))
    (hvalid : Valid k F actions) (hF : Bookkept k F) : Bookkept k (run F actions) := by
  induction actions generalizing F with
  | nil => exact hF
  | cons a actions ih => exact ih (execute F a) hvalid.2 (execute_bookkept F a hvalid.1 hF)

def PathsMatch (F : Frame n) : Prop :=
  ∀ i, (F.paths i).map (fun c => (c.coordinate : ℝ)) = F.state.location i

theorem move_paths_match (m : Move n) (s : State n ℝ) (p : Fin n → List DyadicAnchor)
    (hp : ∀ i, (p i).map (fun c => (c.coordinate : ℝ)) = s.location i) :
    ∀ i, (m.paths p i).map (fun c => (c.coordinate : ℝ)) = (m.apply s).location i := by
  intro i
  by_cases hi : i = m.item
  · subst i
    simp [Move.paths, Move.apply, TreeState.normalize, refineAt, hp]
  · simp [Move.paths, Move.apply, TreeState.normalize, refineAt, hi, hp]

theorem moves_paths_match (s : State n ℝ) (p : Fin n → List DyadicAnchor) (ms : List (Move n))
    (hp : ∀ i, (p i).map (fun c => (c.coordinate : ℝ)) = s.location i) :
    ∀ i, (movePaths p ms i).map (fun c => (c.coordinate : ℝ)) = (applyMoves s ms).location i := by
  induction ms generalizing s p with
  | nil => exact hp
  | cons m ms ih => exact ih (m.apply s) (m.paths p) (move_paths_match m s p hp)

theorem execute_paths_match (F : Frame n) (a : Action n) (hp : PathsMatch F) :
    PathsMatch (execute F a) := by
  cases a with
  | selection m => exact move_paths_match m F.state F.paths hp
  | degree m => exact move_paths_match m F.state F.paths hp
  | path ms => exact moves_paths_match F.state F.paths ms hp
  | answer q a order => exact hp

theorem run_paths_match (F : Frame n) (actions : List (Action n)) (hp : PathsMatch F) :
    PathsMatch (run F actions) := by
  induction actions generalizing F with
  | nil => exact hp
  | cons a actions ih => exact ih (execute F a) (execute_paths_match F a hp)

/-- Prefix counting for a concrete execution from the initial state. All
numeric ledger equalities, the arc budget, and the path-weight identity are
derived from its actions. The remaining premises are the state semantics
maintained by the controller and the local gain/answer guarantees. -/
theorem run_initial_prefix {k : ℕ} (hk : 64 ≤ k) (actions : List (Action n))
    (hvalid : Valid k (initialFrame n) actions)
    (hs : (run (initialFrame n) actions).state.Consistent (run (initialFrame n) actions).history)
    (hb : ∀ i, 0 ≤ (run (initialFrame n) actions).state.system.lower i ∧
      (run (initialFrame n) actions).state.system.upper i ≤ 1)
    (hunit : ∀ x ∉ queriedLabels (run (initialFrame n) actions).history,
      IsolatedUnit (run (initialFrame n) actions).state.system x)
    (hempty : ∀ x ∉ queriedLabels (run (initialFrame n) actions).history,
      (run (initialFrame n) actions).paths x = [])
    (hZ : 0 < nodeVolume (run (initialFrame n) actions).state.system) :
    log2 (n.factorial : ℝ) - (1 + prefixOverhead k) * (run (initialFrame n) actions).history.length ≤
      log2 (transcriptCount (run (initialFrame n) actions).history : ℝ) := by
  let F := run (initialFrame n) actions
  have hB := run_bookkept (initialFrame n) actions hvalid (initial_bookkept k n)
  rcases hB with ⟨hv, hw, ha, he, hl, hn⟩
  have hp := run_paths_match (initialFrame n) actions (by intro i; rfl)
  apply QueriedCompression.prefix_count hk F.state F.history hs hb F.paths hp hunit hempty F.log hZ
    hw hv he hl (by dsimp [F]; omega) hn

end
end SortingAdversary.Continuous.TraceAccounting
