import SortingAdversary.Continuous.Controller

/-!
# Exact traces of the rational controller

The executable controller and the real accounting evaluator perform the
same mutations. A successful comparison returns exactly the actions that
produce its new memory, and exactly one observation is added to its history.
Freezing uses an actual linear extension of the existing transcript.
-/

namespace SortingAdversary.Continuous.Controller

open FiniteAveraging OrderRegion TreeState TraceAccounting

variable {n : ℕ}

def Memory.toFrame (M : Memory n) (L : AccountingLog) : Frame n :=
  ⟨M.tree.toReal, M.paths, M.history, L⟩

def Memory.Represents (M : Memory n) (F : Frame n) : Prop :=
  M.tree.toReal = F.state ∧ M.paths = F.paths ∧ M.history = F.history

theorem Memory.represents_toFrame (M : Memory n) (L : AccountingLog) :
    M.Represents (M.toFrame L) := ⟨rfl, rfl, rfl⟩

@[simp] theorem initial_toFrame (L : AccountingLog) :
    (initial n).toFrame L = ⟨TreeState.initial n, fun _ => [], [], L⟩ := by
  simp [initial, Memory.toFrame]

theorem applyMove_tree (M : Memory n) (m : Move n) :
    (applyMove M m).tree.toReal = m.apply M.tree.toReal := by
  simp only [applyMove, normalize_toReal, refineAt_toReal, Move.apply]

@[simp] theorem applyMove_paths (M : Memory n) (m : Move n) :
    (applyMove M m).paths = m.paths M.paths := rfl

@[simp] theorem applyMove_history (M : Memory n) (m : Move n) :
    (applyMove M m).history = M.history := rfl

theorem applyMoves_tree (M : Memory n) (ms : List (Move n)) :
    (applyMoves M ms).tree.toReal = TraceAccounting.applyMoves M.tree.toReal ms := by
  induction ms generalizing M with
  | nil => rfl
  | cons m ms ih =>
    simp only [applyMoves, TraceAccounting.applyMoves, ih, applyMove_tree]

theorem applyMoves_paths (M : Memory n) (ms : List (Move n)) :
    (applyMoves M ms).paths = movePaths M.paths ms := by
  induction ms generalizing M with
  | nil => rfl
  | cons m ms ih => simp only [applyMoves, movePaths, ih, applyMove_paths]

@[simp] theorem applyMoves_history (M : Memory n) (ms : List (Move n)) :
    (applyMoves M ms).history = M.history := by
  induction ms generalizing M with
  | nil => rfl
  | cons m ms ih => exact ih _

theorem applyAction_tree (M : Memory n) (a : Action n) :
    (applyAction M a).tree.toReal = a.nextState M.tree.toReal := by
  cases a with
  | selection m => exact applyMove_tree M m
  | degree m => exact applyMove_tree M m
  | path ms => exact applyMoves_tree M ms
  | answer q a order => simp only [applyAction, Action.nextState, normalize_toReal, record_toReal]

theorem applyAction_paths (M : Memory n) (a : Action n) :
    (applyAction M a).paths = a.nextPaths M.paths := by
  cases a with
  | selection m => rfl
  | degree m => rfl
  | path ms => exact applyMoves_paths M ms
  | answer q a order => rfl

theorem applyAction_history (M : Memory n) (a : Action n) :
    (applyAction M a).history = a.nextHistory M.history := by
  cases a with
  | selection m => rfl
  | degree m => rfl
  | path ms => exact applyMoves_history M ms
  | answer q a order => rfl

theorem applyAction_represents (M : Memory n) (F : Frame n)
    (h : M.Represents F) (a : Action n) :
    (applyAction M a).Represents (execute F a) := by
  rcases h with ⟨ht, hp, hh⟩
  exact ⟨(applyAction_tree M a).trans (congrArg a.nextState ht),
    (applyAction_paths M a).trans (congrArg a.nextPaths hp),
    (applyAction_history M a).trans (congrArg a.nextHistory hh)⟩

theorem runActions_represents (M : Memory n) (F : Frame n)
    (h : M.Represents F) (actions : List (Action n)) :
    (runActions M actions).Represents (TraceAccounting.run F actions) := by
  induction actions generalizing M F with
  | nil => exact h
  | cons a actions ih => exact ih (applyAction M a) (execute F a) (applyAction_represents M F h a)

theorem runActions_toFrame (M : Memory n) (L : AccountingLog) (actions : List (Action n)) :
    (runActions M actions).toFrame (TraceAccounting.run (M.toFrame L) actions).log =
      TraceAccounting.run (M.toFrame L) actions := by
  obtain ⟨ht, hp, hh⟩ := runActions_represents M (M.toFrame L) (M.represents_toFrame L) actions
  unfold Memory.toFrame
  rw [ht, hp, hh]
  rfl

@[simp] theorem runActions_append (M : Memory n) (as bs : List (Action n)) :
    runActions M (as ++ bs) = runActions (runActions M as) bs := List.foldl_append

/-- The selection loop records every recursive refinement and no answer
mutation; its returned memory is precisely the execution of that list. -/
theorem selectLoop_memory (k : ℕ) (q : Query n) (fuel : ℕ) (M : Memory n)
    (r : Result n) (h : selectLoop k q fuel M = some r) :
    r.memory = runActions M r.actions := by
  induction fuel generalizing M r with
  | zero => simp [selectLoop] at h
  | succ fuel ih =>
    cases ha : attempt M k q with
    | answer a =>
      simp only [selectLoop, ha, Option.some.injEq] at h
      cases h
      rfl
    | refine x c =>
      cases hs : selectLoop k q fuel (applyMove M (makeMove M x c)) with
      | none => simp [selectLoop, ha, hs] at h
      | some s =>
        simp only [selectLoop, ha, hs, Option.map_some, Option.some.injEq] at h
        cases h
        exact ih (applyMove M (makeMove M x c)) s hs

theorem selectLoop_history (k : ℕ) (q : Query n) (fuel : ℕ) (M : Memory n)
    (r : Result n) (h : selectLoop k q fuel M = some r) : r.memory.history = M.history := by
  induction fuel generalizing M r with
  | zero => simp [selectLoop] at h
  | succ fuel ih =>
    cases ha : attempt M k q with
    | answer a =>
      simp only [selectLoop, ha, Option.some.injEq] at h
      cases h
      rfl
    | refine x c =>
      cases hs : selectLoop k q fuel (applyMove M (makeMove M x c)) with
      | none => simp [selectLoop, ha, hs] at h
      | some s =>
        simp only [selectLoop, ha, hs, Option.map_some, Option.some.injEq] at h
        cases h
        exact ih (applyMove M (makeMove M x c)) s hs

theorem repair_memory (k : ℕ) (M : Memory n) :
    (repair k M).1 = runActions M (repair k M).2 := by
  unfold repair
  split
  · simp only [runActions, List.foldl_cons, List.foldl_nil, applyAction, pathBatch_apply]
  · split
    · rfl
    · rfl

@[simp] theorem repair_history (k : ℕ) (M : Memory n) : (repair k M).1.history = M.history := by
  unfold repair
  split
  · rw [pathBatch_apply, applyMoves_history]
  · split <;> rfl

theorem compare_memory (k : ℕ) (M : Memory n) (q : Query n) (r : Result n)
    (h : compare k M q = some r) : r.memory = runActions M r.actions := by
  cases hs : selectLoop k q 3 M with
  | none => simp [compare, hs] at h
  | some s =>
    simp only [compare, hs, Option.map_some, Option.some.injEq] at h
    cases h
    rw [runActions_append, runActions_append, ← selectLoop_memory k q 3 M s hs]
    exact repair_memory k _

theorem compare_history (k : ℕ) (M : Memory n) (q : Query n) (r : Result n)
    (h : compare k M q = some r) : r.memory.history = ⟨q, r.answer⟩ :: M.history := by
  cases hs : selectLoop k q 3 M with
  | none => simp [compare, hs] at h
  | some s =>
    simp only [compare, hs, Option.map_some, Option.some.injEq] at h
    cases h
    rw [repair_history]
    simp only [applyAction]
    rw [selectLoop_history k q 3 M s hs]

theorem compare_represents (k : ℕ) (M : Memory n) (F : Frame n)
    (hF : M.Represents F) (q : Query n) (r : Result n) (h : compare k M q = some r) :
    r.memory.Represents (TraceAccounting.run F r.actions) := by
  rw [compare_memory k M q r h]
  exact runActions_represents M F hF r.actions

theorem runActions_paths_match (M : Memory n) (L : AccountingLog)
    (hp : TraceAccounting.PathsMatch (M.toFrame L)) (actions : List (Action n)) :
    ∀ x, ((runActions M actions).paths x).map (fun c => (c.coordinate : ℝ)) =
      (runActions M actions).tree.toReal.location x := by
  have hm := TraceAccounting.run_paths_match (M.toFrame L) actions hp
  obtain ⟨ht, hpaths, hh⟩ := runActions_represents M (M.toFrame L) (M.represents_toFrame L) actions
  rw [ht, hpaths]
  exact hm

noncomputable def frozenRanking (h : History n) : Ranking n :=
  SortingAdversary.Optimal.PublicOrder.rankingExtension
    (SortingAdversary.Optimal.PublicLegality.publicRows h)

@[simp] theorem frozenRanking_apply (h : History n) (x : Fin n) :
    frozenRanking h x = freeze h x := (freeze_apply h x).symm

theorem freeze_compatible (h : History n) (hne : ∃ π : Ranking n, Compatible π h) :
    Compatible (frozenRanking h) h := by
  apply (SortingAdversary.Optimal.PublicLegality.respects_public_iff h _).mp
  exact SortingAdversary.Optimal.PublicOrder.rankingExtension_respects
    (SortingAdversary.Optimal.PublicLegality.publicRows_order hne)

theorem rankAnswer_holds (π : Ranking n) (q : Query n) :
    (Observation.mk q (rankAnswer π q)).Holds π := outcome_holds π q

theorem freeze_answer_compatible (h : History n) (hne : ∃ π : Ranking n, Compatible π h)
    (q : Query n) : Compatible (frozenRanking h) (⟨q, rankAnswer (freeze h) q⟩ :: h) := by
  rw [compatible_cons]
  have ha : rankAnswer (freeze h) q = rankAnswer (frozenRanking h) q := by
    simp only [rankAnswer, frozenRanking_apply]
  rw [ha]
  exact ⟨rankAnswer_holds (frozenRanking h) q, freeze_compatible h hne⟩

end SortingAdversary.Continuous.Controller
