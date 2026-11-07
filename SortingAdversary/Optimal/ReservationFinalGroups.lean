import SortingAdversary.Optimal.ReservationRun
import SortingAdversary.Optimal.ReservationGroupFits
import SortingAdversary.Optimal.ControllerEvolution

/-!
# Every actual run's groups fit the final stored tree

The selected groups are extracted from actual responses, and their physical
pin destinations persist at the same immutable node through all later
responses. No completed-group or multiplicity certificate is assumed for
the final history: it is derived from the normalizer and controller.
-/

namespace SortingAdversary.Optimal.ReservationFinalGroups

open WidthRepair ReservationMachine ReservationController ReservationRun ReservationFits
open ReservationAnnotations ReservationStoredReplay LedgerTreeBridge StoredEvolution
open RecursiveController ControllerMachine ControllerRun

variable {n : ℕ}

theorem record_paths_fit {p : Parameters} (record : RepairRecord p n) (tree : StoredTree n)
    (occurs : NodeAt tree record.identity record.result.final) :
    ∀ group ∈ recordPaths record, Fits tree group 1 := by
  intro group hg
  obtain ⟨members, hm, rfl⟩ := List.mem_map.mp hg
  exact ⟨record.identity, record.result.final, members, occurs, rfl,
    structural_paths record.result.events members hm⟩

theorem record_scales_fit {p : Parameters} (record : RepairRecord p n) (tree : StoredTree n)
    (occurs : NodeAt tree record.identity record.result.final) :
    ∀ group ∈ recordScales record, Fits tree group 2 := by
  intro group hg
  obtain ⟨members, hm, rfl⟩ := List.mem_map.mp hg
  exact ⟨record.identity, record.result.final, members, occurs, rfl,
    structural_scales record.result.events members hm⟩

theorem response_paths_fit {p : Parameters} (s : Active p n) (q : Query n) :
    ∀ group ∈ responsePaths s q, Fits (respond s q).next.tree group 1 := by
  cases hr : (respond s q).record with
  | none => simp [responsePaths, hr]
  | some record =>
    simpa only [responsePaths, hr] using
      record_paths_fit record _ (ControllerEvolution.respond_site s q record hr).2

theorem response_scales_fit {p : Parameters} (s : Active p n) (q : Query n) :
    ∀ group ∈ responseScales s q, Fits (respond s q).next.tree group 2 := by
  cases hr : (respond s q).record with
  | none => simp [responseScales, hr]
  | some record =>
    simpa only [responseScales, hr] using
      record_scales_fit record _ (ControllerEvolution.respond_site s q record hr).2

def historyPaths {p : Parameters} (s : Active p n) : History n →
    List (Finset (IncidenceLedger.Location n))
  | [] => []
  | observed :: rest => responsePaths s observed.query ++ historyPaths (respond s observed.query).next rest

def historyScales {p : Parameters} (s : Active p n) : History n →
    List (Finset (IncidenceLedger.Location n))
  | [] => []
  | observed :: rest => responseScales s observed.query ++ historyScales (respond s observed.query).next rest

theorem replay_groups {p : Parameters} (s : Active p n) (observations : History n)
    (ledger : IncidenceLedger.State n) (books : Books n) (execution : Execution n)
    (hrun : ReservationRun.replay s observations ledger books = some execution) :
    execution.pathGroups = historyPaths s observations ∧
      execution.scaleGroups = historyScales s observations := by
  induction observations generalizing s ledger books execution with
  | nil =>
    cases hrun
    exact ⟨rfl, rfl⟩
  | cons observed rest ih =>
    dsimp only [ReservationRun.replay] at hrun
    cases hb : ReservationMachine.run books (responseStreams s observed.query) with
    | none => simp [hb] at hrun
    | some nextBooks =>
      rw [hb] at hrun
      dsimp only [Bind.bind, Option.bind] at hrun
      cases ht : ReservationRun.replay (respond s observed.query).next rest
          (LedgerController.responseLog s observed.query ledger).ledger nextBooks with
      | none => simp [ht] at hrun
      | some tail =>
        rw [ht] at hrun
        dsimp only [Bind.bind, Option.bind, Pure.pure] at hrun
        cases hrun
        obtain ⟨hp, hs⟩ := ih (respond s observed.query).next _ nextBooks tail ht
        exact ⟨congrArg (responsePaths s observed.query ++ ·) hp,
          congrArg (responseScales s observed.query ++ ·) hs⟩

theorem history_fits {p : Parameters} {s final : Active p n} {observations : History n}
    (history : ActiveRun p s observations final) :
    (∀ group ∈ historyPaths s observations, Fits final.tree group 1) ∧
      (∀ group ∈ historyScales s observations, Fits final.tree group 2) := by
  induction history with
  | nil => simp [historyPaths, historyScales]
  | cons s q tail ih =>
    have he := ControllerEvolution.activeRun_evolves tail
    constructor
    · intro group hg
      rcases List.mem_append.mp hg with hg | hg
      · exact (response_paths_fit s q group hg).evolution he
      · exact ih.1 group hg
    · intro group hg
      rcases List.mem_append.mp hg with hg | hg
      · exact (response_scales_fit s q group hg).evolution he
      · exact ih.2 group hg

theorem replay_fits {p : Parameters} {s final : Active p n} {observations : History n}
    (history : ActiveRun p s observations final)
    (ledger : IncidenceLedger.State n) (books : Books n) (execution : Execution n)
    (hrun : ReservationRun.replay s observations ledger books = some execution) :
    (∀ group ∈ execution.pathGroups, Fits final.tree group 1) ∧
      (∀ group ∈ execution.scaleGroups, Fits final.tree group 2) := by
  obtain ⟨hp, hs⟩ := replay_groups s observations ledger books execution hrun
  rw [hp, hs]
  exact history_fits history

/-- Every group in the final books comes from the actual run, has its exact
size, is disjoint from earlier groups of the same kind, and has actual final
destination multiplicity one (paths) or two (scales). -/
theorem initial_final_groups (p : Parameters) (N : ℕ) {observations : History (N + 2)}
    {final : Active p (N + 2)} (history : ActiveRun p (initialActive p N) observations final) :
    ∃ execution : Execution (N + 2),
      ReservationRun.replay (initialActive p N) observations (IncidenceLedger.initial (initialFree (N + 2)))
        (ReservationMachine.initial (initialFree (N + 2))) = some execution ∧
      Sound p.repair.D (IncidenceLedger.initial (initialFree (N + 2)))
        (ReservationMachine.initial (initialFree (N + 2))) observations final execution ∧
      (∀ group ∈ execution.books.path.groups, Fits final.tree group 1) ∧
      (∀ group ∈ execution.books.scale.groups, Fits final.tree group 2) := by
  obtain ⟨execution, hr, hs⟩ := initial_activeRun p N history
  have hf := replay_fits history _ _ execution hr
  refine ⟨execution, hr, hs, ?_, ?_⟩
  · intro group hg
    rw [hs.pathGroups] at hg
    simpa only [ReservationMachine.initial, GroupReservations.initial, List.append_nil,
      List.mem_reverse] using hf.1 group (by simpa only [ReservationMachine.initial,
        GroupReservations.initial, List.append_nil, List.mem_reverse] using hg)
  · intro group hg
    rw [hs.scaleGroups] at hg
    exact hf.2 group (by simpa only [ReservationMachine.initial, GroupReservations.initial,
      List.append_nil, List.mem_reverse] using hg)

end SortingAdversary.Optimal.ReservationFinalGroups
