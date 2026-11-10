import SortingAdversary.Continuous.ControllerLocal
import SortingAdversary.Continuous.SelectionTermination

/-!
# The actual selection loop terminates and has valid accounting

Three attempts suffice: each failed attempt refines one queried label with
positive density gain, and that label thereafter has unit marginal density.
The proof applies to the executable loop and its emitted action list.
-/

namespace SortingAdversary.Continuous.Controller

open FiniteAveraging OrderRegion TreeState TraceAccounting

variable {n : ℕ}

theorem selectLoop_none_trace (k : ℕ) (hk : 64 ≤ k) (q : Query n)
    (fuel : ℕ) (M : Memory n) (hM : Ready k M)
    (h : selectLoop k q fuel M = none) :
    ∃ (s' : State n ℝ) (moves : List (Fin n × ℝ)),
      ProfitableRefinements M.tree.toReal moves s' ∧ moves.length = fuel ∧
        ∀ m ∈ moves, m.1 = q.left ∨ m.1 = q.right := by
  induction fuel generalizing M with
  | zero => exact ⟨M.tree.toReal, [], .nil _, rfl, by simp⟩
  | succ fuel ih =>
    cases ha : attempt M k q with
    | answer a => simp [selectLoop, ha] at h
    | refine x c =>
      let m := makeMove M x c
      have hs : selectLoop k q fuel (Controller.applyMove M m) = none := by
        simpa only [selectLoop, ha, Option.map_eq_none_iff, m] using h
      have hnext := attempt_refine_ready M k hk hM q x c ha
      obtain ⟨s', moves, htrace, hlen, hquery⟩ := ih (Controller.applyMove M m) hnext hs
      obtain ⟨hx, hc, hl, hu, hg, _⟩ := attempt_refine_spec M k hk hM.admissible q x c ha
      have hstate : (Controller.applyMove M m).tree.toReal =
          TreeState.normalize (refineAt M.tree.toReal x (c : ℝ)) m.order := by
        rw [applyMove_tree]
        simp only [Move.apply, m, makeMove_item, hc]
      rw [hstate] at htrace
      have hinside : M.tree.toReal.system.lower x < (c : ℝ) ∧
          (c : ℝ) < M.tree.toReal.system.upper x :=
        ⟨(Rat.cast_lt (K := ℝ)).mpr hl, (Rat.cast_lt (K := ℝ)).mpr hu⟩
      have hpositive : (0 : ℝ) < log2 (density M.tree.toReal.system x (c : ℝ)) := by
        exact (Nat.cast_nonneg k).trans_lt hg
      refine ⟨s', (x, (c : ℝ)) :: moves,
        .cons _ x (c : ℝ) m.order moves s' (hM.noLoop x) hinside
          (nodeVolume_pos _ hM.positive) hpositive htrace, ?_, ?_⟩
      · simp only [List.length_cons, hlen]
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hx
        · exact hquery z hz

/-- Exhausting the three allowed attempts would refine three distinct
labels from a two-element query. Thus the executable option is always `some`. -/
theorem selectLoop_total (k : ℕ) (hk : 64 ≤ k) (q : Query n)
    (M : Memory n) (hM : Ready k M) :
    ∃ r : Result n, selectLoop k q 3 M = some r := by
  cases h : selectLoop k q 3 M with
  | some r => exact ⟨r, rfl⟩
  | none =>
    obtain ⟨s', moves, ht, hlen, hquery⟩ := selectLoop_none_trace k hk q 3 M hM h
    have hh := ht.length_le_two q hquery
    omega

/-- A returned selection result is ready for its actual final answer, and
every emitted selection action meets the accounting obligation. -/
theorem selectLoop_spec (k : ℕ) (hk : 64 ≤ k) (q : Query n)
    (fuel : ℕ) (M : Memory n) (hM : Ready k M) (r : Result n)
    (h : selectLoop k q fuel M = some r) :
    Ready k r.memory ∧ attempt r.memory k q = .answer r.answer ∧
      ∀ F : Frame n, M.Represents F → Valid k F r.actions := by
  induction fuel generalizing M r with
  | zero => simp [selectLoop] at h
  | succ fuel ih =>
    cases ha : attempt M k q with
    | answer a =>
      simp only [selectLoop, ha, Option.some.injEq] at h
      cases h
      exact ⟨hM, ha, fun _ _ => trivial⟩
    | refine x c =>
      cases hs : selectLoop k q fuel (Controller.applyMove M (makeMove M x c)) with
      | none => simp [selectLoop, ha, hs] at h
      | some s =>
        simp only [selectLoop, ha, hs, Option.map_some, Option.some.injEq] at h
        cases h
        obtain ⟨hready, hans, hvalid⟩ := ih _
          (attempt_refine_ready M k hk hM q x c ha) s hs
        refine ⟨hready, hans, ?_⟩
        intro F hF
        exact ⟨attempt_refine_valid M k hk hM.admissible q x c ha F hF,
          hvalid (execute F (.selection (makeMove M x c)))
            (applyAction_represents M F hF (.selection (makeMove M x c)))⟩

end SortingAdversary.Continuous.Controller
