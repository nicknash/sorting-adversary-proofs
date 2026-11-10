import SortingAdversary.Continuous.ControllerSelection
import SortingAdversary.Continuous.ControllerRepair
import SortingAdversary.Continuous.ControllerBounds

/-!
# End-to-end correctness of the continuous comparison controller

The local certificate, density, repair, and accounting theorems are all
instantiated at the exact states visited by `compare`. In particular, no
oracle-success, legality, accounting, or termination hypothesis remains in
the fixed-parameter prefix and sorting bounds.
-/

namespace SortingAdversary.Continuous.Controller

open FiniteAveraging OrderRegion TreeState TraceAccounting

variable {n : ℕ}

theorem compare_total_spec (k : ℕ) (hk : 64 ≤ k) (M : Memory n)
    (hM : Ready k M) (q : Query n) :
    ∃ r : Result n, compare k M q = some r ∧ Ready k r.memory ∧
      ∀ F, M.Represents F → Valid k F r.actions := by
  obtain ⟨s, hs⟩ := selectLoop_total k hk q M hM
  obtain ⟨hready, hans, hvalid⟩ := selectLoop_spec k hk q 3 M hM s hs
  have hprob := attempt_answer_probability s.memory k (by omega) hready.toGeometric q s.answer hans
  have hrecord : Geometric (recorded s.memory q s.answer) :=
    hready.toGeometric.recorded hk q s.answer hprob.1 hprob.2
  have hrepair := repair_recorded_ready k hk s.memory hready q s.answer hrecord
  let a : Action n := .answer q s.answer (answerOrder s.memory q s.answer)
  let N := recorded s.memory q s.answer
  let r : Result n := ⟨(repair k N).1, s.answer, s.actions ++ [a] ++ (repair k N).2⟩
  refine ⟨r, ?_, hrepair, ?_⟩
  · simp only [compare, hs, Option.map_some]
    rfl
  · intro F hF
    have hFs : s.memory.Represents (run F s.actions) := by
      rw [selectLoop_memory k q 3 M s hs]
      exact runActions_represents M F hF s.actions
    have hva : a.Valid k (run F s.actions) := by
      apply valid_answer_of_probability hk (run F s.actions) q s.answer _
      · rw [← hFs.1]
        exact hprob.1
      · rw [← hFs.1]
        exact nodeVolume_pos _ hready.positive
      · rw [← hFs.1]
        exact hprob.2
    have hFN : N.Represents (execute (run F s.actions) a) :=
      applyAction_represents s.memory _ hFs a
    have hvr := repair_valid k hk N (hready.recordedAdmissible q s.answer hrecord) _ hFN
    apply valid_append F (s.actions ++ [a]) (repair k N).2
    · exact valid_append F s.actions [a] (hvalid F hF) ⟨hva, trivial⟩
    · simpa only [TraceAccounting.run, List.foldl_append, List.foldl_cons, List.foldl_nil] using hvr

/-- The comparison guarantee is proved for the actual program, for every
input size and every parameter in the paper's range. -/
theorem compareGuarantee (n k : ℕ) (hk : 64 ≤ k) : CompareGuarantee n k :=
  fun M hM q => compare_total_spec k hk M hM q

theorem compare_ready (k : ℕ) (hk : 64 ≤ k) (M : Memory n) (hM : Ready k M)
    (q : Query n) (r : Result n) (h : compare k M q = some r) : Ready k r.memory := by
  obtain ⟨s, hs, hr, _⟩ := compare_total_spec k hk M hM q
  have he : s = r := Option.some.inj (hs.symm.trans h)
  simpa only [he] using hr

theorem consistent (k : ℕ) (hk : 64 ≤ k) (t : DecisionTree n) :
    ∃ π : Ranking n, Compatible π (t.run (strategy k) []).observations :=
  consistent_of_compare_guarantee hk (compareGuarantee n k hk) t

/-- The fixed-stage theorem applies to every completed prefix, including
prefixes after the controller has switched permanently to fixed ranks. -/
theorem prefix_count (k : ℕ) (hk : 64 ≤ k) (h : History n)
    (hf : Follows (strategy k) h) :
    log2 (n.factorial : ℝ) - (1 + prefixOverhead k) * h.length ≤
      log2 (transcriptCount h : ℝ) :=
  prefix_of_compare_guarantee hk (compareGuarantee n k hk) h hf

theorem sorting_bound (k : ℕ) (hk : 64 ≤ k) (t : DecisionTree n) (ht : t.Correct) :
    log2 (n.factorial : ℝ) ≤ (1 + prefixOverhead k) * (t.run (strategy k) []).comparisons :=
  sorting_bound_of_prefix (strategy k) t ht (prefixOverhead k)
    (consistent k hk t) (prefix_count k hk)

end SortingAdversary.Continuous.Controller
