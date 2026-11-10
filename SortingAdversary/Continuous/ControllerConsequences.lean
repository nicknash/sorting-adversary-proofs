import SortingAdversary.Continuous.ControllerBounds

/-!
# Concrete refinement counts and target-independent production

Refinements are counted directly from the returned action list. The
production corollary uses the same initialized machine for every target
relation and the same explicitly nonnegative vanishing error sequence.
-/

namespace SortingAdversary.Continuous

open FiniteAveraging OrderRegion TreeState MeasureTheory Filter
open scoped Topology

variable {n : ℕ}

namespace TraceAccounting

def Action.refinements : Action n → ℕ
  | .selection _ | .degree _ => 1
  | .path ms => ms.length
  | .answer _ _ _ => 0

def actionRefinements (actions : List (Action n)) : ℕ := (actions.map Action.refinements).sum

theorem execute_refinements {k : ℕ} (F : Frame n) (a : Action n) (ha : a.Valid k F) :
    (execute F a).log.refinements = F.log.refinements + a.refinements := by
  cases a with
  | selection m =>
    simp [execute, Action.nextLog, AccountingLog.refinements, RefinementEvent.count,
      Action.refinements, Nat.add_comm]
  | degree m =>
    simp [execute, Action.nextLog, AccountingLog.refinements, RefinementEvent.count,
      Action.refinements, Nat.add_comm]
  | path ms =>
    simp only [execute, Action.nextLog, AccountingLog.refinements, List.map_cons,
      List.sum_cons, pathEvent, RefinementEvent.count, Action.refinements]
    rw [List.toFinset_card_of_nodup ha.1, List.length_map]
    exact Nat.add_comm _ _
  | answer q a order => simp [execute, Action.nextLog, Action.refinements, AccountingLog.refinements]

theorem run_refinements {k : ℕ} (F : Frame n) (actions : List (Action n))
    (hvalid : Valid k F actions) :
    (run F actions).log.refinements = F.log.refinements + actionRefinements actions := by
  induction actions generalizing F with
  | nil => simp [run, actionRefinements]
  | cons a actions ih =>
    change (run (execute F a) actions).log.refinements = _
    rw [ih _ hvalid.2, execute_refinements F a hvalid.1]
    simp only [actionRefinements, List.map_cons, List.sum_cons, Nat.add_assoc]

end TraceAccounting

namespace Controller

/-- The number of actual coordinate refinements in the concrete action
execution is at most `8q/k`. Positivity and the unit bounds come from the
actual final geometric state. -/
theorem refinements_le {k : ℕ} (hk : 64 ≤ k)
    (actions : List (TraceAccounting.Action n))
    (hvalid : TraceAccounting.Valid k (TraceAccounting.initialFrame n) actions)
    (hgeo : Geometric (runActions (initial n) actions)) :
    (TraceAccounting.actionRefinements actions : ℝ) ≤
      8 * (runActions (initial n) actions).history.length / k := by
  let F := TraceAccounting.run (TraceAccounting.initialFrame n) actions
  have hB := TraceAccounting.run_bookkept (TraceAccounting.initialFrame n) actions hvalid
    (TraceAccounting.initial_bookkept k n)
  obtain ⟨hv, hw, ha, he, hl, hn⟩ := hB
  obtain ⟨ht, hp, hh⟩ := runActions_represents (initial n) (TraceAccounting.initialFrame n)
    ⟨initial_toReal n, rfl, rfl⟩ actions
  have hvol : F.log.logVolume ≤ 0 := by
    rw [← hv, ← ht]
    exact log2_nonpos (nodeVolume_pos _ hgeo.positive)
      (nodeVolume_le_one _ (fun x => (hgeo.bounds x).1) (fun x => (hgeo.bounds x).2))
  have harcs : k * F.log.degreeRepairs ≤ F.log.comparisons := by
    dsimp [F]
    omega
  have hcount := AccountingLog.refinement_count hk F.log he hl hvol harcs
  have hr := TraceAccounting.run_refinements (TraceAccounting.initialFrame n) actions hvalid
  have hr' : F.log.refinements = TraceAccounting.actionRefinements actions := by
    simpa only [F, TraceAccounting.initialFrame, AccountingLog.refinements,
      List.map_nil, List.sum_nil, zero_add] using hr
  rw [hr'] at hcount
  dsimp only [F] at hcount
  rwa [hn, ← hh] at hcount

noncomputable def productionError (k : ℝ) : ℝ := prefixOverhead k / (1 + prefixOverhead k)

theorem productionError_bounds {k : ℝ} (hk : 64 ≤ k) :
    0 ≤ productionError k ∧ productionError k < 1 := by
  have hδ := prefixOverhead_nonneg hk
  have hp : 0 < 1 + prefixOverhead k := by linarith
  unfold productionError
  exact ⟨div_nonneg hδ hp.le, (div_lt_one hp).mpr (by linarith)⟩

theorem selected_productionError_tendsto (stage : ℕ → ℕ)
    (hstage : Tendsto stage atTop atTop) :
    Tendsto (fun n => productionError (stage n)) atTop (𝓝 0) :=
  selected_error_tendsto stage hstage

/-- The same initialized adversary works for every target relation. A
successful production transcript must leave at most `e(R)` rankings. -/
theorem production_of_compare_guarantee {k : ℕ} (hk : 64 ≤ k)
    (hcompare : CompareGuarantee n k) (h : History n) (hf : Follows (strategy k) h)
    (R : Item n → Item n → Prop) (assignment : Ranking n)
    (hcorrect : ∀ π, Compatible π h → Produces R assignment π) :
    (1 - productionError k) * (log2 (n.factorial : ℝ) - log2 (extensionCount R : ℝ)) ≤
      h.length := by
  have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
  have hδ := prefixOverhead_nonneg hkR
  have hlegal := (follows_prefixSound hk hcompare h hf).1.compatible
  have hb := production_bound_of_prefix h R assignment (prefixOverhead k) hδ hlegal hcorrect
    (prefix_of_compare_guarantee hk hcompare h hf)
  have heq : 1 - productionError k = 1 / (1 + prefixOverhead k) := by
    unfold productionError
    field_simp [ne_of_gt (show 0 < 1 + prefixOverhead (k : ℝ) by linarith)]
    ring
  rw [heq]
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hb

theorem sorting_of_compare_guarantee {k : ℕ} (hk : 64 ≤ k)
    (hcompare : CompareGuarantee n k) (t : DecisionTree n) (ht : t.Correct) :
    (1 - productionError k) * log2 (n.factorial : ℝ) ≤
      (t.run (strategy k) []).comparisons := by
  have hb := sorting_bound_of_prefix (strategy k) t ht (prefixOverhead k)
    (consistent_of_compare_guarantee hk hcompare t)
    (prefix_of_compare_guarantee hk hcompare)
  have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : 0 < 1 + prefixOverhead k := by linarith [prefixOverhead_nonneg hkR]
  have hdiv : log2 (n.factorial : ℝ) / (1 + prefixOverhead k) ≤
      (t.run (strategy k) []).comparisons :=
    (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hb)
  have heq : 1 - productionError k = 1 / (1 + prefixOverhead k) := by
    unfold productionError
    field_simp [ne_of_gt hp]
    ring
  rw [heq]
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hdiv

end Controller
end SortingAdversary.Continuous
