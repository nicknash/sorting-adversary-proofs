import SortingAdversary.Continuous.ControllerSemantics

/-!
# Legality of the concrete machine from its maintained memory invariant

Positive geometric states have actual compatible rankings. The machine
proof handles its fixed-rank phase and its total fallback explicitly, then
reduces legality on all finite decision trees to preservation of the active
memory invariant by successful calls to the executable comparison routine.
-/

namespace SortingAdversary.Continuous

open FiniteAveraging OrderRegion TreeState MeasureTheory

variable {n : ℕ}

/-- Positive volume supplies an injective feasible assignment, so geometric
transcript consistency implies consistency with an actual strict ranking. -/
theorem TreeState.State.exists_compatible (s : State n ℝ) (h : History n)
    (hs : s.Consistent h) (hb : ∀ x, 0 ≤ s.system.lower x ∧ s.system.upper x ≤ 1)
    (hV : 0 < volume (region s.system)) : ∃ π : Ranking n, Compatible π h := by
  let μ := Measure.pi (fun _ : Fin n => TreeSampling.unitLaw)
  have hp : μ (region s.system) ≠ 0 := by
    simpa only [μ, TreeSampling.unitLaw_region s.system hb] using ne_of_gt hV
  obtain ⟨X, hX, hinj⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hp
    (ae_restrict_of_ae (atomless_iid_tie_free n TreeSampling.unitLaw))
  have hposition : Function.Injective (s.position X) := by
    intro x y hxy
    apply hinj
    exact (List.concat_inj.mp (by simpa only [State.position, List.concat_eq_append] using hxy)).2
  obtain ⟨π, hπ⟩ := exists_orderCell (s.position X) hposition
  refine ⟨π, List.forall_iff_forall_mem.mpr ?_⟩
  intro o ho
  have hh := hs X hX o ho
  cases ha : o.answer with
  | less =>
    simp only [Observation.Holds, ha]
    apply (hπ o.query.left o.query.right).mpr
    simpa only [State.Holds, ha] using hh
  | greater =>
    simp only [Observation.Holds, ha]
    apply (hπ o.query.right o.query.left).mpr
    simpa only [State.Holds, ha] using hh

namespace Controller

/-- The active case carries a local memory invariant and the exact observed
history. The frozen case carries the ranking whose answers are being used. -/
def Sound (P : Memory n → Prop) : MachineState n → History n → Prop
  | .active M, h => P M ∧ M.history = h ∧ ∃ π : Ranking n, Compatible π h
  | .frozen ranks, h => ∃ π : Ranking n, (π : Fin n → Fin n) = ranks ∧ Compatible π h

theorem Sound.compatible {P : Memory n → Prop} {s : MachineState n} {h : History n}
    (hs : Sound P s h) : ∃ π : Ranking n, Compatible π h := by
  cases s with
  | active M => exact hs.2.2
  | frozen ranks => obtain ⟨π, _, hπ⟩ := hs; exact ⟨π, hπ⟩

theorem initial_sound (P : Memory n → Prop) (k : ℕ) (hP : P (initial n)) :
    Sound P (start n k) [] := by
  unfold start
  split
  · exact ⟨hP, rfl, Equiv.refl _, compatible_nil _⟩
  · exact ⟨Equiv.refl _, rfl, compatible_nil _⟩

theorem step_sound (P : Memory n → Prop) (k : ℕ)
    (hnext : ∀ M, P M → ∀ q r, compare k M q = some r →
      P r.memory ∧ ∃ π : Ranking n, Compatible π r.memory.history)
    (s : MachineState n) (h : History n) (hs : Sound P s h) (q : Query n) :
    Sound P (step k s q).2 (⟨q, (step k s q).1⟩ :: h) := by
  cases s with
  | frozen ranks =>
    obtain ⟨π, hr, hπ⟩ := hs
    subst ranks
    exact ⟨π, rfl, (compatible_cons _ _ _).mpr ⟨rankAnswer_holds π q, hπ⟩⟩
  | active M =>
    obtain ⟨hM, rfl, hπ⟩ := hs
    by_cases htime : M.history.length < horizon n
    · cases hc : compare k M q with
      | none =>
        simp only [step, if_pos htime, hc]
        exact ⟨frozenRanking M.history, funext (frozenRanking_apply M.history),
          freeze_answer_compatible M.history hπ q⟩
      | some r =>
        simp only [step, if_pos htime, hc]
        obtain ⟨hR, hπ'⟩ := hnext M hM q r hc
        have hh := compare_history k M q r hc
        exact ⟨hR, hh, by simpa only [hh] using hπ'⟩
    · simp only [step, if_neg htime]
      exact ⟨frozenRanking M.history, funext (frozenRanking_apply M.history),
        freeze_answer_compatible M.history hπ q⟩

/-- Decision-tree legality for the exact replay-based strategy. The premise
concerns the local active-memory invariant, not a desired global bound. -/
theorem run_consistent_of_memory_invariant (P : Memory n → Prop) (k : ℕ)
    (hnext : ∀ M, P M → ∀ q r, compare k M q = some r →
      P r.memory ∧ ∃ π : Ranking n, Compatible π r.memory.history)
    (t : DecisionTree n) (past : History n) (hs : Sound P (replay k past) past) :
    ∃ π : Ranking n, Compatible π past ∧ Compatible π (t.run (strategy k) past).observations := by
  induction t generalizing past with
  | leaf output =>
    obtain ⟨π, hπ⟩ := hs.compatible
    exact ⟨π, hπ, compatible_nil _⟩
  | compare q onLess onGreater ihLess ihGreater =>
    have hstep := step_sound P k hnext (replay k past) past hs q
    have hsound : Sound P (replay k (⟨q, strategy k past q⟩ :: past))
        (⟨q, strategy k past q⟩ :: past) := by
      simpa only [replay_cons, strategy] using hstep
    cases ha : strategy k past q with
    | less =>
      rw [ha] at hsound
      obtain ⟨π, hp, hrun⟩ := ihLess (⟨q, .less⟩ :: past) hsound
      obtain ⟨ho, hpast⟩ := (compatible_cons _ _ _).mp hp
      refine ⟨π, hpast, ?_⟩
      simpa only [DecisionTree.run, ha] using (compatible_cons π ⟨q, .less⟩ _).mpr ⟨ho, hrun⟩
    | greater =>
      rw [ha] at hsound
      obtain ⟨π, hp, hrun⟩ := ihGreater (⟨q, .greater⟩ :: past) hsound
      obtain ⟨ho, hpast⟩ := (compatible_cons _ _ _).mp hp
      refine ⟨π, hpast, ?_⟩
      simpa only [DecisionTree.run, ha] using (compatible_cons π ⟨q, .greater⟩ _).mpr ⟨ho, hrun⟩

theorem strategy_consistent_of_memory_invariant (P : Memory n → Prop) (k : ℕ)
    (hinit : P (initial n))
    (hnext : ∀ M, P M → ∀ q r, compare k M q = some r →
      P r.memory ∧ ∃ π : Ranking n, Compatible π r.memory.history)
    (t : DecisionTree n) :
    ∃ π : Ranking n, Compatible π (t.run (strategy k) []).observations := by
  obtain ⟨π, _, hπ⟩ := run_consistent_of_memory_invariant P k hnext t [] (initial_sound P k hinit)
  exact ⟨π, hπ⟩

end Controller
end SortingAdversary.Continuous
