import SortingAdversary.Optimal.UniformAdversary
import SortingAdversary.Optimal.TreeTerminal

/-!
# Actual finite runs, cutoff accounting, and terminal totality

The direct machine execution supplies a chronological sequence of concrete
responses. If the execution remains active, that sequence is an `ActiveRun`;
otherwise its physical clock has already exceeded the chosen cutoff. Correct
sorting forces the actual terminal public order to be total.
-/

namespace SortingAdversary.Optimal.OnlineMachine.Machine

variable {n : ℕ}

theorem execute_preserves (m : OnlineMachine.Machine n) (P : m.State → Prop)
    (hstep : ∀ s q, P s → P (m.step s q).2) (t : DecisionTree n) (s : m.State) (hs : P s) :
    P (m.execute t s).2 := by
  induction t generalizing s with
  | leaf => exact hs
  | compare q left right ihL ihR =>
    cases ha : (m.step s q).1 with
    | less => simpa only [execute, ha] using ihL _ (hstep s q hs)
    | greater => simpa only [execute, ha] using ihR _ (hstep s q hs)

theorem execute_clock (m : OnlineMachine.Machine n) (clock : m.State → ℕ)
    (hstep : ∀ s q, clock (m.step s q).2 = clock s + 1) (t : DecisionTree n) (s : m.State) :
    clock (m.execute t s).2 = clock s + (m.execute t s).1.comparisons := by
  induction t generalizing s with
  | leaf => simp [execute]
  | compare q left right ihL ihR =>
    cases ha : (m.step s q).1 with
    | less =>
      simpa only [execute, ha, hstep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ihL (m.step s q).2
    | greater =>
      simpa only [execute, ha, hstep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ihR (m.step s q).2

end SortingAdversary.Optimal.OnlineMachine.Machine

namespace SortingAdversary.Optimal.ControllerRun

open ControllerMachine RecursiveController PublicOrder SparseClosure PublicLegality

variable {n : ℕ}

theorem extend_rows (R : Rows (Fin n)) (hR : IsOrder R) (a b : Fin n)
    (hba : R b a ≠ true) (hne : a ≠ b) :
    ∃ π : Ranking n, Respects R π ∧ π a < π b := by
  let R' : Rows (Fin n) := fun x y => R x y || (R x a && R b y)
  have hR' : IsOrder R' := adjoin_order hR a b hba
  let π := rankingExtension R'
  have hπ : Respects R' π := rankingExtension_respects hR'
  refine ⟨π, ?_, ?_⟩
  · intro x y hxy
    exact hπ x y (by simp [R', hxy])
  · apply strict_of_row hπ _ hne
    simp [R', hR.refl a, hR.refl b]

theorem total_of_unique (R : Rows (Fin n)) (hR : IsOrder R)
    (hu : ∀ π ρ : Ranking n, Respects R π → Respects R ρ → π = ρ) :
    ∀ a b, R a b = true ∨ R b a = true := by
  intro a b
  by_cases hab : R a b = true
  · exact Or.inl hab
  · right
    by_contra hba
    have hne : a ≠ b := by rintro rfl; exact hab (hR.refl a)
    obtain ⟨π, hπ, hp⟩ := extend_rows R hR a b hba hne
    obtain ⟨ρ, hρ, hr⟩ := extend_rows R hR b a hab hne.symm
    rw [← hu π ρ hπ hρ] at hr
    exact lt_asymm hp hr

/-- Totality concerns the actual stored public relation. It follows because
every extension of that relation is compatible with the actual full run. -/
theorem execute_final_total (m : OnlineMachine.Machine n) (t : DecisionTree n) (ht : t.Correct) :
    ∀ a b, m.rows (m.execute t m.initial).2 a b = true ∨
      m.rows (m.execute t m.initial).2 b a = true := by
  apply total_of_unique _ (m.ordered _)
  intro π ρ hπ hρ
  have hp := (m.execute_respects t m.initial π hπ).2
  have hr := (m.execute_respects t m.initial ρ hρ).2
  have he := m.execute_eq_run t []
  rw [m.replay_nil] at he
  rw [he] at hp hr
  exact (CompletedOrder.compatible_eq_output t ht m.strategy [] π hp).trans
    (CompletedOrder.compatible_eq_output t ht m.strategy [] ρ hr).symm

inductive ActiveRun (p : Parameters) : Active p n → History n → Active p n → Prop
  | nil (s : Active p n) : ActiveRun p s [] s
  | cons (s : Active p n) (q : Query n) {observations : History n} {t : Active p n}
      (tail : ActiveRun p (respond s q).next observations t) :
      ActiveRun p s (⟨q, (respond s q).answer⟩ :: observations) t

def ClockBound {p : Parameters} (cutoff : ℕ) (s : State p n) : Prop :=
  match s.mode with | .inl _ => s.clock ≤ cutoff | .inr _ => cutoff < s.clock

theorem step_clockBound {p : Parameters} (cutoff : ℕ) (s : State p n) (q : Query n)
    (h : ClockBound cutoff s) : ClockBound cutoff (step cutoff s q).2 := by
  cases hm : s.mode with
  | inl a =>
    by_cases hc : s.clock < cutoff
    · simp only [step, hm, if_pos hc, ClockBound]
      omega
    · simp only [step, hm, if_neg hc, ClockBound]
      omega
  | inr f =>
    simp only [ClockBound, hm] at h
    simp only [step, hm, ClockBound]
    omega

theorem execute_clockBound (p : Parameters) (N cutoff : ℕ) (t : DecisionTree (N + 2)) :
    ClockBound cutoff ((machine p N cutoff).execute t (machine p N cutoff).initial).2 :=
  (machine p N cutoff).execute_preserves (ClockBound cutoff) (step_clockBound cutoff)
    t _ (Nat.zero_le _)

theorem execute_clock (p : Parameters) (N cutoff : ℕ) (t : DecisionTree (N + 2)) :
    ((machine p N cutoff).execute t (machine p N cutoff).initial).2.clock =
      ((machine p N cutoff).execute t (machine p N cutoff).initial).1.comparisons := by
  simpa only [machine, Nat.zero_add] using
    (machine p N cutoff).execute_clock State.clock (step_clock cutoff) t (machine p N cutoff).initial

theorem execute_frozen (p : Parameters) (N cutoff : ℕ) (t : DecisionTree (N + 2))
    (clock : ℕ) (f : Frozen (N + 2)) :
    ((machine p N cutoff).execute t ⟨clock, .inr f⟩).2.mode = .inr f := by
  induction t generalizing clock with
  | leaf => rfl
  | compare q left right ihL ihR =>
    cases ha : f.answer q with
    | less => simpa only [OnlineMachine.Machine.execute, machine, step, ha] using ihL (clock + 1)
    | greater => simpa only [OnlineMachine.Machine.execute, machine, step, ha] using ihR (clock + 1)

/-- An actual active ending yields the full chronological sequence of actual
responses, rather than a supplied execution certificate. -/
theorem execute_activeRun (p : Parameters) (N cutoff : ℕ) (t : DecisionTree (N + 2))
    (clock : ℕ) (s final : Active p (N + 2))
    (hfinal : ((machine p N cutoff).execute t ⟨clock, .inl s⟩).2.mode = .inl final) :
    ActiveRun p s ((machine p N cutoff).execute t ⟨clock, .inl s⟩).1.observations final := by
  induction t generalizing clock s final with
  | leaf output =>
    have he : s = final := Sum.inl.inj hfinal
    subst final
    exact .nil s
  | compare q left right ihL ihR =>
    by_cases hc : clock < cutoff
    · cases ha : (respond s q).answer with
      | less =>
        have ht : ((machine p N cutoff).execute left
            ⟨clock + 1, .inl (respond s q).next⟩).2.mode = .inl final := by
          simpa only [OnlineMachine.Machine.execute, machine, step, if_pos hc, ha] using hfinal
        have tail := ihL (clock + 1) (respond s q).next final ht
        simpa only [OnlineMachine.Machine.execute, machine, step, if_pos hc, ha] using ActiveRun.cons s q tail
      | greater =>
        have ht : ((machine p N cutoff).execute right
            ⟨clock + 1, .inl (respond s q).next⟩).2.mode = .inl final := by
          simpa only [OnlineMachine.Machine.execute, machine, step, if_pos hc, ha] using hfinal
        have tail := ihR (clock + 1) (respond s q).next final ht
        simpa only [OnlineMachine.Machine.execute, machine, step, if_pos hc, ha] using ActiveRun.cons s q tail
    · cases ha : (freeze s).answer q with
      | less =>
        have ht : ((machine p N cutoff).execute left
            ⟨clock + 1, .inr (freeze s)⟩).2.mode = .inl final := by
          simpa only [OnlineMachine.Machine.execute, machine, step, if_neg hc, ha] using hfinal
        rw [execute_frozen] at ht
        contradiction
      | greater =>
        have ht : ((machine p N cutoff).execute right
            ⟨clock + 1, .inr (freeze s)⟩).2.mode = .inl final := by
          simpa only [OnlineMachine.Machine.execute, machine, step, if_neg hc, ha] using hfinal
        rw [execute_frozen] at ht
        contradiction

theorem active_or_cutoff (p : Parameters) (N cutoff : ℕ) (t : DecisionTree (N + 2)) :
    cutoff < (t.run (machine p N cutoff).strategy []).comparisons ∨
      ∃ final : Active p (N + 2),
        ActiveRun p (initialActive p N) (t.run (machine p N cutoff).strategy []).observations final ∧
        (t.run (machine p N cutoff).strategy []).comparisons ≤ cutoff ∧
        ((machine p N cutoff).execute t (machine p N cutoff).initial).2.mode = .inl final := by
  let m := machine p N cutoff
  have he : (m.execute t m.initial).1 = t.run m.strategy [] := by
    simpa only [OnlineMachine.Machine.replay_nil] using m.execute_eq_run t []
  have hb := execute_clockBound p N cutoff t
  have hclock := execute_clock p N cutoff t
  cases hm : (m.execute t m.initial).2.mode with
  | inl final =>
    right
    refine ⟨final, ?_, ?_, rfl⟩
    · rw [← he]
      exact execute_activeRun p N cutoff t 0 (initialActive p N) final hm
    · change ClockBound cutoff (m.execute t m.initial).2 at hb
      simp only [ClockBound, hm] at hb
      rw [hclock, he] at hb
      exact hb
  | inr f =>
    left
    change ClockBound cutoff (m.execute t m.initial).2 at hb
    simp only [ClockBound, hm] at hb
    rw [hclock, he] at hb
    exact hb

theorem active_terminal_total (p : Parameters) (N cutoff : ℕ)
    (t : DecisionTree (N + 2)) (ht : t.Correct) (final : Active p (N + 2))
    (hfinal : ((machine p N cutoff).execute t (machine p N cutoff).initial).2.mode = .inl final) :
    PoolTree.Tree.TotalOnMembers final.tree.pool := by
  intro a _ b _
  have h := execute_final_total (machine p N cutoff) t ht a b
  change State.rows ((machine p N cutoff).execute t (machine p N cutoff).initial).2 a b = true ∨
    State.rows ((machine p N cutoff).execute t (machine p N cutoff).initial).2 b a = true at h
  simpa only [State.rows, hfinal] using h

end SortingAdversary.Optimal.ControllerRun
