import SortingAdversary.Continuous.ControllerWork
import SortingAdversary.Continuous.ControllerResources

/-!
# Reachable component budgets for a measured comparison

The caps below bound the actual stored depths, transcript, and dyadic grid.
Geometric preservation and the precision theorems propagate these bounds
through every call in selection and repair. Component work bounds can thus
be instantiated on stored-data routines without assuming a bound for the
whole comparison, or for arbitrary unbounded memories.
-/

namespace SortingAdversary.Continuous.ControllerWork

open Controller Precision UniformStages Certificates FiniteAveraging

variable {n k p f qmax b : ℕ}

structure Sized (M : Controller.Memory n) (p f qmax : ℕ) : Prop where
  grid : M.OnGrid f
  depth : totalDepth M ≤ p
  history : M.history.length ≤ qmax

structure CallBounds (R : Routines n k) (p f qmax b : ℕ) : Prop where
  attempt : ∀ s, Admissible k (R.memory s) → Sized (R.memory s) p f qmax →
    ∀ q, (R.attempt s q).work ≤ b
  anchor : ∀ s, Admissible k (R.memory s) → Sized (R.memory s) p f qmax →
    ∀ x, (R.anchor s x).work ≤ b
  refine : ∀ s, Admissible k (R.memory s) → Sized (R.memory s) p f qmax →
    ∀ x c, OnDyadicGrid f c → 0 < c → c < 1 →
      (R.refine s x c).work ≤ b
  record : ∀ s, Admissible k (R.memory s) → Sized (R.memory s) p f qmax →
    ∀ q a, (R.record s q a).work ≤ b
  firstPath : ∀ s, Admissible k (R.memory s) → Sized (R.memory s) p f qmax →
    (R.firstPath s).work ≤ b
  degreeChoice : ∀ s, Admissible k (R.memory s) → Sized (R.memory s) p f qmax →
    (R.degreeChoice s).work ≤ b

variable (R : Routines n k) (hk : 64 ≤ k)

abbrev stepDigits (k : ℕ) (hk : 0 < k) : ℕ := Nat.log 2 (enumerationBudget k hk)

include hk

theorem selection_budget (hC : CallBounds R p f qmax b) (q : Query n)
    (fuel F : ℕ) (s : R.State) (hM : Ready k (R.memory s))
    (hg : (R.memory s).OnGrid F)
    (hp : totalDepth (R.memory s) + fuel ≤ p)
    (hF : F + fuel * stepDigits k (by omega) ≤ f)
    (hh : (R.memory s).history.length ≤ qmax) : SelectionBudget R q b fuel s := by
  induction fuel generalizing F s with
  | zero => trivial
  | succ fuel ih =>
    have hs : Sized (R.memory s) p f qmax :=
      ⟨hg.mono (by omega), by omega, hh⟩
    refine ⟨hC.attempt s hM.admissible hs q, ?_⟩
    rw [R.attempt_value]
    cases ha : Controller.attempt (R.memory s) k q with
    | answer a => trivial
    | refine x c =>
      obtain ⟨_, _, hl, hu, _, _⟩ := attempt_refine_spec (R.memory s) k hk hM.admissible q x c ha
      have hunit := hM.toGeometric.rationalBounds x
      have hcg := attempt_refine_onGrid (R.memory s) F k (by omega) hM.toGeometric hg q x c ha
      have hcg' : OnDyadicGrid f c := grid_mono hcg (by
        dsimp only [stepDigits] at hF ⊢
        rw [Nat.succ_mul] at hF
        omega)
      refine ⟨hC.refine s hM.admissible hs x c hcg' (hunit.1.trans_lt hl) (hu.trans_le hunit.2), ?_⟩
      have hn : Ready k (R.memory (R.refine s x c).value) := by
        rw [R.refine_value]
        exact attempt_refine_ready (R.memory s) k hk hM q x c ha
      have hgn : (R.memory (R.refine s x c).value).OnGrid (F + stepDigits k (by omega)) := by
        rw [R.refine_value]
        exact attempt_move_onGrid (R.memory s) F k hk hM.admissible hg q x c ha
      apply ih _ _ hn hgn
      · rw [R.refine_value, totalDepth_applyMove]
        omega
      · rw [Nat.succ_mul] at hF
        omega
      · simpa only [R.refine_value, applyMove_history] using hh

theorem anchor_grid (s : R.State) (F : ℕ) (hM : Admissible k (R.memory s))
    (hg : (R.memory s).OnGrid F) (x : Fin n) :
    OnDyadicGrid (F + stepDigits k (by omega)) (R.anchor s x).value := by
  rw [R.anchor_value]
  have hw := ArbitraryLabels.weak_endpoints (R.memory s).tree.system hM.normalized hM.toGeometric.widths
  exact RuntimePrecision.chooseAnchor_onGrid (R.memory s).tree.system F k (by omega) x hg.1
    hM.degree hw.1 hw.2 hM.toGeometric.widths
    (hM.toGeometric.rationalBounds x).1 (hM.toGeometric.rationalBounds x).2

theorem path_budget (hC : CallBounds R p f qmax b) (xs : List (Fin n))
    (F : ℕ) (s : R.State) (hM : Admissible k (R.memory s))
    (hg : (R.memory s).OnGrid F)
    (hp : totalDepth (R.memory s) + xs.length ≤ p)
    (hF : F + xs.length * stepDigits k (by omega) ≤ f)
    (hh : (R.memory s).history.length ≤ qmax) : PathBudget R b s xs := by
  induction xs generalizing F s with
  | nil => trivial
  | cons x xs ih =>
    have hs : Sized (R.memory s) p f qmax :=
      ⟨hg.mono (by omega), by omega, hh⟩
    have ha := anchor_move_spec (R.memory s) k hk hM x
    have hunit := hM.toGeometric.rationalBounds x
    have hcg := anchor_grid R hk s F hM hg x
    have hcg' : OnDyadicGrid f (R.anchor s x).value := grid_mono hcg (by
      simp only [List.length_cons, Nat.succ_mul] at hF
      omega)
    have hl : 0 < (R.anchor s x).value := by
      rw [R.anchor_value]
      exact hunit.1.trans_lt ha.2.1
    have hu : (R.anchor s x).value < 1 := by
      rw [R.anchor_value]
      exact ha.2.2.1.trans_le hunit.2
    refine ⟨hC.anchor s hM hs x, hC.refine s hM hs x _ hcg' hl hu, ?_⟩
    have hn : Admissible k (R.memory (R.refine s x (R.anchor s x).value).value) := by
      rw [R.refine_value, R.anchor_value]
      exact ha.2.2.2.1
    have hgn : (R.memory (R.refine s x (R.anchor s x).value).value).OnGrid
        (F + stepDigits k (by omega)) := by
      rw [R.refine_value, R.anchor_value]
      exact anchor_move_onGrid (R.memory s) F k hk hM hg x
    apply ih _ _ hn hgn
    · rw [R.refine_value, totalDepth_applyMove]
      simp only [List.length_cons] at hp
      omega
    · simp only [List.length_cons, Nat.succ_mul] at hF
      omega
    · simpa only [R.refine_value, applyMove_history] using hh

theorem repair_budget (hC : CallBounds R p f qmax b) (F : ℕ) (s : R.State)
    (hM : Admissible k (R.memory s)) (hg : (R.memory s).OnGrid F)
    (hp : totalDepth (R.memory s) + n ≤ p)
    (hF : F + n * stepDigits k (by omega) ≤ f)
    (hh : (R.memory s).history.length ≤ qmax) : RepairBudget R b s := by
  have hs : Sized (R.memory s) p f qmax := ⟨hg.mono (by omega), by omega, hh⟩
  refine ⟨hC.firstPath s hM hs, ?_⟩
  rw [R.firstPath_value]
  cases hpick : GraphPaths.firstPath (R.memory s).tree.system.edge (2 ^ k) with
  | some xs =>
    obtain ⟨_, hchain, _⟩ := GraphPaths.firstPath_some _ _ _ hpick
    obtain ⟨rank, hrank, _⟩ := hM.rank
    have hn := GraphPaths.path_nodup (R.memory s).tree.system.edge rank hrank hchain
    have hlen : xs.length ≤ n := by
      have hc := Finset.card_le_univ xs.toFinset
      simpa only [List.toFinset_card_of_nodup hn, Fintype.card_fin] using hc
    refine ⟨hlen, path_budget R hk hC xs F s hM hg (by omega) ?_ hh⟩
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ hlen) F).trans hF
  | none =>
    refine ⟨hC.degreeChoice s hM hs, ?_⟩
    rw [R.degreeChoice_value]
    cases hd : Controller.degreeChoice (R.memory s) k with
    | none => trivial
    | some x =>
      have hn : 1 ≤ n := Nat.zero_lt_of_lt x.isLt
      have hpath : PathBudget R b s [x] := path_budget R hk hC [x] F s hM hg
        (by simp only [List.length_singleton]; omega)
        (by simpa only [List.length_singleton, one_mul] using
          (Nat.add_le_add_left (Nat.mul_le_mul_right (stepDigits k (by omega)) hn) F).trans hF) hh
      exact ⟨hpath.1, hpath.2.1⟩

omit hk in
theorem selection_refinements_lt (q : Query n) (fuel : ℕ) (M : Controller.Memory n)
    (r : Controller.Result n) (h : Controller.selectLoop k q fuel M = some r) :
    refinementCount r.actions < fuel := by
  induction fuel generalizing M r with
  | zero => simp [Controller.selectLoop] at h
  | succ fuel ih =>
    cases ha : Controller.attempt M k q with
    | answer a =>
      simp only [Controller.selectLoop, ha, Option.some.injEq] at h
      cases h
      exact Nat.zero_lt_succ fuel
    | refine x c =>
      cases ht : Controller.selectLoop k q fuel (Controller.applyMove M (makeMove M x c)) with
      | none => simp [Controller.selectLoop, ha, ht] at h
      | some t =>
        simp only [Controller.selectLoop, ha, ht, Option.map_some, Option.some.injEq] at h
        cases h
        have hb := ih _ t ht
        simp only [refinementCount_cons, actionRefinements]
        omega

theorem compare_budget (hC : CallBounds R p f qmax b) (q : Query n)
    (F : ℕ) (s : R.State) (hM : Ready k (R.memory s)) (hg : (R.memory s).OnGrid F)
    (hp : totalDepth (R.memory s) + n + 3 ≤ p)
    (hF : F + (n + 3) * stepDigits k (by omega) ≤ f)
    (hh : (R.memory s).history.length + 1 ≤ qmax) : CompareBudget R b s q := by
  have hFsel : F + 3 * stepDigits k (by omega) ≤ f := by
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : 3 ≤ n + 3)) F).trans hF
  refine ⟨selection_budget R hk hC q 3 F s hM hg (by omega) hFsel (by omega), ?_⟩
  have hv := selectLoop_value R q 3 s
  cases hs : (selectLoop R q 3 s).value with
  | none => trivial
  | some z =>
    obtain ⟨t, a⟩ := z
    cases ht : Controller.selectLoop k q 3 (R.memory s) with
    | none => simp [hs, ht] at hv
    | some r =>
      have he : R.memory t = r.memory ∧ a = r.answer := by
        simpa only [hs, ht, Option.map_some, Option.some.injEq,
          storedView, resultView, Prod.mk.injEq] using hv
      have hready := (Controller.selectLoop_spec k hk q 3 (R.memory s) hM r ht).1
      have hans := (Controller.selectLoop_spec k hk q 3 (R.memory s) hM r ht).2.1
      have hcount := selection_refinements_lt q 3 (R.memory s) r ht
      have hgsel := (selectLoop_onGrid k hk q 3 (R.memory s) F hM.admissible hg ht).2
      have hgrid : r.memory.OnGrid (F + 3 * stepDigits k (by omega)) := by
        apply hgsel.mono
        exact Nat.add_le_add_left (by
          simpa only [stepDigits, Nat.mul_comm] using
            Nat.mul_le_mul_right (stepDigits k (by omega)) hcount.le) F
      have hdepth : totalDepth r.memory = totalDepth (R.memory s) + refinementCount r.actions := by
        rw [Controller.selectLoop_memory k q 3 (R.memory s) r ht]
        exact totalDepth_runActions _ _
      have hhistory := Controller.selectLoop_history k q 3 (R.memory s) r ht
      have hsize : Sized (R.memory t) p f qmax := by
        rw [he.1]
        refine ⟨hgrid.mono hFsel, by omega, ?_⟩
        rw [hhistory]
        omega
      refine ⟨hC.record t (he.1.symm ▸ hready.admissible) hsize q a, ?_⟩
      have hprob := attempt_answer_probability r.memory k (by omega) hready.toGeometric q r.answer hans
      have hrecord := hready.toGeometric.recorded hk q r.answer hprob.1 hprob.2
      have hn : Admissible k (R.memory (R.record t q a).value) := by
        rw [R.record_value, he.1, he.2]
        exact hready.recordedAdmissible q r.answer hrecord
      have hgn : (R.memory (R.record t q a).value).OnGrid (F + 3 * stepDigits k (by omega)) := by
        rw [R.record_value, he.1, he.2]
        exact hgrid.record q r.answer _
      apply repair_budget R hk hC _ _ hn hgn
      · rw [R.record_value, he.1, he.2]
        change totalDepth r.memory + n ≤ p
        omega
      · nlinarith
      · rw [R.record_value, recorded_history, List.length_cons, he.1, hhistory]
        exact hh

def depthCap (n : ℕ) : ℕ := (n + 3) ^ 2
def gridCap (n : ℕ) : ℕ := 4 * (n + 3) ^ 3
def historyCap (n : ℕ) : ℕ := n ^ 2 + 1

/-- The caps include every intermediate state of a query from an actual
reachable active memory at an admitted parameter. -/
theorem reachable_compare_budget
    (hC : CallBounds R (depthCap n) (gridCap n) (historyCap n) b)
    (past : History n) (s : R.State)
    (hr : Controller.replay k past = .active (R.memory s))
    (hE : enumerationBudget k (by omega) ≤ n) (q : Query n) : CompareBudget R b s q := by
  have hrun := replay_runtimeInvariant k (by omega) past
  rw [hr] at hrun
  have hd := active_depth_bound k (by omega) past (R.memory s) hr
  have hg := active_grid_bound k (by omega) past (R.memory s) hr hE
  have hlog : stepDigits k (by omega) ≤ n := (Nat.log_le_self 2 _).trans hE
  apply compare_budget R hk hC q (n ^ 3) s hrun.2.1.1 hg
  · unfold depthCap
    nlinarith
  · unfold gridCap
    have hm := Nat.mul_le_mul_left (n + 3) hlog
    nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)]
  · have ht := hrun.2.2.2.trans (Controller.horizon_le_square n)
    unfold historyCap
    omega

end SortingAdversary.Continuous.ControllerWork
