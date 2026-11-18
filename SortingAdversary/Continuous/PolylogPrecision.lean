import SortingAdversary.Continuous.PolylogAdversary
import SortingAdversary.Continuous.ControllerPrecision
import SortingAdversary.Continuous.ControllerCorrect
import SortingAdversary.Continuous.PolylogLocalBudget

/-!
# Fractional precision along actual rounded comparisons

Selection may move two labels before recording its answer. Repair either
moves one label or the vertices of a path of the prescribed length. Each
prefix anchor adds at most two bits; the successful central anchors lie on
a stage-dependent grid independent of the current stored precision.
-/

namespace SortingAdversary.Continuous.PolylogPrecision

open Controller FiniteAveraging Certificates TraceAccounting
open PolylogOracle (prefixAnchor centralTest)
open SortingAdversary.Optimal

variable {n : ℕ}

attribute [local instance] PolylogOracle.choices PolylogOracle.choices_valid

theorem prefix_grid (M : Memory n) (hM : Geometric M) {F : ℕ} (hg : M.OnGrid F) (x : Fin n) :
    OnDyadicGrid (F + 2) (prefixAnchor M x) := by
  have hl := hg.1.1 x
  have hr := hg.1.2 x
  have hw := hM.widths x
  have hb := hM.rationalBounds x
  have hW : M.tree.system.upper x - M.tree.system.lower x ≤ 1 := by linarith
  unfold prefixAnchor
  rw [← PolylogAnchor.fallback_eq_reference (Precision.interval_width_ge hl hr hw) hw hW]
  exact PolylogAnchor.fallback_onGrid hl hr hw hW

/-- A stage bound for the successful central test. -/
def CentralGrid (n k A : ℕ) : Prop :=
  ∀ M : Memory n, Admissible k M → ∀ x J, centralTest M k x = some J →
    OnDyadicGrid A (roundUp J)

private theorem anchor_move (M : Memory n) (k A F : ℕ) (hA : CentralGrid n k A) (hAF : A ≤ F)
    (hk : 64 ≤ k) (hM : Admissible k M) (hg : M.OnGrid F) (x : Fin n) :
    (Controller.applyMove M (makeMove M x (PolylogOracle.anchor M k x))).OnGrid (F + 2) := by
  apply (hg.mono (show F ≤ F + 2 by omega)).applyMove
  rw [(PolylogOracle.anchor_move_spec M k hk hM x).1]
  cases ht : centralTest M k x with
  | none => exact (show PolylogOracle.anchor M k x = prefixAnchor M x by simp [PolylogOracle.anchor, ht]) ▸
      prefix_grid M hM.toGeometric hg x
  | some J =>
    rw [PolylogOracle.anchor, ht]
    exact Precision.grid_mono (hA M hM x J ht) (by omega)

private theorem selected_move (M : Memory n) (F k : ℕ) (hk : 64 ≤ k) (hM : Admissible k M)
    (hg : M.OnGrid F) (q : Query n) (x : Fin n) (v : ℚ)
    (h : PolylogOracle.attempt M k q = .refine x v) :
    (Controller.applyMove M (makeMove M x v)).OnGrid (F + 2) := by
  apply (hg.mono (show F ≤ F + 2 by omega)).applyMove
  rw [(PolylogOracle.attempt_refine_spec M k hk hM q x v h).2.1,
    (PolylogOracle.attempt_refine_output M k q x v h).2]
  exact prefix_grid M hM.toGeometric hg x

/-- A successful selection with `fuel` trials made at most `fuel-1` moves:
one trial produced its answer. -/
private theorem select_grid (k : ℕ) (hk : 64 ≤ k) (q : Query n) (fuel : ℕ)
    (M : Memory n) (F : ℕ) (hM : Ready k M) (hg : M.OnGrid F) {r : Result n}
    (h : selectLoop k q fuel M = some r) :
    0 < fuel ∧ r.memory.OnGrid (F + 2 * (fuel - 1)) := by
  induction fuel generalizing M F r with
  | zero => simp [selectLoop] at h
  | succ fuel ih =>
    cases ha : PolylogOracle.attempt M k q with
    | answer a =>
      change (match PolylogOracle.attempt M k q with
        | .answer a => some ⟨M, a, []⟩
        | .refine x c => _) = some r at h
      simp only [ha, Option.some.injEq] at h
      subst r
      exact ⟨by omega, hg.mono (by omega)⟩
    | refine x c =>
      change (match PolylogOracle.attempt M k q with
        | .answer a => some ⟨M, a, []⟩
        | .refine x c => (selectLoop k q fuel (Controller.applyMove M (makeMove M x c))).map
          fun r => ⟨r.memory, r.answer, .selection (makeMove M x c) :: r.actions⟩) = some r at h
      rw [ha] at h
      cases ht : selectLoop k q fuel (Controller.applyMove M (makeMove M x c)) with
      | none => simp [ht] at h
      | some s =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst r
        have hn := attempt_refine_ready M k hk hM q x c ha
        obtain ⟨hpos, hgrid⟩ := ih _ _ hn (selected_move M F k hk hM.admissible hg q x c ha) ht
        exact ⟨by omega, hgrid.mono (by omega)⟩

private theorem path_grid (k A : ℕ) (hA : CentralGrid n k A) (hk : 64 ≤ k)
    (xs : List (Fin n)) (M : Memory n) (F : ℕ) (hAF : A ≤ F) (hM : Admissible k M)
    (hg : M.OnGrid F) : (pathBatch k M xs).1.OnGrid (F + 2 * xs.length) := by
  induction xs generalizing M F with
  | nil => simpa only [pathBatch, List.length_nil, mul_zero, add_zero] using hg
  | cons x xs ih =>
    have hs := PolylogOracle.anchor_move_spec M k hk hM x
    have h := ih _ (F + 2) (by omega) hs.2.2.2.1 (anchor_move M k A F hA hAF hk hM hg x)
    have he : F + 2 * (x :: xs).length = F + 2 + 2 * xs.length := by simp; omega
    rw [he]
    exact h

private theorem repair_grid (M : Memory n) (k A F : ℕ) (hA : CentralGrid n k A)
    (hAF : A ≤ F) (hk : 64 ≤ k) (hM : Admissible k M) (hg : M.OnGrid F) :
    (repair k M).1.OnGrid (F + 2 * 2 ^ k) := by
  cases hp : GraphPaths.firstPath M.tree.system.edge (2 ^ k) with
  | some xs =>
    have hh := path_grid k A hA hk xs M F hAF hM hg
    rw [(GraphPaths.firstPath_some _ _ _ hp).1] at hh
    simpa only [repair, hp] using hh
  | none =>
    cases hd : degreeChoice M k with
    | none => simpa only [repair, hp, hd] using hg.mono (show F ≤ F + 2 * 2 ^ k by omega)
    | some x =>
      have hh := anchor_move M k A F hA hAF hk hM hg x
      have hp' : 0 < 2 ^ k := pow_pos (by decide) _
      simp only [repair, hp, hd]
      change (Controller.applyMove M (makeMove M x (PolylogOracle.anchor M k x))).OnGrid _
      exact hh.mono (by omega)

/-- One completed rounded comparison, including normalization and path repair. -/
theorem compare_grid (M : Memory n) (k A F : ℕ) (hA : CentralGrid n k A) (hAF : A ≤ F)
    (hk : 64 ≤ k) (hM : Ready k M) (hg : M.OnGrid F) (q : Query n) {r : Result n}
    (h : Controller.compare k M q = some r) : r.memory.OnGrid (F + 2 * (2 ^ k + 2)) := by
  cases hs : selectLoop k q 3 M with
  | none => simp only [Controller.compare, hs, Option.map_none] at h; contradiction
  | some s =>
    simp only [Controller.compare, hs, Option.map_some, Option.some.injEq] at h
    subst r
    have hsel := selectLoop_spec k hk q 3 M hM s hs
    have hgrid : s.memory.OnGrid (F + 4) := (select_grid k hk q 3 M F hM hg hs).2
    have hp := PolylogOracle.attempt_answer_probability s.memory k (by omega)
      hsel.1.toGeometric q s.answer hsel.2.1
    have hrgeom := hsel.1.toGeometric.recorded hk q s.answer hp.1 hp.2
    have hradm := hsel.1.recordedAdmissible q s.answer hrgeom
    have hrgrid := hgrid.record q s.answer (answerOrder s.memory q s.answer)
    have hrepair := repair_grid (recorded s.memory q s.answer) k A (F + 4) hA (by omega)
      hk hradm hrgrid
    exact hrepair.mono (by omega)

/-- Active runs of the actual rounded controller prior to freezing. -/
inductive ActiveRun (k : ℕ) : ℕ → Memory n → Prop where
  | start : ActiveRun k 0 (initial n)
  | next {t M} (prior : ActiveRun k t M) (q : Query n) {r : Result n}
      (step : Controller.compare k M q = some r) : ActiveRun k (t + 1) r.memory

theorem active_grid {k A t : ℕ} (hA : CentralGrid n k A) (hk : 64 ≤ k)
    {M : Memory n} (h : ActiveRun k t M) : Ready k M ∧ M.OnGrid (A + t * (2 * (2 ^ k + 2))) := by
  induction h with
  | start => exact ⟨initial_ready n k (by omega), (Controller.initial_onGrid n).mono (by omega)⟩
  | @next t M prior q r step ih =>
    have hh := compare_grid M k A _ hA (Nat.le_add_right _ _) hk ih.1 ih.2 q step
    rw [Nat.add_mul, one_mul, ← Nat.add_assoc]
    obtain ⟨s, hs, hready, _⟩ := Controller.compare_total_spec k hk M ih.1 q
    have he : s = r := Option.some.inj (hs.symm.trans step)
    exact ⟨he ▸ hready, hh⟩

/-- The actual scheduled central test writes at most one short word of
fractional bits before the controller performs its next refinement. -/
theorem scheduled_central (extra : CappedArithmetic.Expr)
    (hk : 64 ≤ PolylogSchedule.parameter extra n) :
    CentralGrid n (PolylogSchedule.parameter extra n) (Parameters.logCap n) := by
  intro M hM x J hJ
  have hk' : 0 < PolylogSchedule.parameter extra n := by omega
  simp only [centralTest, dif_pos hk'] at hJ
  have he := ArbitraryLabels.weak_endpoints M.tree.system hM.normalized hM.widths
  exact PolylogLocalBudget.central_anchor_precision extra M.tree.system hk {x} hM.degree x
    hM.widths he.1 he.2 (hM.rationalBounds x).1 (hM.rationalBounds x).2 hJ

/-- Every endpoint and anchor in an actual active state fits the shared
capacity from the note. Addresses into this many bits use logarithmic space. -/
theorem active_capacity (extra : CappedArithmetic.Expr) (hk : 64 ≤ PolylogSchedule.parameter extra n)
    {t : ℕ} (ht : t ≤ horizon n) {M : Memory n} (h : ActiveRun (PolylogSchedule.parameter extra n) t M) :
    let D := PolylogSchedule.capacity (Parameters.logCap n)
      (ArbitraryLabels.pathHeight (PolylogSchedule.parameter extra n)) n
    M.OnGrid D ∧ D.size ≤ 5 + (Parameters.logCap n + 1) * 3 := by
  have hg := (active_grid (scheduled_central extra hk) hk h).2
  refine ⟨hg.mono ?_, PolylogSchedule.capacity_bits hk le_rfl⟩
  let k := PolylogSchedule.parameter extra n
  have hH : 2 ^ k ≤ ArbitraryLabels.pathHeight k := by
    unfold ArbitraryLabels.pathHeight
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hprod := Nat.mul_le_mul (Nat.le_succ_of_le ht) (Nat.add_le_add_right hH 2)
  change Parameters.logCap n + t * (2 * (2 ^ k + 2)) ≤
    PolylogSchedule.capacity (Parameters.logCap n) (ArbitraryLabels.pathHeight k) n
  unfold PolylogSchedule.capacity
  nlinarith

/-- The active state reached by the public policy after replaying a list of
queries is exactly such a run. Recorded answers are irrelevant to replay. -/
theorem replay_active {k : ℕ} (hk : 64 ≤ k) (hist : History n) {fuel : ℕ} {M : Memory n}
    (h : (PolylogAdversary.policy n).replay k hist = .active fuel M) :
    ActiveRun k hist.length M ∧ Ready k M ∧ fuel + hist.length = horizon n := by
  induction hist generalizing fuel M with
  | nil =>
    simp only [PolylogMachine.Policy.replay, PolylogMachine.start, if_pos hk,
      PolylogMachine.State.active.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.start, initial_ready n k (by omega), rfl⟩
  | cons o hist ih =>
    cases hs : (PolylogAdversary.policy n).replay k hist with
    | fallback => simp [PolylogMachine.Policy.replay, hs, PolylogMachine.Policy.step] at h
    | frozen N => simp [PolylogMachine.Policy.replay, hs, PolylogMachine.Policy.step] at h
    | active t N =>
      obtain ⟨hrun, hready, hcount⟩ := ih hs
      cases t with
      | zero => simp [PolylogMachine.Policy.replay, hs, PolylogMachine.Policy.step] at h
      | succ t =>
        obtain ⟨r, hr, hn, _⟩ := Controller.compare_total_spec k hk N hready o.query
        have hpolicy : (PolylogAdversary.policy n).compare k N o.query = r := by
          change (@Controller.compare n (PolylogOracle.choices n) k N o.query).getD _ = r
          rw [hr]; rfl
        simp only [PolylogMachine.Policy.replay, hs, PolylogMachine.Policy.step, hpolicy,
          PolylogMachine.State.active.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨.next hrun o.query hr, hn, by simp; omega⟩

/-- The concrete policy used by the published comparison bound fits all of
its pre-freeze states into the indicated dyadic capacity. -/
theorem replay_capacity (hist : History n) {fuel : ℕ} {M : Memory n}
    (hk : 64 ≤ PolylogAdversary.parameter n)
    (h : (PolylogAdversary.policy n).replay (PolylogAdversary.parameter n) hist = .active fuel M) :
    let D := PolylogSchedule.capacity (Parameters.logCap n)
      (ArbitraryLabels.pathHeight (PolylogAdversary.parameter n)) n
    M.OnGrid D ∧ D.size ≤ 5 + (Parameters.logCap n + 1) * 3 := by
  obtain ⟨hr, _, hc⟩ := replay_active hk hist h
  exact active_capacity PolylogAdversary.extra hk (by omega) hr

/-- The shared block tree has room for the next comparison even just before
freezing. Its height is the number of bits in the capacity, so `D` is a
valid bit position and all moves in the call may use the same binary point. -/
theorem replay_workspace (hist : History n) {fuel : ℕ} {M : Memory n}
    (hk : 64 ≤ PolylogAdversary.parameter n)
    (h : (PolylogAdversary.policy n).replay (PolylogAdversary.parameter n) hist = .active fuel M) :
    let k := PolylogAdversary.parameter n
    let A := Parameters.logCap n
    let D := PolylogSchedule.capacity A (ArbitraryLabels.pathHeight k) n
    ∃ F, M.OnGrid F ∧ F + 2 * (2^k + 2) + 2 ≤ D ∧ A ≤ D ∧ D < 2 ^ D.size ∧
      D.size ≤ 5 + (A + 1) * 3 := by
  obtain ⟨hr, _, hc⟩ := replay_active hk hist h
  let k := PolylogAdversary.parameter n
  let A := Parameters.logCap n
  have sh := scheduled_central (n := n) PolylogAdversary.extra hk
  have hg := (active_grid sh hk hr).2
  refine ⟨_, hg, ?_, ?_, Nat.lt_size_self _, (replay_capacity hist hk h).2⟩
  · have hp : 2 ^ k ≤ ArbitraryLabels.pathHeight k :=
      Nat.pow_le_pow_right (by decide) (Nat.le_succ k)
    have he := Nat.mul_le_mul (show hist.length + 1 ≤ horizon n + 1 by omega) (Nat.add_le_add_right hp 2)
    change A + hist.length * (2 * (2 ^ k + 2)) + 2 * (2 ^ k + 2) + 2 ≤
      PolylogSchedule.capacity A (ArbitraryLabels.pathHeight k) n
    unfold PolylogSchedule.capacity
    nlinarith
  · unfold PolylogSchedule.capacity
    omega

end SortingAdversary.Continuous.PolylogPrecision
