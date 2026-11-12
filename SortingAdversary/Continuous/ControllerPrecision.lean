import SortingAdversary.Continuous.RuntimePrecision
import SortingAdversary.Continuous.ControllerLocal
import SortingAdversary.Continuous.ControllerSelection
import SortingAdversary.Continuous.RecordInvariant

/-!
# Stored precision along the actual controller

`Memory.OnGrid` covers interval bounds, rational location paths, and reduced
anchor codes. The concrete mutations preserve this predicate, and the actual
selection and repair loops increase its exponent by at most `log₂ E_k` per
emitted refinement. Recording an answer adds no precision.
-/

namespace SortingAdversary.Continuous.Controller

open FiniteAveraging OrderRegion TreeState Certificates Precision UniformStages
open TraceAccounting (Move Action)

variable {n : ℕ}

def Memory.OnGrid (M : Memory n) (F : ℕ) : Prop :=
  BoundsOnGrid M.tree.system F ∧
    (∀ x c, c ∈ M.tree.location x → OnDyadicGrid F c) ∧
    ∀ x c, c ∈ M.paths x → OnDyadicGrid F c.coordinate

theorem Memory.OnGrid.mono {M : Memory n} {F G : ℕ}
    (h : M.OnGrid F) (hFG : F ≤ G) : M.OnGrid G :=
  ⟨bounds_mono h.1 hFG, (fun x c hc => grid_mono (h.2.1 x c hc) hFG),
    fun x c hc => grid_mono (h.2.2 x c hc) hFG⟩

theorem initial_onGrid (n : ℕ) : (initial n).OnGrid 0 := by
  refine ⟨Precision.initial_onGrid n 0, ?_, ?_⟩
  · simp [initial, TreeState.initial]
  · simp [initial]

theorem Memory.OnGrid.applyMove {M : Memory n} {F : ℕ} (h : M.OnGrid F)
    (m : Move n) (hc : OnDyadicGrid F m.anchor.coordinate) : (applyMove M m).OnGrid F := by
  refine ⟨normalize_onGrid _ F m.order (resetCoordinate_onGrid _ F _ _ h.1 hc), ?_, ?_⟩
  · intro x c hmem
    by_cases hx : x = m.item
    · subst x
      simp only [Controller.applyMove, TreeState.normalize, refineAt, Function.update_self,
        List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | rfl
      · exact h.2.1 _ _ hmem
      · exact hc
    · simp only [Controller.applyMove, TreeState.normalize, refineAt, Function.update_of_ne hx] at hmem
      exact h.2.1 _ _ hmem
  · intro x c hmem
    by_cases hx : x = m.item
    · subst x
      simp only [Controller.applyMove, Function.update_self, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | rfl
      · exact h.2.2 _ _ hmem
      · exact hc
    · simp only [Controller.applyMove, Function.update_of_ne hx] at hmem
      exact h.2.2 _ _ hmem

private def routeGrid (F : ℕ) : Routing ℚ → Prop
  | .coordinates => True
  | .leftFree c | .rightFree c => OnDyadicGrid F c
  | .anchors c d => OnDyadicGrid F c ∧ OnDyadicGrid F d

private theorem route_onGrid (F : ℕ) (p q : List ℚ)
    (hp : ∀ c ∈ p, OnDyadicGrid F c) (hq : ∀ c ∈ q, OnDyadicGrid F c) :
    routeGrid F (route p q) := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => trivial
    | cons c q => exact hq c (by simp)
  | cons c p ih =>
    cases q with
    | nil => exact hp c (by simp)
    | cons d q =>
      by_cases hcd : c = d
      · simp only [route, if_pos hcd]
        exact ih q (fun e he => hp e (by simp [he])) (fun e he => hq e (by simp [he]))
      · exact And.intro (hp c (by simp)) (hq d (by simp)) |>
          (by simpa only [route, if_neg hcd, routeGrid] using ·)

private theorem boundBelow_onGrid (D : System (Fin n) ℚ) (F : ℕ) (x : Fin n) (c : ℚ)
    (hD : BoundsOnGrid D F) (hc : OnDyadicGrid F c) : BoundsOnGrid (boundBelow D x c) F := by
  refine ⟨hD.1, fun y => ?_⟩
  by_cases hy : y = x
  · subst y
    simpa only [boundBelow, Function.update_self] using onDyadicGrid_min (hD.2 x) hc
  · simpa only [boundBelow, Function.update_of_ne hy] using hD.2 y

private theorem boundAbove_onGrid (D : System (Fin n) ℚ) (F : ℕ) (x : Fin n) (c : ℚ)
    (hD : BoundsOnGrid D F) (hc : OnDyadicGrid F c) : BoundsOnGrid (boundAbove D x c) F := by
  refine ⟨fun y => ?_, hD.2⟩
  by_cases hy : y = x
  · subst y
    simpa only [boundAbove, Function.update_self] using onDyadicGrid_max (hD.1 x) hc
  · simpa only [boundAbove, Function.update_of_ne hy] using hD.1 y

theorem Memory.OnGrid.record {M : Memory n} {F : ℕ} (h : M.OnGrid F)
    (q : Query n) (a : Answer) (order : List (Fin n)) :
    (applyAction M (.answer q a order)).OnGrid F := by
  have hr := route_onGrid F (M.tree.location q.left) (M.tree.location q.right)
    (h.2.1 q.left) (h.2.1 q.right)
  refine ⟨normalize_onGrid _ F order ?_, h.2.1, h.2.2⟩
  change BoundsOnGrid (recordSystem M.tree.system
    (route (M.tree.location q.left) (M.tree.location q.right)) q.left q.right a) F
  cases he : route (M.tree.location q.left) (M.tree.location q.right) with
  | coordinates => cases a <;> exact h.1
  | leftFree c =>
    rw [he] at hr
    cases a
    · exact boundBelow_onGrid _ F _ c h.1 hr
    · exact boundAbove_onGrid _ F _ c h.1 hr
  | rightFree c =>
    rw [he] at hr
    cases a
    · exact boundAbove_onGrid _ F _ c h.1 hr
    · exact boundBelow_onGrid _ F _ c h.1 hr
  | anchors c d => cases a <;> exact h.1

def actionRefinements : Action n → ℕ
  | .selection _ | .degree _ => 1
  | .path ms => ms.length
  | .answer _ _ _ => 0

def refinementCount (actions : List (Action n)) : ℕ := (actions.map actionRefinements).sum

@[simp] theorem refinementCount_nil : refinementCount ([] : List (Action n)) = 0 := rfl

@[simp] theorem refinementCount_cons (a : Action n) (as : List (Action n)) :
    refinementCount (a :: as) = actionRefinements a + refinementCount as := rfl

@[simp] theorem refinementCount_append (as bs : List (Action n)) :
    refinementCount (as ++ bs) = refinementCount as + refinementCount bs := by
  simp [refinementCount]

theorem attempt_refine_onGrid (M : Memory n) (F k : ℕ) (hk : 0 < k)
    (hM : Geometric M) (hgrid : M.OnGrid F) (q : Query n) (x : Fin n) (c : ℚ)
    (h : attempt M k q = .refine x c) :
    OnDyadicGrid (F + Nat.log 2 (enumerationBudget k hk)) c := by
  cases hr : route (M.tree.location q.left) (M.tree.location q.right) with
  | coordinates =>
    exact RuntimePrecision.select_refine_onGrid M.tree.system F k hk _ _ _ _ hgrid.1
      hM.rationalBounds hM.widths (by simpa only [attempt, hr] using h)
  | leftFree a =>
    exact RuntimePrecision.selectThreshold_refine_onGrid M.tree.system F k hk _ _ _ _ hgrid.1
      hM.rationalBounds hM.widths (by simpa only [attempt, hr] using h)
  | rightFree a =>
    have ht : ArbitraryLabels.selectThreshold M.tree.system k q.right a = .refine x c := by
      cases ht : ArbitraryLabels.selectThreshold M.tree.system k q.right a with
      | answer b => simp only [attempt, hr, ht, reverseResult] at h; cases h
      | refine y v =>
        have he : y = x ∧ v = c := by simpa only [attempt, hr, ht, reverseResult,
          LocalSelection.Result.refine.injEq] using h
        simpa only [he.1, he.2] using ht
    exact RuntimePrecision.selectThreshold_refine_onGrid M.tree.system F k hk _ _ _ _ hgrid.1
      hM.rationalBounds hM.widths ht
  | anchors a b => simp only [attempt, hr] at h; cases h

theorem attempt_move_onGrid (M : Memory n) (F k : ℕ) (hk : 64 ≤ k)
    (hM : Admissible k M) (hgrid : M.OnGrid F) (q : Query n) (x : Fin n) (c : ℚ)
    (h : attempt M k q = .refine x c) :
    (applyMove M (makeMove M x c)).OnGrid
      (F + Nat.log 2 (enumerationBudget k (by omega))) := by
  have hg := attempt_refine_onGrid M F k (by omega) hM.toGeometric hgrid q x c h
  have hc := (attempt_refine_spec M k hk hM q x c h).2.1
  apply (hgrid.mono (Nat.le_add_right _ _)).applyMove
  rwa [hc]

theorem anchor_move_onGrid (M : Memory n) (F k : ℕ) (hk : 64 ≤ k)
    (hM : Admissible k M) (hgrid : M.OnGrid F) (x : Fin n) :
    (applyMove M (makeMove M x (ArbitraryLabels.chooseAnchor M.tree.system k x))).OnGrid
      (F + Nat.log 2 (enumerationBudget k (by omega))) := by
  have he := ArbitraryLabels.weak_endpoints M.tree.system hM.normalized hM.toGeometric.widths
  have hg := RuntimePrecision.chooseAnchor_onGrid M.tree.system F k (by omega) x hgrid.1
    hM.degree he.1 he.2 hM.toGeometric.widths
    (hM.toGeometric.rationalBounds x).1 (hM.toGeometric.rationalBounds x).2
  have hc := (anchor_move_spec M k hk hM x).1
  apply (hgrid.mono (Nat.le_add_right _ _)).applyMove
  rwa [hc]

theorem pathBatch_onGrid (M : Memory n) (F k : ℕ) (hk : 64 ≤ k)
    (hM : Admissible k M) (hgrid : M.OnGrid F) (xs : List (Fin n)) :
    Admissible k (pathBatch k M xs).1 ∧
      (pathBatch k M xs).1.OnGrid
        (F + Nat.log 2 (enumerationBudget k (by omega)) * xs.length) := by
  induction xs generalizing M F with
  | nil => simpa only [pathBatch, List.length_nil, mul_zero, add_zero] using And.intro hM hgrid
  | cons x xs ih =>
    have hnew := (anchor_move_spec M k hk hM x).2.2.2.1
    have hg := anchor_move_onGrid M F k hk hM hgrid x
    have ht := ih _ _ hnew hg
    simpa only [pathBatch, List.length_cons, mul_add, mul_one, Nat.add_assoc,
      Nat.add_comm (Nat.log 2 (enumerationBudget k (by omega))),
      Nat.add_left_comm (Nat.log 2 (enumerationBudget k (by omega)))] using ht

theorem selectLoop_onGrid (k : ℕ) (hk : 64 ≤ k) (q : Query n) (fuel : ℕ)
    (M : Memory n) (F : ℕ) (hM : Admissible k M) (hgrid : M.OnGrid F)
    {r : Result n} (h : selectLoop k q fuel M = some r) :
    Admissible k r.memory ∧
      r.memory.OnGrid (F + Nat.log 2 (enumerationBudget k (by omega)) * refinementCount r.actions) := by
  induction fuel generalizing M F r with
  | zero => simp [selectLoop] at h
  | succ fuel ih =>
    cases ha : attempt M k q with
    | answer a =>
      simp only [selectLoop, ha, Option.some.injEq] at h
      subst r
      simpa only [refinementCount_nil, mul_zero, add_zero] using And.intro hM hgrid
    | refine x c =>
      simp only [selectLoop, ha] at h
      cases ht : selectLoop k q fuel (applyMove M (makeMove M x c)) with
      | none => simp only [ht, Option.map_none] at h; contradiction
      | some r' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst r
        have hh := ih _ _ (attempt_refine_admissible M k hk hM q x c ha)
          (attempt_move_onGrid M F k hk hM hgrid q x c ha) ht
        simpa only [refinementCount_cons, actionRefinements, mul_add, mul_one,
          Nat.add_assoc] using hh

theorem repair_onGrid (M : Memory n) (F k : ℕ) (hk : 64 ≤ k)
    (hM : Admissible k M) (hgrid : M.OnGrid F) :
    Admissible k (repair k M).1 ∧
      (repair k M).1.OnGrid
        (F + Nat.log 2 (enumerationBudget k (by omega)) * refinementCount (repair k M).2) := by
  cases hp : GraphPaths.firstPath M.tree.system.edge (2 ^ k) with
  | some xs =>
    have hh := pathBatch_onGrid M F k hk hM hgrid xs
    have hlen := congrArg List.length (pathBatch_labels k M xs)
    simp only [List.length_map] at hlen
    simpa only [repair, hp, refinementCount_cons, actionRefinements, refinementCount_nil,
      Nat.add_zero, hlen] using hh
  | none =>
    cases hd : degreeChoice M k with
    | none => simpa only [repair, hp, hd, refinementCount_nil, mul_zero, add_zero] using And.intro hM hgrid
    | some x =>
      have hn := (anchor_move_spec M k hk hM x).2.2.2.1
      have hg := anchor_move_onGrid M F k hk hM hgrid x
      simpa only [repair, hp, hd, refinementCount_cons, actionRefinements, refinementCount_nil,
        Nat.add_zero, mul_one] using And.intro hn hg

/-- Every completed call increases precision by at most one budget increment
per actual refinement in its emitted trace. -/
theorem compare_onGrid (M : Memory n) (F k : ℕ) (hk : 64 ≤ k)
    (hM : Ready k M) (hgrid : M.OnGrid F) (q : Query n) {r : Result n}
    (h : compare k M q = some r) :
    r.memory.OnGrid (F + Nat.log 2 (enumerationBudget k (by omega)) * refinementCount r.actions) := by
  cases hs : selectLoop k q 3 M with
  | none => simp only [compare, hs, Option.map_none] at h; contradiction
  | some s =>
    simp only [compare, hs, Option.map_some, Option.some.injEq] at h
    subst r
    have hsel := selectLoop_spec k hk q 3 M hM s hs
    have hg := (selectLoop_onGrid k hk q 3 M F hM.admissible hgrid hs).2
    have hp := attempt_answer_probability s.memory k (by omega) hsel.1.toGeometric q s.answer hsel.2.1
    have hrgeom := hsel.1.toGeometric.recorded hk q s.answer hp.1 hp.2
    have hradm := hsel.1.recordedAdmissible q s.answer hrgeom
    have hrgrid := hg.record q s.answer (answerOrder s.memory q s.answer)
    have hrepair := (repair_onGrid (recorded s.memory q s.answer) _ k hk hradm hrgrid).2
    simpa only [recorded, answerOrder, refinementCount_append, refinementCount_cons,
      actionRefinements, refinementCount_nil, zero_add, Nat.add_zero, mul_add,
      Nat.add_assoc] using hrepair

/-- This stored counter is exactly the number of refinements from the
initial memory, because every move appends one reduced anchor to one path. -/
def totalDepth (M : Memory n) : ℕ := ∑ x, (M.paths x).length

theorem totalDepth_initial (n : ℕ) : totalDepth (initial n) = 0 := by simp [totalDepth, initial]

theorem totalDepth_applyMove (M : Memory n) (m : Move n) :
    totalDepth (applyMove M m) = totalDepth M + 1 := by
  have he : ∀ x, ((applyMove M m).paths x).length =
      (M.paths x).length + if x = m.item then 1 else 0 := by
    intro x
    by_cases hx : x = m.item <;> simp [Controller.applyMove, hx]
  unfold totalDepth
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

theorem totalDepth_applyMoves (M : Memory n) (ms : List (Move n)) :
    totalDepth (applyMoves M ms) = totalDepth M + ms.length := by
  induction ms generalizing M with
  | nil => simp [applyMoves]
  | cons m ms ih =>
    simp only [applyMoves, ih, totalDepth_applyMove, List.length_cons]
    omega

theorem totalDepth_applyAction (M : Memory n) (a : Action n) :
    totalDepth (applyAction M a) = totalDepth M + actionRefinements a := by
  cases a with
  | selection m | degree m => exact totalDepth_applyMove M m
  | path ms => exact totalDepth_applyMoves M ms
  | answer q a order => rfl

theorem totalDepth_runActions (M : Memory n) (actions : List (Action n)) :
    totalDepth (runActions M actions) = totalDepth M + refinementCount actions := by
  induction actions generalizing M with
  | nil => simp [runActions]
  | cons a as ih =>
    change totalDepth (runActions (applyAction M a) as) = _
    rw [ih, totalDepth_applyAction, refinementCount_cons]
    omega

theorem totalDepth_compare (M : Memory n) (k : ℕ) (q : Query n) {r : Result n}
    (h : compare k M q = some r) :
    totalDepth r.memory = totalDepth M + refinementCount r.actions := by
  rw [compare_memory k M q r h, totalDepth_runActions]

/-- The precise stored-state induction: after `P` actual refinements every
stored rational has at most `P log₂ E_k` fractional binary digits. -/
def Memory.Precise (M : Memory n) (k : ℕ) (hk : 0 < k) : Prop :=
  M.OnGrid (totalDepth M * Nat.log 2 (enumerationBudget k hk))

theorem initial_precise (n k : ℕ) (hk : 0 < k) : (initial n).Precise k hk := by
  simpa only [Memory.Precise, totalDepth_initial, zero_mul] using initial_onGrid n

theorem compare_precise (M : Memory n) (k : ℕ) (hk : 64 ≤ k)
    (hM : Ready k M) (hprecise : M.Precise k (by omega)) (q : Query n) {r : Result n}
    (h : compare k M q = some r) : r.memory.Precise k (by omega) := by
  have hg := compare_onGrid M _ k hk hM hprecise q h
  unfold Memory.Precise
  rw [totalDepth_compare M k q h, add_mul]
  simpa only [Nat.mul_comm (refinementCount r.actions)] using hg

theorem stored_anchor_level {M : Memory n} {F : ℕ} (h : M.OnGrid F)
    (x : Fin n) (c : DyadicAnchor) (hc : c ∈ M.paths x) : c.1 + 1 ≤ F :=
  dyadicAnchor_level_le_grid c (h.2.2 x c hc)

theorem stored_endpoint_bits {M : Memory n} {F : ℕ} (h : M.OnGrid F) (hM : Geometric M)
    (x : Fin n) :
    (M.tree.system.lower x).den.size ≤ F + 1 ∧
    (M.tree.system.lower x).num.natAbs.size ≤ F + 1 ∧
    (M.tree.system.upper x).den.size ≤ F + 1 ∧
    (M.tree.system.upper x).num.natAbs.size ≤ F + 1 := by
  have hb := hM.rationalBounds x
  have hw := hM.widths x
  have hl := rational_bits (h.1.1 x) hb.1 (hw.le.trans hb.2)
  have hu := rational_bits (h.1.2 x) (hb.1.trans hw.le) hb.2
  exact ⟨hl.1, hl.2, hu.1, hu.2⟩

theorem stored_anchor_bits {M : Memory n} {F : ℕ} (h : M.OnGrid F)
    (x : Fin n) (c : DyadicAnchor) (hc : c ∈ M.paths x) :
    c.coordinate.den.size ≤ F + 1 ∧ c.coordinate.num.natAbs.size ≤ F + 1 :=
  rational_bits (h.2.2 x c hc) c.coordinate_pos.le c.coordinate_lt_one.le

end SortingAdversary.Continuous.Controller
