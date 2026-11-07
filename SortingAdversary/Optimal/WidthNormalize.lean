import SortingAdversary.Optimal.WidthRepair
import SortingAdversary.Optimal.LocalOracle

/-!
# Executable width normalization

The first two priorities scan the actual free numerical graph in label order.
Every iteration performs a certified physical pin or strict wall cut, and the
chronological trace retains an incident edge from the repair's initial graph.
This last certificate allows historical physical-row accounting to be replayed
without adding any operational dependency on the comparison transcript.
-/

namespace SortingAdversary.Optimal.WidthRepair

open WeakMaps WeakMaps.WeakSystem FiniteInsertion NumericalRepresentation SparseClosure
open GraphBalls PoolState

variable {n : ℕ}

namespace Step

/-- Every physical pin is justified by an incident edge in the specified
reservation graph. A later pin may have removed that edge numerically. -/
def IncidentFrom (E : Rows (Fin n)) {s t : State n} : Step s t → Prop
  | .pin p => (neighbors E p.vertex).Nonempty
  | .lowerCut .. => True
  | .upperCut .. => True

theorem incidentFrom_mono {E F : Rows (Fin n)} {s t : State n} (a : Step s t)
    (hEF : ∀ x y, E x y = true → F x y = true) (h : a.IncidentFrom E) :
    a.IncidentFrom F := by
  cases a with
  | pin p => exact h.mono (SparseRepairGraph.neighbors_mono E F hEF p.vertex)
  | lowerCut => trivial
  | upperCut => trivial

theorem numerical_edge_old {s t : State n} (a : Step s t) {u v : Fin n}
    (h : t.numerical.system.edge u v = true) : s.numerical.system.edge u v = true := by
  have hh : closure t.rows.active u v = true := by
    simpa only [State.numerical, closeSystem, SourcePartition.view, lookup_tableClosure] using h
  have hout := closure_subset_closed t.rows.active (closure s.rows.active)
    (closure_refl _) (closure_trans _) (fun x y hxy => closure_old _ (a.active_old x y hxy)) u v hh
  simpa only [State.numerical, closeSystem, SourcePartition.view, lookup_tableClosure] using hout

theorem comparable_le {s t : State n} (a : Step s t) (v : Fin n) :
    comparableCount t.numerical v ≤ comparableCount s.numerical v := by
  apply Finset.card_le_card
  intro u hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact ⟨hu.1, hu.2.elim (fun h => Or.inl (a.numerical_edge_old h))
    (fun h => Or.inr (a.numerical_edge_old h))⟩

def sparseBounds {s t : State n} (a : Step s t) {H d : ℕ}
    (g : LocalOracle.SparseBounds s.rows H d) : LocalOracle.SparseBounds t.rows H d where
  rank := g.rank
  strict x y h := g.strict x y ⟨h.1, a.active_old x y h.2⟩
  height := g.height
  degree x := (SparseRepairGraph.degree_mono _ _ a.active_old x).trans (g.degree x)

end Step

namespace Trace

def IncidentFrom (E : Rows (Fin n)) {s t : State n} : Trace s t → Prop
  | .nil _ => True
  | .cons head tail => head.IncidentFrom E ∧ tail.IncidentFrom E

theorem incidentFrom_mono {E F : Rows (Fin n)} {s t : State n} (trace : Trace s t)
    (hEF : ∀ x y, E x y = true → F x y = true) (h : trace.IncidentFrom E) :
    trace.IncidentFrom F := by
  induction trace with
  | nil => trivial
  | cons head tail ih => exact ⟨head.incidentFrom_mono hEF h.1, ih h.2⟩

theorem active_old {s t : State n} (trace : Trace s t) (u v : Fin n)
    (h : t.rows.active u v = true) : s.rows.active u v = true := by
  induction trace with
  | nil => exact h
  | cons head tail ih => exact head.active_old u v (ih h)

theorem comparable_le {s t : State n} (trace : Trace s t) (v : Fin n) :
    comparableCount t.numerical v ≤ comparableCount s.numerical v := by
  induction trace with
  | nil => rfl
  | cons head tail ih => exact ih.trans (head.comparable_le v)

def sparseBounds {s t : State n} (trace : Trace s t) {H d : ℕ}
    (g : LocalOracle.SparseBounds s.rows H d) : LocalOracle.SparseBounds t.rows H d where
  rank := g.rank
  strict x y h := g.strict x y ⟨h.1, trace.active_old x y h.2⟩
  height := g.height
  degree x := (SparseRepairGraph.degree_mono _ _ trace.active_old x).trans (g.degree x)

theorem incidentFrom_append {E : Rows (Fin n)} {s t u : State n}
    (first : Trace s t) (second : Trace t u)
    (hfirst : first.IncidentFrom E) (hsecond : second.IncidentFrom E) :
    (first.append second).IncidentFrom E := by
  induction first with
  | nil => exact hsecond
  | cons head tail ih => exact ⟨hfirst.1, ih second hfirst.2 hsecond⟩

end Trace

/-- Explicit width-stage constants. The insertion constant is derived from
the sparse comparable cap, rather than an assumed point-mass premise. -/
structure WidthParameters where
  W₀ : ℕ
  B : ℕ
  L : ℕ
  large : 32 ≤ W₀
  cutBudget : 2 * 4 ^ B < L

namespace WidthParameters

def constant (p : WidthParameters) : ℕ := 2 * 4 ^ p.B
def cheapCharge (p : WidthParameters) : ℚ := p.W₀ * 4 ^ p.B
def cutCharge (p : WidthParameters) : ℚ := (p.L : ℚ) / (p.L - p.constant)

theorem two_le_L (p : WidthParameters) : 2 ≤ p.L := by
  have h : 1 ≤ 4 ^ p.B := Nat.one_le_pow _ _ (by decide)
  have := p.cutBudget
  omega

theorem L_pos (p : WidthParameters) : 0 < p.L := lt_of_lt_of_le (by decide) p.two_le_L

theorem constant_lt (p : WidthParameters) : (p.constant : ℚ) < p.L := by
  exact_mod_cast p.cutBudget

end WidthParameters

def ComparableBound (s : State n) (B : ℕ) : Prop :=
  ∀ v, comparableCount s.numerical v ≤ B

theorem comparableBound_step {s t : State n} (a : Step s t) {B : ℕ}
    (h : ComparableBound s B) : ComparableBound t B := fun v => (a.comparable_le v).trans (h v)

theorem comparableBound_trace {s t : State n} (trace : Trace s t) {B : ℕ}
    (h : ComparableBound s B) : ComparableBound t B := fun v => (trace.comparable_le v).trans (h v)

theorem comparableBound_of_sparse (s : State n) (H d : ℕ)
    (g : LocalOracle.SparseBounds s.rows H d) : ComparableBound s ((d + 1) ^ (H + 1)) := by
  intro v
  exact NumericalGeometry.comparableCount_le s.rows.view g.rank H d g.strict g.height g.degree v

private theorem retained_charge {N N' : ℕ} {L C : ℚ} (hN : 0 < N)
    (hL : 0 < L) (hC : C < L) (h : 1 - C / L ≤ (N' : ℚ) / N) :
    (N : ℚ) ≤ (L / (L - C)) * N' := by
  have hNQ : (0 : ℚ) < N := by exact_mod_cast hN
  have hd : 0 < L - C := sub_pos.mpr hC
  have hmul := (le_div_iff₀ hNQ).mp h
  have hmul' := mul_le_mul_of_nonneg_left hmul hL.le
  have hcancel : L * ((1 - C / L) * (N : ℚ)) = (L - C) * N := by
    field_simp
  rw [hcancel] at hmul'
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hd).mpr
  nlinarith

namespace State

def cheapUpdate (s : State n) (p : WidthParameters) (hB : ComparableBound s p.B)
    (v : Fin n) (hv : (neighbors s.rows.active v).Nonempty) (hw : s.width v < p.W₀) :
    PinUpdate s where
  vertex := v
  free := s.nonisolated_free hv
  colour := s.centralColour v
  supported := s.centralColour_window v
  mate := s.nonisolated_mate hv
  result := Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v
    (s.nonisolated_free hv) (s.centralColour v) (s.centralColour_window v)
  actual := rfl
  data := s.promotionData v (s.nonisolated_free hv) (s.centralColour v) (s.centralColour_window v)
  charge := p.cheapCharge
  retained := by
    have h := s.cheapPin_count v hv p.W₀ p.B hw.le (hB v)
    dsimp only [WidthParameters.cheapCharge]
    exact_mod_cast h

theorem lower_cut_charge (s : State n) (p : WidthParameters) (hB : ComparableBound s p.B)
    (u v : Fin n) (hlive : s.rows.active u v = true)
    (hscale : p.L * s.width v < s.width u)
    (hratio : 2 * s.width v < s.width u) :
    (s.pool.system.count : ℚ) ≤ p.cutCharge * (s.lowerCut u v hlive hratio).pool.system.count := by
  apply retained_charge s.pool.count_pos (by exact_mod_cast p.L_pos) p.constant_lt
  have h := s.lowerCut_retention u v hlive hratio p.L (by exact_mod_cast p.L_pos)
    (by exact_mod_cast hscale.le)
  apply le_trans _ h
  apply sub_le_sub_left
  apply div_le_div_of_nonneg_right _ (by positivity)
  change (2 : ℚ) * 4 ^ comparableCount s.numerical u ≤ (2 * 4 ^ p.B : ℕ)
  norm_cast
  exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) (hB u))

theorem upper_cut_charge (s : State n) (p : WidthParameters) (hB : ComparableBound s p.B)
    (u v : Fin n) (hlive : s.rows.active u v = true)
    (hscale : p.L * s.width u < s.width v)
    (hratio : 2 * s.width u < s.width v) :
    (s.pool.system.count : ℚ) ≤ p.cutCharge * (s.upperCut u v hlive hratio).pool.system.count := by
  apply retained_charge s.pool.count_pos (by exact_mod_cast p.L_pos) p.constant_lt
  have h := s.upperCut_retention u v hlive hratio p.L (by exact_mod_cast p.L_pos)
    (by exact_mod_cast hscale.le)
  apply le_trans _ h
  apply sub_le_sub_left
  apply div_le_div_of_nonneg_right _ (by positivity)
  change (2 : ℚ) * 4 ^ comparableCount s.numerical v ≤ (2 * 4 ^ p.B : ℕ)
  norm_cast
  exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) (hB v))

end State

/-- The two finite, lexicographically ordered scans used before a scale group. -/
def narrowWitness (s : State n) (W₀ : ℕ) : Option (Fin n) :=
  (List.finRange n).find? (fun v => decide ((neighbors s.rows.active v).Nonempty ∧ s.width v < W₀))

def steepWitness (s : State n) (L : ℕ) : Option (Fin n × Fin n) :=
  ((List.finRange n).flatMap (fun u => (List.finRange n).map (fun v => (u, v)))).find?
    (fun uv => decide (s.rows.active uv.1 uv.2 = true ∧
      (L * s.width uv.2 < s.width uv.1 ∨ L * s.width uv.1 < s.width uv.2)))

theorem narrowWitness_some (s : State n) (W₀ : ℕ) {v : Fin n}
    (h : narrowWitness s W₀ = some v) :
    (neighbors s.rows.active v).Nonempty ∧ s.width v < W₀ := by
  exact of_decide_eq_true (List.find?_some (p := fun w =>
    decide ((neighbors s.rows.active w).Nonempty ∧ s.width w < W₀)) h)

theorem narrowWitness_none (s : State n) (W₀ : ℕ) : narrowWitness s W₀ = none ↔
    ∀ v, (neighbors s.rows.active v).Nonempty → W₀ ≤ s.width v := by
  simp [narrowWitness, List.find?_eq_none]

theorem steepWitness_some (s : State n) (L : ℕ) {uv : Fin n × Fin n}
    (h : steepWitness s L = some uv) : s.rows.active uv.1 uv.2 = true ∧
      (L * s.width uv.2 < s.width uv.1 ∨ L * s.width uv.1 < s.width uv.2) := by
  exact of_decide_eq_true (List.find?_some (p := fun pair : Fin n × Fin n => decide (s.rows.active pair.1 pair.2 = true ∧
    (L * s.width pair.2 < s.width pair.1 ∨ L * s.width pair.1 < s.width pair.2))) h)

theorem steepWitness_none (s : State n) (L : ℕ) : steepWitness s L = none ↔
    ∀ u v, s.rows.active u v = true →
      s.width u ≤ L * s.width v ∧ s.width v ≤ L * s.width u := by
  simp [steepWitness, List.find?_eq_none, not_or]

structure EarlyNormal (s : State n) (W₀ L : ℕ) : Prop where
  wide : ∀ v, (neighbors s.rows.active v).Nonempty → W₀ ≤ s.width v
  edgeScale : ∀ u v, s.rows.active u v = true →
    s.width u ≤ L * s.width v ∧ s.width v ≤ L * s.width u

inductive EarlyMove (s : State n) (W₀ L : ℕ) where
  | cheap (v : Fin n) (incident : (neighbors s.rows.active v).Nonempty) (narrow : s.width v < W₀)
  | lower (u v : Fin n) (live : s.rows.active u v = true) (steep : L * s.width v < s.width u)
  | upper (u v : Fin n) (live : s.rows.active u v = true) (steep : L * s.width u < s.width v)

def selectEarly (s : State n) (W₀ L : ℕ) : Option (EarlyMove s W₀ L) :=
  match hn : narrowWitness s W₀ with
  | some v => some (.cheap v (narrowWitness_some s W₀ hn).1 (narrowWitness_some s W₀ hn).2)
  | none => match he : steepWitness s L with
    | none => none
    | some uv =>
      if hs : L * s.width uv.2 < s.width uv.1 then
        some (.lower uv.1 uv.2 (steepWitness_some s L he).1 hs)
      else some (.upper uv.1 uv.2 (steepWitness_some s L he).1
        ((steepWitness_some s L he).2.resolve_left hs))

theorem selectEarly_none (s : State n) (W₀ L : ℕ) : selectEarly s W₀ L = none ↔
    EarlyNormal s W₀ L := by
  unfold selectEarly
  split
  · rename_i v hv
    simp only [Option.some_ne_none, false_iff]
    intro h
    have hn := narrowWitness_some s W₀ hv
    exact Nat.not_lt_of_ge (h.wide v hn.1) hn.2
  · rename_i hn
    split
    · rename_i he
      simp only [true_iff]
      exact ⟨(narrowWitness_none s W₀).mp hn, (steepWitness_none s L).mp he⟩
    · rename_i uv he
      have hs := steepWitness_some s L he
      split <;> simp only [Option.some_ne_none, false_iff] <;> intro h
      all_goals have hh := h.edgeScale uv.1 uv.2 hs.1
      all_goals omega

def EarlyMove.execute {s : State n} (p : WidthParameters) (hB : ComparableBound s p.B)
    (move : EarlyMove s p.W₀ p.L) : Σ t : State n, Step s t :=
  match move with
  | .cheap v incident narrow => ⟨_, .pin (s.cheapUpdate p hB v incident narrow)⟩
  | .lower u v live steep =>
    let ratio := (Nat.mul_le_mul_right (s.width v) p.two_le_L).trans_lt steep
    ⟨_, .lowerCut s u v live ratio p.cutCharge (s.lower_cut_charge p hB u v live steep ratio)⟩
  | .upper u v live steep =>
    let ratio := (Nat.mul_le_mul_right (s.width u) p.two_le_L).trans_lt steep
    ⟨_, .upperCut s u v live ratio p.cutCharge (s.upper_cut_charge p hB u v live steep ratio)⟩

theorem EarlyMove.execute_incident {s : State n} (p : WidthParameters) (hB : ComparableBound s p.B)
    (move : EarlyMove s p.W₀ p.L) : (move.execute p hB).2.IncidentFrom s.rows.active := by
  cases move with
  | cheap v hi hn => exact hi
  | lower => trivial
  | upper => trivial

/-- The chronological W1/W2 classifications refer to the very same primitive
steps that the tree replays. No operation is classified from its charge. -/
inductive EarlyEvents (p : WidthParameters) : {s t : State n} → Trace s t → Type
  | nil (s : State n) : EarlyEvents p (.nil s)
  | cons {s t : State n} (hB : ComparableBound s p.B) (move : EarlyMove s p.W₀ p.L)
      (rest : Trace (move.execute p hB).1 t) (events : EarlyEvents p rest) :
      EarlyEvents p (.cons (move.execute p hB).2 rest)

/-- The finite W1/W2 loop returns the actual chronological transition trace,
the preserved sparse cap, and both stopping conditions. -/
structure EarlyResult (s : State n) (p : WidthParameters) where
  final : State n
  trace : Trace s final
  events : EarlyEvents p trace
  incident : trace.IncidentFrom s.rows.active
  bound : ComparableBound final p.B
  normal : EarlyNormal final p.W₀ p.L

def normalizeEarly (s : State n) (p : WidthParameters) (hB : ComparableBound s p.B) : EarlyResult s p :=
  match hm : selectEarly s p.W₀ p.L with
  | none => ⟨s, .nil s, .nil s, trivial, hB, (selectEarly_none s p.W₀ p.L).mp hm⟩
  | some move =>
    let next := move.execute p hB
    let rest := normalizeEarly next.1 p (comparableBound_step next.2 hB)
    ⟨rest.final, .cons next.2 rest.trace, .cons hB move rest.trace rest.events,
      ⟨move.execute_incident p hB, rest.trace.incidentFrom_mono next.2.active_old rest.incident⟩,
      rest.bound, rest.normal⟩
termination_by s.measure
decreasing_by exact (move.execute p hB).2.measure_lt

theorem normalizeEarly_steps_le (s : State n) (p : WidthParameters) (hB : ComparableBound s p.B) :
    (normalizeEarly s p hB).trace.length ≤ s.pool.free.card + (SparseRepairGraph.rawRows s.rows.active).card := by
  have h := (normalizeEarly s p hB).trace.length_add_measure_le
  exact (Nat.le_add_right _ _).trans h

end SortingAdversary.Optimal.WidthRepair
