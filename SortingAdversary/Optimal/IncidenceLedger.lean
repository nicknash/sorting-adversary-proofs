import SortingAdversary.Optimal.Accounting
import Mathlib.Data.List.Nodup

/-!
# Chronological charging to real comparison endpoints

The executable ledger uses immutable natural-number node identities. A
physical call appends one optional real free--free row at its stopping node;
it cannot create a row at any other node. Admissions are accepted only once
per node and label. A promotion removes a currently free member and saves
its actual previously recorded endpoint incidences. Reserved path members
may therefore use their original witnesses after their live degree falls.

Every accepted finite action sequence satisfies the incidence budgets proved
below. Neither the promotion bound nor an injective charge map is a field of
the state or a premise of the runner theorem.
-/

namespace SortingAdversary.Optimal.IncidenceLedger

open scoped BigOperators

abbrev Location (n : ℕ) := ℕ × Fin n
abbrev Endpoint := ℕ × Bool

structure Row (n : ℕ) where
  node : ℕ
  left : Fin n
  right : Fin n
  deriving DecidableEq

def Row.endpoint {n : ℕ} (r : Row n) (side : Bool) : Location n :=
  (r.node, if side then r.right else r.left)

def recordedEndpoint {n : ℕ} (calls : List (Option (Row n))) (e : Endpoint) :
    Option (Location n) := (calls[e.1]?).join.map (fun r => r.endpoint e.2)

def endpointUniverse {n : ℕ} (calls : List (Option (Row n))) : Finset Endpoint :=
  (Finset.range calls.length) ×ˢ Finset.univ

def incidences {n : ℕ} (calls : List (Option (Row n))) (x : Location n) : Finset Endpoint :=
  (endpointUniverse calls).filter (fun e => recordedEndpoint calls e = some x)

theorem mem_incidences {n : ℕ} (calls : List (Option (Row n))) (x : Location n) (e : Endpoint) :
    e ∈ incidences calls x ↔ e.1 < calls.length ∧ recordedEndpoint calls e = some x := by
  simp [incidences, endpointUniverse]

theorem recordedEndpoint_append {n : ℕ} (calls extra : List (Option (Row n)))
    (e : Endpoint) (he : e.1 < calls.length) :
    recordedEndpoint (calls ++ extra) e = recordedEndpoint calls e := by
  simp only [recordedEndpoint, List.getElem?_append_left he]

theorem incidences_append {n : ℕ} (calls extra : List (Option (Row n))) (x : Location n) :
    incidences calls x ⊆ incidences (calls ++ extra) x := by
  intro e he
  obtain ⟨ht, hw⟩ := (mem_incidences calls x e).mp he
  apply (mem_incidences _ _ _).mpr
  exact ⟨by simp only [List.length_append]; omega, (recordedEndpoint_append _ _ _ ht).trans hw⟩

inductive Kind where
  | cheap | degree | path | scale
  deriving DecidableEq

structure Move (n : ℕ) where
  location : Location n
  kind : Kind
  charges : Finset Endpoint
  deriving DecidableEq

structure State (n : ℕ) where
  entered : Finset (Location n)
  free : Finset (Location n)
  calls : List (Option (Row n))
  moves : Finset (Move n)

def initial {n : ℕ} (free : Finset (Location n)) : State n :=
  ⟨free, free, [], ∅⟩

/-- A live neighbor is an opposite endpoint of a previously recorded real
row whose two labels are still free. Parallel records do not increase degree:
the image into neighboring locations removes repetitions. -/
def liveIncidences {n : ℕ} (s : State n) (x : Location n) : Finset Endpoint :=
  (incidences s.calls x).filter (fun e =>
    (recordedEndpoint s.calls (e.1, !e.2)).any (fun y => decide (y ∈ s.free ∧ y ≠ x)))

def neighbors {n : ℕ} (s : State n) (x : Location n) : Finset (Option (Location n)) :=
  (liveIncidences s x).image (fun e => recordedEndpoint s.calls (e.1, !e.2))

def liveDegree {n : ℕ} (s : State n) (x : Location n) : ℕ := (neighbors s x).card

theorem liveDegree_le_incidences {n : ℕ} (s : State n) (x : Location n) :
    liveDegree s x ≤ (incidences s.calls x).card :=
  (Finset.card_image_le).trans (Finset.card_le_card (Finset.filter_subset _ _))

structure Valid {n : ℕ} (threshold : ℕ) (s : State n) : Prop where
  free_entered : s.free ⊆ s.entered
  move_entered : ∀ m ∈ s.moves, m.location ∈ s.entered
  move_not_free : ∀ m ∈ s.moves, m.location ∉ s.free
  unique : ∀ m ∈ s.moves, ∀ m' ∈ s.moves, m.location = m'.location → m = m'
  witnessed : ∀ m ∈ s.moves, m.charges.Nonempty
  recorded : ∀ m ∈ s.moves, m.charges ⊆ incidences s.calls m.location
  degree : ∀ m ∈ s.moves, m.kind = .degree → threshold ≤ m.charges.card

theorem initial_valid {n : ℕ} (threshold : ℕ) (free : Finset (Location n)) :
    Valid threshold (initial free) := by
  constructor <;> simp [initial]

inductive Action (n : ℕ) where
  | admit (location : Location n)
  | physical (row : Option (Row n))
  | promote (location : Location n) (kind : Kind)

def rowAdmissible {n : ℕ} (s : State n) : Option (Row n) → Prop
  | none => True
  | some r => r.endpoint false ∈ s.free ∧ r.endpoint true ∈ s.free ∧ r.left ≠ r.right

instance {n : ℕ} (s : State n) (r : Option (Row n)) : Decidable (rowAdmissible s r) := by
  cases r <;> unfold rowAdmissible <;> infer_instance

/-- An accepted move records the actual historical incidences, rather than
an externally supplied numerical witness. A degree move additionally checks
the present live degree. Other moves retain their historical path witnesses.
-/
def step {n : ℕ} (threshold : ℕ) (s : State n) : Action n → Option (State n)
  | .admit x =>
    if x ∉ s.entered then some { s with entered := insert x s.entered, free := insert x s.free }
    else none
  | .physical row =>
    if rowAdmissible s row then some { s with calls := s.calls ++ [row] }
    else none
  | .promote x kind =>
    if x ∈ s.free ∧ (incidences s.calls x).Nonempty ∧
        (kind = .degree → threshold ≤ liveDegree s x) then
      some { s with free := s.free.erase x, moves := insert ⟨x, kind, incidences s.calls x⟩ s.moves }
    else none

theorem step_valid {n : ℕ} {threshold : ℕ} {s t : State n}
    (hs : Valid threshold s) (a : Action n) (ht : step threshold s a = some t) :
    Valid threshold t := by
  cases a with
  | admit x =>
    simp only [step] at ht
    split at ht
    next hx =>
      cases ht
      constructor
      · exact Finset.insert_subset_insert _ hs.free_entered
      · intro m hm
        exact Finset.mem_insert_of_mem (hs.move_entered m hm)
      · intro m hm hfree
        rcases Finset.mem_insert.mp hfree with heq | hold
        · exact hx (heq ▸ hs.move_entered m hm)
        · exact hs.move_not_free m hm hold
      · exact hs.unique
      · exact hs.witnessed
      · exact hs.recorded
      · exact hs.degree
    next => contradiction
  | physical row =>
    simp only [step] at ht
    split at ht
    next =>
      cases ht
      exact ⟨hs.free_entered, hs.move_entered, hs.move_not_free, hs.unique,
        hs.witnessed, fun m hm => (hs.recorded m hm).trans (incidences_append _ _ _), hs.degree⟩
    next => contradiction
  | promote x kind =>
    simp only [step] at ht
    split at ht
    next h =>
      obtain ⟨hfree, hwitness, hdegree⟩ := h
      cases ht
      constructor
      · exact (Finset.erase_subset _ _).trans hs.free_entered
      · intro m hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact hs.free_entered hfree
        · exact hs.move_entered m hm
      · intro m hm hmem
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact Finset.notMem_erase _ _ hmem
        · exact hs.move_not_free m hm (Finset.mem_of_mem_erase hmem)
      · intro m hm m' hm' heq
        rcases Finset.mem_insert.mp hm with rfl | hm
        · rcases Finset.mem_insert.mp hm' with rfl | hm'
          · rfl
          · exact False.elim (hs.move_not_free m' hm' (heq ▸ hfree))
        · rcases Finset.mem_insert.mp hm' with rfl | hm'
          · exact False.elim (hs.move_not_free m hm (heq.symm ▸ hfree))
          · exact hs.unique m hm m' hm' heq
      · intro m hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact hwitness
        · exact hs.witnessed m hm
      · intro m hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact Finset.Subset.refl _
        · exact hs.recorded m hm
      · intro m hm hkind
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact (hdegree hkind).trans (liveDegree_le_incidences s x)
        · exact hs.degree m hm hkind
    next => contradiction

def run {n : ℕ} (threshold : ℕ) (s : State n) : List (Action n) → Option (State n)
  | [] => some s
  | a :: rest => (step threshold s a).bind (fun t => run threshold t rest)

theorem run_valid {n : ℕ} {threshold : ℕ} (actions : List (Action n))
    {s t : State n} (hs : Valid threshold s) (ht : run threshold s actions = some t) :
    Valid threshold t := by
  induction actions generalizing s with
  | nil =>
    simp only [run, Option.some.injEq] at ht
    exact ht ▸ hs
  | cons a rest ih =>
    simp only [run] at ht
    cases hstep : step threshold s a with
    | none => simp [hstep] at ht
    | some u =>
      simp only [hstep, Option.bind_some] at ht
      exact ih (step_valid hs a hstep) ht

theorem charge_disjoint {n : ℕ} {threshold : ℕ} {s : State n} (hs : Valid threshold s) :
    (s.moves : Set (Move n)).Pairwise (fun m m' => Disjoint m.charges m'.charges) := by
  intro m hm m' hm' hne
  apply Finset.disjoint_left.mpr
  intro e he he'
  have h := ((mem_incidences _ _ _).mp (hs.recorded m hm he)).2
  have h' := ((mem_incidences _ _ _).mp (hs.recorded m' hm' he')).2
  exact hne (hs.unique m hm m' hm' (Option.some.inj (h.symm.trans h')))

/-- All saved incidences are distinct actual physical-call endpoints. -/
theorem charge_sum_le {n : ℕ} {threshold : ℕ} {s : State n} (hs : Valid threshold s) :
    (∑ m ∈ s.moves, m.charges.card) ≤ 2 * s.calls.length := by
  have hsum := Finset.card_biUnion (charge_disjoint hs)
  have hsubset : s.moves.biUnion Move.charges ⊆ endpointUniverse s.calls := by
    intro e he
    obtain ⟨m, hm, he⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_filter.mp (hs.recorded m hm he)).1
  have hcard := Finset.card_le_card hsubset
  rw [hsum] at hcard
  simpa [endpointUniverse, Nat.mul_comm] using hcard

/-- The global promotion count follows from the checked event history. -/
theorem promotions_le_twice_calls {n : ℕ} {threshold : ℕ} {s : State n}
    (hs : Valid threshold s) : s.moves.card ≤ 2 * s.calls.length := by
  calc
    s.moves.card = ∑ _m ∈ s.moves, 1 := by simp
    _ ≤ ∑ m ∈ s.moves, m.charges.card := Finset.sum_le_sum (fun m hm =>
      Nat.succ_le_of_lt (Finset.card_pos.mpr (hs.witnessed m hm)))
    _ ≤ _ := charge_sum_le hs

def degreeMoves {n : ℕ} (s : State n) : Finset (Move n) := s.moves.filter (fun m => m.kind = .degree)

/-- Every accepted degree selection pays its complete actual incident set;
the degree budget has no aggregate counting assumption. -/
theorem degree_moves_mul_le {n : ℕ} {threshold : ℕ} {s : State n}
    (hs : Valid threshold s) : threshold * (degreeMoves s).card ≤ 2 * s.calls.length := by
  calc
    threshold * (degreeMoves s).card = ∑ _m ∈ degreeMoves s, threshold := by simp [Nat.mul_comm]
    _ ≤ ∑ m ∈ degreeMoves s, m.charges.card := by
      apply Finset.sum_le_sum
      intro m hm
      obtain ⟨hm, hk⟩ := Finset.mem_filter.mp hm
      exact hs.degree m hm hk
    _ ≤ ∑ m ∈ s.moves, m.charges.card := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ ≤ _ := charge_sum_le hs

theorem degree_moves_le {n : ℕ} {threshold : ℕ} {s : State n}
    (hs : Valid threshold s) (hthreshold : 0 < threshold) :
    ((degreeMoves s).card : ℝ) ≤ 2 * s.calls.length / threshold := by
  have ht : (0 : ℝ) < threshold := by exact_mod_cast hthreshold
  apply (le_div_iff₀ ht).mpr
  exact_mod_cast (by simpa [Nat.mul_comm] using degree_moves_mul_le hs)

/-- One call verifies an arbitrary finite event trace and returns both global
incidence bounds. Physical call identities are their immutable list indices.
-/
theorem accepted_run_budgets {n : ℕ} (threshold : ℕ) (free : Finset (Location n))
    (actions : List (Action n)) (s : State n)
    (h : run threshold (initial free) actions = some s) :
    s.moves.card ≤ 2 * s.calls.length ∧
      threshold * (degreeMoves s).card ≤ 2 * s.calls.length := by
  have hv := run_valid actions (initial_valid threshold free) h
  exact ⟨promotions_le_twice_calls hv, degree_moves_mul_le hv⟩

def Action.physicalCost {n : ℕ} : Action n → ℕ
  | .physical _ => 1
  | _ => 0

def Action.promotionCost {n : ℕ} : Action n → ℕ
  | .promote _ _ => 1
  | _ => 0

def Action.degreeCost {n : ℕ} : Action n → ℕ
  | .promote _ .degree => 1
  | _ => 0

theorem step_counts {n : ℕ} {threshold : ℕ} {s t : State n}
    (hs : Valid threshold s) (a : Action n) (ht : step threshold s a = some t) :
    t.calls.length = s.calls.length + a.physicalCost ∧
      t.moves.card = s.moves.card + a.promotionCost ∧
      (degreeMoves t).card = (degreeMoves s).card + a.degreeCost := by
  cases a with
  | admit x =>
    simp only [step] at ht
    split at ht
    · cases ht
      simp [Action.physicalCost, Action.promotionCost, Action.degreeCost, degreeMoves]
    · contradiction
  | physical row =>
    simp only [step] at ht
    split at ht
    · cases ht
      simp [Action.physicalCost, Action.promotionCost, Action.degreeCost, degreeMoves]
    · contradiction
  | promote x kind =>
    simp only [step] at ht
    split at ht
    next h =>
      have hnew : (⟨x, kind, incidences s.calls x⟩ : Move n) ∉ s.moves :=
        fun hm => hs.move_not_free _ hm h.1
      have hnew' : (⟨x, kind, incidences s.calls x⟩ : Move n) ∉ degreeMoves s :=
        fun hm => hnew (Finset.mem_filter.mp hm).1
      cases ht
      cases kind <;>
        simp [Action.physicalCost, Action.promotionCost, Action.degreeCost,
          Finset.card_insert_of_notMem hnew, degreeMoves, Finset.filter_insert, hnew] at hnew' ⊢
    next => contradiction

/-- The stored cardinalities are exactly the numbers of accepted actions,
so the finite-set representation never hides repeated promotions. -/
theorem run_counts {n : ℕ} {threshold : ℕ} (actions : List (Action n))
    {s t : State n} (hs : Valid threshold s) (ht : run threshold s actions = some t) :
    t.calls.length = s.calls.length + (actions.map Action.physicalCost).sum ∧
      t.moves.card = s.moves.card + (actions.map Action.promotionCost).sum ∧
      (degreeMoves t).card = (degreeMoves s).card + (actions.map Action.degreeCost).sum := by
  induction actions generalizing s with
  | nil =>
    simp only [run, Option.some.injEq] at ht
    subst t
    simp
  | cons a rest ih =>
    simp only [run] at ht
    cases hstep : step threshold s a with
    | none => simp [hstep] at ht
    | some u =>
      simp only [hstep, Option.bind_some] at ht
      have hnext := ih (step_valid hs a hstep) ht
      have hfirst := step_counts hs a hstep
      simp only [List.map_cons, List.sum_cons]
      omega

/-- The chronological form of the two incidence budgets counts the actual
physical, promotion, and degree-selection actions in the input trace. -/
theorem accepted_action_budgets {n : ℕ} (threshold : ℕ) (free : Finset (Location n))
    (actions : List (Action n)) (s : State n)
    (h : run threshold (initial free) actions = some s) :
    (actions.map Action.promotionCost).sum ≤ 2 * (actions.map Action.physicalCost).sum ∧
      threshold * (actions.map Action.degreeCost).sum ≤ 2 * (actions.map Action.physicalCost).sum := by
  have hb := accepted_run_budgets threshold free actions s h
  have hc := run_counts actions (initial_valid threshold free) h
  simp only [initial, degreeMoves, Finset.filter_empty, Finset.card_empty,
    List.length_nil, zero_add] at hc
  simpa only [degreeMoves, hc.1, hc.2.1, hc.2.2] using hb

end SortingAdversary.Optimal.IncidenceLedger
