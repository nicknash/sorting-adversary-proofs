import SortingAdversary.Basic
import SortingAdversary.Continuous.OrderRegion
import Mathlib.Data.List.Lex

/-!
# The continuous tree and refinement legality

The tree is stored by each item's finite path of child anchors.  Every item
has exactly one variable, at the end of its path.  Arcs join items at the same
path.  Consequently the global order region is the Cartesian product of the
node regions, with no extra coordinates for ancestors or unused labels.

A represented position is the lexicographically ordered list consisting of
the anchor path followed by the item's current coordinate.  This is exactly
the recursive insertion of child blocks described in the manuscript.

`refineAt` is the actual restriction followed by isolated admission: it clips
the neighbours' bounds, deletes the incident arcs, resets the moved variable
to `(0,1)`, and appends the anchor to its path.  Its consistency theorem does
not require refinement to preserve the set of represented orders.  Instead,
two feasible perturbations in the old parent bracket every new child position.
-/

namespace SortingAdversary.Continuous.TreeState

open FiniteAveraging OrderRegion

structure State (n : ℕ) (K : Type*) where
  system : System (Fin n) K
  location : Fin n → List K

section OrderedField

variable {n : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Read the order by recursively replacing each anchor with its child block. -/
def State.position (s : State n K) (X : Fin n → K) (x : Fin n) : List K :=
  s.location x ++ [X x]

def State.Holds (s : State n K) (X : Fin n → K) (o : Observation n) : Prop :=
  match o.answer with
  | .less => s.position X o.query.left < s.position X o.query.right
  | .greater => s.position X o.query.right < s.position X o.query.left

/-- Every feasible assignment satisfies every answer already given.  Ties
between unqueried items are allowed in this stronger geometric invariant. -/
def State.Consistent (s : State n K) (history : History n) : Prop :=
  ∀ X, s.system.StrictlyFeasible X → ∀ o ∈ history, s.Holds X o

def State.LocalArcs (s : State n K) : Prop :=
  ∀ x y, s.system.edge x y = true → s.location x = s.location y

def initial (n : ℕ) : State n K where
  system := ⟨fun _ => 0, fun _ => 1, fun _ _ => false⟩
  location := fun _ => []

theorem initial_consistent : (initial n : State n K).Consistent [] := by
  intro X hX o ho
  simp at ho

theorem initial_localArcs : (initial n : State n K).LocalArcs := by
  intro x y h
  simp [initial] at h

/-- Fix `x=c` in its old node and install its fresh unit coordinate. -/
def resetCoordinate (D : System (Fin n) K) (x : Fin n) (c : K) : System (Fin n) K where
  lower y := if y = x then 0 else
    if D.edge x y then max (D.lower y) c else D.lower y
  upper y := if y = x then 1 else
    if D.edge y x then min (D.upper y) c else D.upper y
  edge y z := if y = x ∨ z = x then false else D.edge y z

def refineAt (s : State n K) (x : Fin n) (c : K) : State n K where
  system := resetCoordinate s.system x c
  location := Function.update s.location x (s.location x ++ [c])

@[simp] theorem refineAt_location_self (s : State n K) (x : Fin n) (c : K) :
    (refineAt s x c).location x = s.location x ++ [c] := by
  simp [refineAt]

@[simp] theorem refineAt_location_other (s : State n K) (x y : Fin n) (c : K)
    (hy : y ≠ x) : (refineAt s x c).location y = s.location y := by
  simp [refineAt, Function.update_of_ne hy]

@[simp] theorem refineAt_isolated (s : State n K) (x y : Fin n) (c : K) :
    (refineAt s x c).system.edge x y = false ∧
      (refineAt s x c).system.edge y x = false := by
  simp [refineAt, resetCoordinate]

@[simp] theorem refineAt_unit (s : State n K) (x : Fin n) (c : K) :
    (refineAt s x c).system.lower x = 0 ∧
      (refineAt s x c).system.upper x = 1 := by
  simp [refineAt, resetCoordinate]

theorem refineAt_localArcs (s : State n K) (hs : s.LocalArcs)
    (x : Fin n) (c : K) : (refineAt s x c).LocalArcs := by
  intro a b hab
  have ha : a ≠ x := by
    intro h
    subst a
    simp [refineAt, resetCoordinate] at hab
  have hb : b ≠ x := by
    intro h
    subst b
    simp [refineAt, resetCoordinate] at hab
  have he : s.system.edge a b = true := by
    simpa [refineAt, resetCoordinate, ha, hb] using hab
  simpa [refineAt_location_other, ha, hb] using hs a b he

/-- The reset region is precisely the old coordinate section times a unit
interval, before the harmless endpoint-normalization passes. -/
theorem resetCoordinate_feasible_iff (D : System (Fin n) K) (x : Fin n) (c : K)
    (hxx : D.edge x x = false) (hc : D.lower x < c ∧ c < D.upper x)
    (Y : Fin n → K) :
    (resetCoordinate D x c).StrictlyFeasible Y ↔
      (0 < Y x ∧ Y x < 1) ∧ D.StrictlyFeasible (Function.update Y x c) := by
  constructor
  · intro h
    refine ⟨by simpa [resetCoordinate] using h.1 x, ?_⟩
    constructor
    · intro y
      by_cases hy : y = x
      · subst y
        simpa using hc
      · rw [Function.update_of_ne hy]
        have hl := (h.1 y).1
        have hu := (h.1 y).2
        simp only [resetCoordinate, if_neg hy] at hl hu
        constructor
        · split_ifs at hl with he
          · exact (le_max_left _ _).trans_lt hl
          · exact hl
        · split_ifs at hu with he
          · exact hu.trans_le (min_le_left _ _)
          · exact hu
    · intro a b hab
      by_cases ha : a = x
      · subst a
        have hb : b ≠ x := by intro hbx; subst b; simp [hxx] at hab
        rw [Function.update_self, Function.update_of_ne hb]
        have h := (h.1 b).1
        simp only [resetCoordinate, if_neg hb, hab, if_true] at h
        exact (le_max_right _ _).trans_lt h
      · by_cases hb : b = x
        · subst b
          rw [Function.update_self, Function.update_of_ne ha]
          have h := (h.1 a).2
          simp only [resetCoordinate, if_neg ha, hab, if_true] at h
          exact h.trans_le (min_le_right _ _)
        · rw [Function.update_of_ne ha, Function.update_of_ne hb]
          exact h.2 a b (by simp [resetCoordinate, ha, hb, hab])
  · rintro ⟨hy, h⟩
    constructor
    · intro y
      by_cases hxy : y = x
      · subst y
        simpa [resetCoordinate] using hy
      · have hbase := h.1 y
        simp only [Function.update_of_ne hxy] at hbase
        constructor
        · simp only [resetCoordinate, if_neg hxy]
          split_ifs with he
          · apply max_lt hbase.1
            simpa [Function.update_of_ne hxy] using h.2 x y he
          · exact hbase.1
        · simp only [resetCoordinate, if_neg hxy]
          split_ifs with he
          · apply lt_min hbase.2
            simpa [Function.update_of_ne hxy] using h.2 y x he
          · exact hbase.2
    · intro a b hab
      have ha : a ≠ x := by intro hax; subst a; simp [resetCoordinate] at hab
      have hb : b ≠ x := by intro hbx; subst b; simp [resetCoordinate] at hab
      have he : D.edge a b = true := by simpa [resetCoordinate, ha, hb] using hab
      simpa [Function.update_of_ne ha, Function.update_of_ne hb] using h.2 a b he

/-- Replacing one feasible value anywhere inside its actual conditional
interval preserves every strict inequality. -/
theorem replace_feasible (D : System (Fin n) K) (x : Fin n) (X : Fin n → K)
    (hX : D.StrictlyFeasible X) (t : K)
    (ht : conditionalLower D x X < t ∧ t < conditionalUpper D x X) :
    D.StrictlyFeasible (Function.update X x t) := by
  constructor
  · intro y
    by_cases hy : y = x
    · subst y
      simpa using And.intro ((lower_le_conditionalLower D x X).trans_lt ht.1)
        (ht.2.trans_le (conditionalUpper_le_upper D x X))
    · simpa [Function.update_of_ne hy] using hX.1 y
  · intro a b hab
    by_cases ha : a = x
    · subst a
      have hb : b ≠ x := by intro h; subst b; exact lt_irrefl _ (hX.2 x x hab)
      rw [Function.update_self, Function.update_of_ne hb]
      exact ht.2.trans_le (conditionalUpper_le_successor D x b X hab)
    · by_cases hb : b = x
      · subst b
        rw [Function.update_of_ne ha, Function.update_self]
        exact (predecessor_le_conditionalLower D x a X hab).trans_lt ht.1
      · simpa [Function.update_of_ne ha, Function.update_of_ne hb] using hX.2 a b hab

/-- Feasible values immediately on either side of a fixed interior coordinate
are obtained by bisecting its two conditional subintervals. -/
theorem feasible_bracketing (D : System (Fin n) K) (x : Fin n) (X : Fin n → K)
    (hX : D.StrictlyFeasible X) :
    ∃ a b, a < X x ∧ X x < b ∧
      D.StrictlyFeasible (Function.update X x a) ∧
      D.StrictlyFeasible (Function.update X x b) := by
  have hm := conditional_mem_strict D x hX
  let a := (conditionalLower D x X + X x) / 2
  let b := (X x + conditionalUpper D x X) / 2
  have ha : conditionalLower D x X < a ∧ a < X x := by
    dsimp [a]
    constructor <;> linarith
  have hb : X x < b ∧ b < conditionalUpper D x X := by
    dsimp [b]
    constructor <;> linarith
  exact ⟨a, b, ha.2, hb.1,
    replace_feasible D x X hX a ⟨ha.1, ha.2.trans hm.2⟩,
    replace_feasible D x X hX b ⟨hm.1.trans hb.1, hb.2⟩⟩

theorem child_position_between (p : List K) {a c b : K} (t : K)
    (ha : a < c) (hb : c < b) :
    p ++ [a] < p ++ [c, t] ∧ p ++ [c, t] < p ++ [b] := by
  exact ⟨(List.Lex.rel ha).append_left _ p, (List.Lex.rel hb).append_left _ p⟩

/-- Refinement into either a new or an existing child preserves all past
answers.  The proof uses the actual clipped constraints and actual tree order. -/
theorem refineAt_consistent (s : State n K) (history : History n)
    (hs : s.Consistent history) (x : Fin n) (c : K)
    (hxx : s.system.edge x x = false)
    (hc : s.system.lower x < c ∧ c < s.system.upper x) :
    (refineAt s x c).Consistent history := by
  intro Y hY o ho
  have hrest := ((resetCoordinate_feasible_iff s.system x c hxx hc Y).mp hY).2
  obtain ⟨a, b, ha, hb, hA, hB⟩ := feasible_bracketing s.system x
    (Function.update Y x c) hrest
  simp only [Function.update_self] at ha hb
  simp only [Function.update_idem] at hA hB
  have hleft := hs (Function.update Y x a) hA o ho
  have hright := hs (Function.update Y x b) hB o ho
  have hbetween := child_position_between (s.location x) (Y x) ha hb
  have hnew : (refineAt s x c).position Y x = s.location x ++ [c, Y x] := by
    simp [State.position, List.append_assoc]
  have hother : ∀ y, y ≠ x → (refineAt s x c).position Y y = s.position Y y := by
    intro y hy
    simp [State.position, refineAt_location_other, hy]
  have hold : ∀ y, y ≠ x → ∀ t, s.position (Function.update Y x t) y = s.position Y y := by
    intro y hy t
    simp [State.position, Function.update_of_ne hy]
  have hself : ∀ t, s.position (Function.update Y x t) x = s.location x ++ [t] := by
    intro t
    simp [State.position]
  have hpair : ∀ u v, u ≠ v →
      s.position (Function.update Y x a) u < s.position (Function.update Y x a) v →
      s.position (Function.update Y x b) u < s.position (Function.update Y x b) v →
      (refineAt s x c).position Y u < (refineAt s x c).position Y v := by
    intro u v huv hlow hhigh
    by_cases hu : u = x
    · subst u
      have hv : v ≠ x := Ne.symm huv
      rw [hnew, hother v hv]
      rw [hself b, hold v hv b] at hhigh
      exact hbetween.2.trans hhigh
    · by_cases hv : v = x
      · subst v
        rw [hother u hu, hnew]
        rw [hold u hu a, hself a] at hlow
        exact hlow.trans hbetween.1
      · simpa only [hother u hu, hother v hv, hold u hu a, hold v hv a] using hlow
  cases hanswer : o.answer with
  | less =>
      simp only [State.Holds, hanswer]
      apply hpair o.query.left o.query.right o.query.distinct
      · simpa [State.Holds, hanswer] using hleft
      · simpa [State.Holds, hanswer] using hright
  | greater =>
      simp only [State.Holds, hanswer]
      apply hpair o.query.right o.query.left (Ne.symm o.query.distinct)
      · simpa [State.Holds, hanswer] using hleft
      · simpa [State.Holds, hanswer] using hright

/-- Endpoint propagation also preserves the tree's transcript invariant. -/
def normalize (s : State n K) (order : List (Fin n)) : State n K :=
  { s with system := OrderRegion.normalize s.system order }

theorem normalize_consistent (s : State n K) (history : History n)
    (hs : s.Consistent history) (order : List (Fin n)) :
    (normalize s order).Consistent history := by
  intro X hX o ho
  exact hs X ((normalize_feasible_iff s.system order X).mp hX) o ho

end OrderedField

end SortingAdversary.Continuous.TreeState
