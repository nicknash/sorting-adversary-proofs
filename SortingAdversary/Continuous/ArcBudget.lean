import SortingAdversary.Continuous.TreeRouting
import SortingAdversary.Optimal.GraphBalls

/-!
# Arc credits for the actual tree mutations

A recorded comparison inserts at most one generating arc. A refinement
deletes every arc incident to its moved item. Normalization changes no arcs.
These finite identities give the degree-repair budget for execution traces.
-/

namespace SortingAdversary.Continuous.ArcBudget

open FiniteAveraging TreeState

variable {n : ℕ} {K : Type*}

def arcs (D : System (Fin n) K) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e => D.edge e.1 e.2 = true)

def incident (D : System (Fin n) K) (x : Fin n) : Finset (Fin n × Fin n) :=
  (arcs D).filter (fun e => e.1 = x ∨ e.2 = x)

@[simp] theorem mem_arcs (D : System (Fin n) K) (e : Fin n × Fin n) :
    e ∈ arcs D ↔ D.edge e.1 e.2 = true := by simp [arcs]

@[simp] theorem mem_incident (D : System (Fin n) K) (x : Fin n) (e : Fin n × Fin n) :
    e ∈ incident D x ↔ D.edge e.1 e.2 = true ∧ (e.1 = x ∨ e.2 = x) := by
  simp [incident]

theorem neighbors_card_le_incident (D : System (Fin n) K) (x : Fin n) :
    (SortingAdversary.Optimal.GraphBalls.neighbors D.edge x).card ≤ (incident D x).card := by
  let f (y : Fin n) := if D.edge x y = true then (x, y) else (y, x)
  apply Finset.card_le_card_of_injOn f
  · intro y hy
    obtain ⟨hyx, he⟩ := (SortingAdversary.Optimal.GraphBalls.mem_neighbors D.edge x y).mp hy
    by_cases hxy : D.edge x y = true
    · simp [f, hxy]
    · have hyx' : D.edge y x = true := he.resolve_left hxy
      simp [f, hxy, hyx']
  · intro y hy z hz heq
    have hyx := ((SortingAdversary.Optimal.GraphBalls.mem_neighbors D.edge x y).mp hy).1
    have hzx := ((SortingAdversary.Optimal.GraphBalls.mem_neighbors D.edge x z).mp hz).1
    by_cases hxy : D.edge x y = true <;> by_cases hxz : D.edge x z = true
    · simpa [f, hxy, hxz] using congrArg Prod.snd heq
    · have hyx' : y = x := by simpa [f, hxy, hxz] using congrArg Prod.snd heq
      exact (hyx hyx').elim
    · have hzx' : x = z := by simpa [f, hxy, hxz] using congrArg Prod.snd heq
      exact (hzx hzx'.symm).elim
    · simpa [f, hxy, hxz] using congrArg Prod.fst heq

section OrderedField

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem normalize_edge (D : System (Fin n) K) (order : List (Fin n)) :
    (OrderRegion.normalize D order).edge = D.edge := by
  have hlo : ∀ (l : List (Fin n)) (D : System (Fin n) K),
      (l.foldl OrderRegion.propagateLower D).edge = D.edge := by
    intro l
    induction l with
    | nil => intro D; rfl
    | cons x l ih => intro D; exact ih (OrderRegion.propagateLower D x)
  have hhi : ∀ (l : List (Fin n)) (D : System (Fin n) K),
      (l.foldl OrderRegion.propagateUpper D).edge = D.edge := by
    intro l
    induction l with
    | nil => intro D; rfl
    | cons x l ih => intro D; exact ih (OrderRegion.propagateUpper D x)
  exact (hhi order.reverse _).trans (hlo order D)

@[simp] theorem arcs_normalize (D : System (Fin n) K) (order : List (Fin n)) :
    arcs (OrderRegion.normalize D order) = arcs D := by
  simp only [arcs, normalize_edge]

theorem arcs_reset (D : System (Fin n) K) (x : Fin n) (c : K) :
    arcs (resetCoordinate D x c) = (arcs D).filter (fun e => ¬(e.1 = x ∨ e.2 = x)) := by
  ext e
  by_cases he : e.1 = x ∨ e.2 = x <;> simp [resetCoordinate, he, and_comm]

/-- The deleted incident arcs are exactly the drop in the stored arc count. -/
theorem reset_arc_identity (D : System (Fin n) K) (x : Fin n) (c : K) :
    (arcs (resetCoordinate D x c)).card + (incident D x).card = (arcs D).card := by
  rw [arcs_reset, incident]
  have h := Finset.card_filter_add_card_filter_not (s := arcs D) (fun e => e.1 = x ∨ e.2 = x)
  omega

theorem reset_arc_le (D : System (Fin n) K) (x : Fin n) (c : K) :
    (arcs (resetCoordinate D x c)).card ≤ (arcs D).card := by
  have h := reset_arc_identity D x c
  omega

theorem arcs_addArc (D : System (Fin n) K) (x y : Fin n) :
    arcs (addArc D x y) = insert (x, y) (arcs D) := by
  ext e
  simp [addArc, Prod.ext_iff, or_comm]

theorem record_arc_le (s : State n K) (q : Query n) (a : Answer) :
    (arcs (record s q a).system).card ≤ (arcs s.system).card + 1 := by
  cases hr : route (s.location q.left) (s.location q.right) <;> cases a
  all_goals simp only [record, hr, recordSystem]
  · rw [arcs_addArc]; exact Finset.card_insert_le _ _
  · rw [arcs_addArc]; exact Finset.card_insert_le _ _
  all_goals change (arcs s.system).card ≤ (arcs s.system).card + 1; omega

@[simp] theorem initial_arcs (n : ℕ) : arcs (initial n : State n K).system = ∅ := by
  ext e
  simp [initial]

end OrderedField

end SortingAdversary.Continuous.ArcBudget
