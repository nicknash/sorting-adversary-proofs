import SortingAdversary.Continuous.RefinementBatch
import SortingAdversary.Continuous.StateInvariants
import SortingAdversary.Continuous.Weights

/-!
# At most two refinements before answering a comparison

Every failed selection has positive logarithmic gain. After its coordinate
is reset, that coordinate is isolated with unit interval and density one.
Further refinements and normalization preserve this property. Consequently
no label can be selected twice in one unanswered comparison.
-/

namespace SortingAdversary.Continuous.TreeState

open FiniteAveraging OrderRegion

variable {n : ℕ}

/-- A concrete pre-answer refinement trace with the local gain promised by
failed selection. Positivity and the gain concern the actual order region. -/
inductive ProfitableRefinements : State n ℝ → List (Fin n × ℝ) → State n ℝ → Prop
  | nil (s : State n ℝ) : ProfitableRefinements s [] s
  | cons (s : State n ℝ) (x : Fin n) (c : ℝ) (order : List (Fin n))
      (moves : List (Fin n × ℝ)) (s' : State n ℝ)
      (hxx : s.system.edge x x = false)
      (hc : s.system.lower x < c ∧ c < s.system.upper x)
      (hV : 0 < nodeVolume s.system)
      (hgain : 0 < log2 (density s.system x c))
      (tail : ProfitableRefinements (normalize (refineAt s x c) order) moves s') :
      ProfitableRefinements s ((x, c) :: moves) s'

theorem ProfitableRefinements.toRefinementSteps {s s' : State n ℝ}
    {moves : List (Fin n × ℝ)} (h : ProfitableRefinements s moves s') :
    RefinementSteps s moves s' := by
  induction h with
  | nil s => exact .nil s
  | cons s x c order moves s' hxx hc hV hgain tail ih =>
      exact .cons s x c order moves s' hxx hc ih

theorem ProfitableRefinements.isolated_not_mem {s s' : State n ℝ}
    {moves : List (Fin n × ℝ)} (h : ProfitableRefinements s moves s')
    (x : Fin n) (hx : IsolatedUnit s.system x) : x ∉ moves.map Prod.fst := by
  induction h with
  | nil s => simp
  | cons s y c order moves s' hyy hc hV hgain tail ih =>
      have hxy : x ≠ y := by
        intro heq
        subst y
        have hc' : 0 < c ∧ c < 1 := by simpa [hx.1, hx.2.1] using hc
        rw [isolatedUnit_density s.system x hx hV c hc', log2_one] at hgain
        exact (lt_irrefl _ hgain)
      have hnext : IsolatedUnit (normalize (refineAt s y c) order).system x :=
        normalize_isolatedUnit _ x (resetCoordinate_preserves_isolatedUnit s.system x y c hx) order
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨hxy, ih hnext⟩

theorem ProfitableRefinements.labels_nodup {s s' : State n ℝ}
    {moves : List (Fin n × ℝ)} (h : ProfitableRefinements s moves s') :
    (moves.map Prod.fst).Nodup := by
  induction h with
  | nil s => simp
  | cons s x c order moves s' hxx hc hV hgain tail ih =>
      simp only [List.map_cons, List.nodup_cons]
      exact ⟨tail.isolated_not_mem x
        (normalize_isolatedUnit _ x (refineAt_isolatedUnit s x c) order), ih⟩

theorem ProfitableRefinements.length_le {s s' : State n ℝ}
    {moves : List (Fin n × ℝ)} (h : ProfitableRefinements s moves s')
    (Q : Finset (Fin n)) (hQ : ∀ m ∈ moves, m.1 ∈ Q) : moves.length ≤ Q.card := by
  have hs : (moves.map Prod.fst).toFinset ⊆ Q := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact hQ m hm
  have hh := Finset.card_le_card hs
  simpa only [List.toFinset_card_of_nodup h.labels_nodup, List.length_map] using hh

/-- This is the paper's bound of two failed selections per comparison. -/
theorem ProfitableRefinements.length_le_two {s s' : State n ℝ}
    {moves : List (Fin n × ℝ)} (h : ProfitableRefinements s moves s')
    (q : Query n) (hq : ∀ m ∈ moves, m.1 = q.left ∨ m.1 = q.right) :
    moves.length ≤ 2 := by
  have hh := h.length_le {q.left, q.right} (fun m hm => by simpa using hq m hm)
  exact hh.trans (by simp [q.distinct])

end SortingAdversary.Continuous.TreeState
