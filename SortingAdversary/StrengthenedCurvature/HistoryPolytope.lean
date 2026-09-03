import SortingAdversary.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# The history polytope and its concrete semantics

An enriched history retains every informative comparison as a strict linear
inequality. This file defines the resulting open polytope directly from an
ordinary comparison transcript and proves that every compatible ranking gives
an explicit feasible point. Thus the geometric state cannot represent an
inconsistent collection of answers.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

/-- A real coordinate for each labelled item. -/
abbrev Placement (n : ℕ) := Item n → ℝ

/-- All item coordinates lie strictly between the two ground boundaries. -/
def InUnitBox (x : Placement n) : Prop :=
  ∀ v, 0 < x v ∧ x v < 1

/-- The strict real inequality represented by an answered comparison. -/
def RealizesPlacement (o : Observation n) (x : Placement n) : Prop :=
  match o.answer with
  | .less => x o.query.left < x o.query.right
  | .greater => x o.query.right < x o.query.left

/-- The open history polytope associated with a full transcript. -/
def InHistoryPolytope (h : History n) (x : Placement n) : Prop :=
  InUnitBox x ∧ h.Forall (fun o => RealizesPlacement o x)

/-- Embed a concrete ranking into the unit interval with equally spaced
coordinates. -/
noncomputable def rankingPlacement (π : Ranking n) : Placement n :=
  fun v => (((π v : Fin n) : ℕ) + 1 : ℝ) / (n + 1)

private theorem rankingPlacement_pos (π : Ranking n) (v : Item n) :
    0 < rankingPlacement π v := by
  unfold rankingPlacement
  positivity

private theorem rankingPlacement_lt_one (π : Ranking n) (v : Item n) :
    rankingPlacement π v < 1 := by
  unfold rankingPlacement
  have hv : ((π v : Fin n) : ℕ) < n := (π v).isLt
  have hnum : ((π v : Fin n) : ℕ) + 1 < n + 1 :=
    Nat.add_lt_add_right hv 1
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  apply (div_lt_one hden).2
  exact_mod_cast hnum

private theorem rankingPlacement_lt_of_rank_lt
    (π : Ranking n) {u v : Item n} (huv : π u < π v) :
    rankingPlacement π u < rankingPlacement π v := by
  unfold rankingPlacement
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  apply (div_lt_div_iff_of_pos_right hden).2
  exact_mod_cast Nat.add_lt_add_right huv 1

/-- An observation true in a ranking is also true at its canonical placement. -/
theorem realizesPlacement_rankingPlacement
    (π : Ranking n) (o : Observation n) (ho : o.Holds π) :
    RealizesPlacement o (rankingPlacement π) := by
  cases hanswer : o.answer with
  | less =>
      simpa [RealizesPlacement, hanswer] using
        rankingPlacement_lt_of_rank_lt π
          (by simpa [Observation.Holds, hanswer] using ho)
  | greater =>
      simpa [RealizesPlacement, hanswer] using
        rankingPlacement_lt_of_rank_lt π
          (by simpa [Observation.Holds, hanswer] using ho)

/-- Every ranking compatible with a transcript supplies an explicit point of
the corresponding history polytope. -/
theorem rankingPlacement_mem
    (π : Ranking n) (h : History n) (hcompat : Compatible π h) :
    InHistoryPolytope h (rankingPlacement π) := by
  constructor
  · intro v
    exact ⟨rankingPlacement_pos π v, rankingPlacement_lt_one π v⟩
  · exact hcompat.imp (fun o ho => realizesPlacement_rankingPlacement π o ho)

/-- A compatible transcript has a nonempty history polytope. -/
theorem historyPolytope_nonempty
    (h : History n) (π : Ranking n) (hcompat : Compatible π h) :
    ∃ x : Placement n, InHistoryPolytope h x :=
  ⟨rankingPlacement π, rankingPlacement_mem π h hcompat⟩

end StrengthenedCurvature
end SortingAdversary
