import SortingAdversary.StrengthenedCurvature.HistoryPolytope
import SortingAdversary.StrengthenedCurvature.InformativeHistory
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

/-!
# Recovering a ranking from a strict history placement

The local determinant argument constructs a concrete point in one child
history polytope.  This file turns such a point back into an ordinary ranking,
so feasibility of the geometric answer is proved at the semantic boundary.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

private def PlacedItem (x : Placement n) := Item n

private instance (x : Placement n) : Fintype (PlacedItem x) :=
  inferInstanceAs (Fintype (Item n))

private instance (x : Placement n) : DecidableEq (PlacedItem x) :=
  inferInstanceAs (DecidableEq (Item n))

private def toPlacedItem (x : Placement n) : Item n ≃ PlacedItem x :=
  Equiv.refl _

/-- Pull back the lexicographic order on `(x i, i)` to the items.  The item
coordinate breaks ties without disturbing any strict inequality between
placement coordinates. -/
noncomputable def placementLinearOrder (x : Placement n) : LinearOrder (PlacedItem x) :=
  LinearOrder.lift' (fun i => toLex (x i, (i : Item n).val)) (by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun z => (ofLex z).2) hij)

/-- Rank every item by its position in the placement-induced linear order. -/
noncomputable def placementRanking (x : Placement n) : Ranking n := by
  letI : LinearOrder (PlacedItem x) := placementLinearOrder x
  exact (toPlacedItem x).trans
    (Fintype.orderIsoFinOfCardEq (PlacedItem x) (by
      change Fintype.card (Fin n) = n
      simp)).symm.toEquiv

theorem placementRanking_lt_of_lt (x : Placement n) {u v : Item n}
    (huv : x u < x v) : placementRanking x u < placementRanking x v := by
  letI : LinearOrder (PlacedItem x) := placementLinearOrder x
  let e := Fintype.orderIsoFinOfCardEq (PlacedItem x) (by
    change Fintype.card (Fin n) = n
    simp)
  have hlex : toLex (x u, u.val) < toLex (x v, v.val) :=
    Prod.Lex.left u.val v.val huv
  have hplaced : toPlacedItem x u < toPlacedItem x v := hlex
  have hrank : e.symm (toPlacedItem x u) < e.symm (toPlacedItem x v) :=
    e.symm.lt_iff_lt.mpr hplaced
  simpa [placementRanking, e] using hrank

/-- Every point of a strict history polytope induces a compatible concrete
ranking. -/
theorem compatible_placementRanking {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) : Compatible (placementRanking x) h := by
  rw [Compatible, List.forall_iff_forall_mem]
  intro o ho
  rw [holds_iff_lower_lt_upper]
  apply placementRanking_lt_of_lt x
  have hreal := (List.forall_iff_forall_mem.mp hx.2) o ho
  cases o with
  | mk q answer =>
      cases answer <;> simpa [RealizesPlacement, lower, upper] using hreal

/-- Geometric nonemptiness is enough for the adversary's semantic
feasibility predicate. -/
theorem feasible_of_mem_historyPolytope {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) : Feasible h :=
  ⟨placementRanking x, compatible_placementRanking hx⟩

end StrengthenedCurvature
end SortingAdversary
