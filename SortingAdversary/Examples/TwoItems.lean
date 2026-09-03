import SortingAdversary.DecisionTree

/-!
# A tiny semantic sanity check

The result is intentionally elementary: a correct comparison tree for two
items must make at least one comparison on some input.  Its purpose is to test
that `Ranking`, `Correct`, `cost`, and `WorstCaseAtLeast` have the expected
meaning independently of any sophisticated adversary representation.
-/

namespace SortingAdversary
namespace Examples

private def identityRankingTwo : Ranking 2 := Equiv.refl (Fin 2)
private def swappedRankingTwo : Ranking 2 := Equiv.swap 0 1

private theorem identity_ne_swapped : identityRankingTwo ≠ swappedRankingTwo := by
  intro h
  have h0 := congrArg (fun π : Ranking 2 => π 0) h
  simpa [identityRankingTwo, swappedRankingTwo] using h0

/-- Every correct deterministic comparison tree on two labelled items has an
input on which it performs at least one comparison. -/
theorem two_items_need_one_comparison (t : DecisionTree 2) (ht : t.Correct) :
    t.WorstCaseAtLeast 1 := by
  cases t with
  | leaf output =>
      have hid : output = identityRankingTwo := ht identityRankingTwo
      have hswap : output = swappedRankingTwo := ht swappedRankingTwo
      exact (identity_ne_swapped (hid.symm.trans hswap)).elim
  | compare q onLess onGreater =>
      refine ⟨identityRankingTwo, ?_⟩
      cases hanswer : q.outcome identityRankingTwo <;>
        simp [DecisionTree.cost, hanswer]

#print axioms two_items_need_one_comparison

end Examples
end SortingAdversary
