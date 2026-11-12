import SortingAdversary.Continuous.LayerReduction
import SortingAdversary.Continuous.ControllerCorrect

/-!
# The actual adversary for supplied partial information

These public corollaries instantiate every local controller guarantee in
`LayerReduction` with the proved executable continuous controller. The
supplied ordered partition and its entropy-retention inequality remain
explicit inputs. Their construction is precisely the external weak-order
extension theorem cited by the manuscript.
-/

namespace SortingAdversary.Continuous.LayerAdversary

open LayerReduction
open scoped BigOperators

variable {n t : ℕ}

theorem run_legal (L : Layering n t) (k : ℕ) (hk : 64 ≤ k)
    (P : Item n → Item n → Prop) (hP : L.Extends P) (tree : DecisionTree n) :
    ∃ π : Ranking n, Compatible π (tree.run (L.strategy k) []).observations ∧ Respects P π :=
  LayerReduction.run_legal L k hk (fun m => Controller.compareGuarantee m k hk) P hP tree

theorem run_comparison_bound (L : Layering n t) (k : ℕ) (hk : 64 ≤ k)
    (P : Item n → Item n → Prop) (hP : L.Extends P)
    (tree : DecisionTree n) (hcorrect : CorrectFor tree P)
    (loss : ℝ) (hretained : log2 (extensionCount P : ℝ) - loss ≤
      ∑ i, log2 ((L.size i).factorial : ℝ)) :
    (log2 (extensionCount P : ℝ) - loss) / (1 + prefixOverhead k) ≤
      (tree.run (L.strategy k) []).comparisons :=
  LayerReduction.run_comparison_bound L k hk (fun m => Controller.compareGuarantee m k hk)
    P hP tree hcorrect loss hretained

theorem run_comparison_error (L : Layering n t) (k : ℕ) (hk : 64 ≤ k)
    (P : Item n → Item n → Prop) (hP : L.Extends P)
    (tree : DecisionTree n) (hcorrect : CorrectFor tree P)
    (loss : ℝ) (hloss : 0 ≤ loss) (hretained : log2 (extensionCount P : ℝ) - loss ≤
      ∑ i, log2 ((L.size i).factorial : ℝ)) :
    (1 - Controller.productionError k) * log2 (extensionCount P : ℝ) - loss ≤
      (tree.run (L.strategy k) []).comparisons :=
  LayerReduction.run_comparison_error L k hk (fun m => Controller.compareGuarantee m k hk)
    P hP tree hcorrect loss hloss hretained

/-- A genuine extension of the supplied relation realizes the lower bound
against every comparison tree correct on that relation. -/
theorem worst_case (L : Layering n t) (k : ℕ) (hk : 64 ≤ k)
    (P : Item n → Item n → Prop) (hP : L.Extends P)
    (tree : DecisionTree n) (hcorrect : CorrectFor tree P)
    (loss : ℝ) (hloss : 0 ≤ loss) (hretained : log2 (extensionCount P : ℝ) - loss ≤
      ∑ i, log2 ((L.size i).factorial : ℝ)) :
    ∃ π : Ranking n, Respects P π ∧
      (1 - Controller.productionError k) * log2 (extensionCount P : ℝ) - loss ≤ tree.cost π :=
  LayerReduction.worst_case L k hk (fun m => Controller.compareGuarantee m k hk)
    P hP tree hcorrect loss hloss hretained

end SortingAdversary.Continuous.LayerAdversary
