import SortingAdversary.Continuous.PolylogMemory
import SortingAdversary.Continuous.PolylogResources

/-!
# Representation across active comparisons

The memory interprets its own canonical block heap. The same refinement
counter bounds live allocations and the number of fractional digits
committed to the semantic memory.
-/

namespace SortingAdversary.Continuous.PolylogCompare

open PolylogBits PolylogResources
open Optimal.Parameters (logCap)

structure Aligned {n t b : ℕ} (D A : ℕ) (m : Memory n t b) (M : Controller.Memory n) : Prop where
  storage : ∃ nodes, m.Represents D nodes M
  grid : M.OnGrid (A + 2 * Controller.totalDepth M)
  sized : Sized A b (Controller.totalDepth M) m.spatial.directory m.heap

theorem initialize_aligned (n t b D A : ℕ) (hD : D < 2^b) :
    Aligned D A (initialMemory n t b D) (Controller.initial n) := by
  refine ⟨⟨[[]], initialize_represents n t b D hD⟩,
    (Controller.initial_onGrid n).mono (Nat.zero_le _), ?_⟩
  rw [Controller.totalDepth_initial]
  exact PolylogResources.initialized blockStore A b D t

end SortingAdversary.Continuous.PolylogCompare
