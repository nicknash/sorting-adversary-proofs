import SortingAdversary.Continuous.Controller
import SortingAdversary.Continuous.Dyadic

/-!
# Small exact regression examples

These examples reduce executable rational and finite-graph routines in the
kernel. They check multiplicities, strict separation, query orientation,
sequential updates, reduced dyadic anchors, and deterministic path choice.
No native-evaluation axiom is used.
-/

namespace SortingAdversary.Continuous.Examples

open FiniteAveraging Certificates TreeState

def forward : ComparisonIntervals := ((0, 0), (1, 1))
def backward : ComparisonIntervals := ((1, 1), (0, 0))

example : lowerFraction [forward, forward, backward] = (2 / 3 : ℚ) := by decide +kernel

example : selectAnswer 64 [forward, backward] = some .less := by decide +kernel

example : selectAnswer 64 [backward, backward, forward] = some .greater := by decide +kernel

example : separated ((0, 1 / 2), (1 / 2, 1)) = false := by decide +kernel

example : centralInterval [(0, 0), (0, 0), (1 / 2, 1 / 2), (1 / 2, 1 / 2),
    (1 / 2, 1 / 2), (1 / 2, 1 / 2), (1, 1), (1, 1)] = some (0, 1 / 2) := by
  have hs : ([0, 0, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 1, 1] : List ℚ).mergeSort (· ≤ ·) =
      [0, 0, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 1, 1] :=
    List.mergeSort_eq_self (· ≤ ·) (by norm_num)
  norm_num [centralInterval, centralCandidate, insideCount, hs]

example : centralInterval [(0, 0), (1 / 2, 1 / 2), (1, 1)] = none := by decide +kernel

example : roundUp (1 / 5, 2 / 5) = (1 / 4 : ℚ) := by decide +kernel

example : roundUp (middleHalf 0 1) = (1 / 2 : ℚ) := by decide +kernel

example : (DyadicAnchor.ofRat (3 / 8)).1 = 2 := by decide +kernel

example : (DyadicAnchor.ofRat (3 / 8)).coordinate = (3 / 8 : ℚ) := by decide +kernel

def chain : System (Fin 2) ℚ :=
  ⟨fun _ => 0, fun _ => 1, fun x y => decide (x = 0 ∧ y = 1)⟩

def twoUpdates : List (Fin 2 × Fin 4) := [(0, 2), (1, 2)]

example : fullSteps chain 4 twoUpdates chain.lower 1 = (1 / 2 : ℚ) := by decide +kernel

example : fullSteps chain 4 twoUpdates chain.upper 1 = (15 / 16 : ℚ) := by decide +kernel

example : route ([1 / 4] : List ℚ) [1 / 4, 3 / 4] = .leftFree (3 / 4) := by decide +kernel

example : route ([1 / 4, 3 / 4] : List ℚ) [1 / 4] = .rightFree (3 / 4) := by decide +kernel

def forkGraph (x y : Fin 3) : Bool := decide ((x = 0 ∨ x = 1) ∧ y = 2)

example : GraphPaths.firstPath forkGraph 2 = some [0, 2] := by decide +kernel

example : Controller.start 3 32 = .frozen id := rfl

end SortingAdversary.Continuous.Examples
