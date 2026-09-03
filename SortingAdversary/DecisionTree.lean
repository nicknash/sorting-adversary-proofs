import SortingAdversary.Basic

/-!
# Deterministic comparison decision trees

The tree is intentionally finite and purely semantic.  No running-time model
for the sorting algorithm is built into the definition.
-/

namespace SortingAdversary

/-- A deterministic comparison tree.  Leaves claim a complete ranking. -/
inductive DecisionTree (n : ℕ) where
  | leaf (output : Ranking n)
  | compare (query : Query n) (onLess onGreater : DecisionTree n)

namespace DecisionTree

/-- The ranking output by a tree on a concrete input. -/
def evaluate : DecisionTree n → Ranking n → Ranking n
  | .leaf output, _ => output
  | .compare q onLess onGreater, π =>
      match q.outcome π with
      | .less => onLess.evaluate π
      | .greater => onGreater.evaluate π

/-- The number of comparisons made on a concrete input. -/
def cost : DecisionTree n → Ranking n → ℕ
  | .leaf _, _ => 0
  | .compare q onLess onGreater, π =>
      match q.outcome π with
      | .less => onLess.cost π + 1
      | .greater => onGreater.cost π + 1

/-- Extensional correctness for sorting: every hidden ranking is recovered. -/
def Correct (t : DecisionTree n) : Prop :=
  ∀ π : Ranking n, t.evaluate π = π

/-- A worst-case lower bound for one concrete decision tree. -/
def WorstCaseAtLeast (t : DecisionTree n) (k : ℕ) : Prop :=
  ∃ π : Ranking n, k ≤ t.cost π

end DecisionTree
end SortingAdversary
