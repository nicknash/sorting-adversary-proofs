import SortingAdversary.AsymptoticStatement

/-!
# Independently inspectable challenge statement

This file is deliberately excluded from the trusted library root.  The `sorry`
below states the target to be replaced by the actual adversary-specific proof.
It must never be imported by `SortingAdversary.lean` or accepted by no-sorry CI.
-/

namespace SortingAdversary

/-- Target theorem: a deterministic adversary with clean leading constant 0.72. -/
theorem adversary_072 : Target072 := by
  sorry

end SortingAdversary
