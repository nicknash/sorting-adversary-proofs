import SortingAdversary.StrengthenedCurvature.CountingRule

/-!
# Independently inspectable challenge statement

The original repository used this file to isolate the clean `18/25` target.
The majority-compatible-rankings adversary now proves the stronger leading
coefficient one, so the challenge is part of the trusted library root.
-/

namespace SortingAdversary

/-- Target theorem: a deterministic adversary with clean leading constant 0.72. -/
theorem adversary_072 : Target072 := by
  apply hasLeadingConstant_of_hasAdversaryLeadingConstant
  exact StrengthenedCurvature.hasAdversaryLeadingConstant_of_le_one (by norm_num)

end SortingAdversary
