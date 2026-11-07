import SortingAdversary.Optimal.LocalParameters

/-!
# Natural-only evaluation of the local-oracle scalar recipe

At reciprocal integer accuracy, both rational ceilings are exact integers.
The stage scanner can therefore evaluate these formulas using only natural
addition, multiplication, maximum and exponentiation.
-/

namespace SortingAdversary.Optimal.StageScalars

open LocalParameters

def sweeps (H M R E : ℕ) : ℕ :=
  momentOrder H M * (32 * R * E * insertionConstant M) + 8 * E

def widthNeed (H M R E : ℕ) : ℕ :=
  max (32 * H * sweeps H M R E * E * insertionConstant M)
    (4 * insertionConstant M * E) + 1

theorem sweeps_eq (H M R E : ℕ) (hE : 0 < E) :
    sweepCount H M R (1 / (E : ℚ)) = sweeps H M R E := by
  have he : (E : ℚ) ≠ 0 := by exact_mod_cast hE.ne'
  have hc : (insertionConstant M : ℚ) ≠ 0 := by exact_mod_cast (insertionConstant_pos M).ne'
  have hfirst : 2 * (R : ℚ) / relativeTolerance M (1 / (E : ℚ)) =
      (32 * R * E * insertionConstant M : ℕ) := by
    unfold relativeTolerance
    push_cast
    field_simp
    <;> ring
  have hsecond : (8 : ℚ) / (1 / (E : ℚ)) = (8 * E : ℕ) := by
    push_cast
    field_simp
  simp only [sweepCount, hfirst, hsecond, Nat.ceil_natCast, sweeps]

theorem widthNeed_eq (H M R E : ℕ) (hE : 0 < E) :
    minimumWidth H M R (1 / (E : ℚ)) = widthNeed H M R E := by
  have he : (E : ℚ) ≠ 0 := by exact_mod_cast hE.ne'
  have hc : (insertionConstant M : ℚ) ≠ 0 := by exact_mod_cast (insertionConstant_pos M).ne'
  have hfirst : 2 * (H : ℚ) * sweepCount H M R (1 / (E : ℚ)) /
      relativeTolerance M (1 / (E : ℚ)) =
        (32 * H * sweeps H M R E * E * insertionConstant M : ℕ) := by
    rw [sweeps_eq H M R E hE]
    unfold relativeTolerance
    push_cast
    field_simp
    <;> ring
  have hsecond : 4 * (insertionConstant M : ℚ) / (1 / (E : ℚ)) =
      (4 * insertionConstant M * E : ℕ) := by
    push_cast
    field_simp
  simp only [minimumWidth, hfirst, hsecond, ← Nat.cast_max, Nat.ceil_natCast, widthNeed]

end SortingAdversary.Optimal.StageScalars
