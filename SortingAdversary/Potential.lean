import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith

/-!
# Exact potential accounting

The potential layer uses rational arithmetic.  Decimal approximations and
floating-point computations are intentionally absent from the trusted proof.
-/

namespace SortingAdversary

/-- An exact telescoping certificate for one adversarial execution. -/
structure PotentialCertificate where
  initial : ℚ
  terminal : ℚ
  increments : List ℚ
  maxIncrease : ℚ
  target : ℚ
  telescope : terminal = initial + increments.sum
  initial_nonpos : initial ≤ 0
  terminal_lower : target ≤ terminal
  each_increment : ∀ δ ∈ increments, δ ≤ maxIncrease

namespace PotentialCertificate

private theorem list_sum_le_length_mul :
    ∀ (xs : List ℚ) (M : ℚ), (∀ x ∈ xs, x ≤ M) →
      xs.sum ≤ (xs.length : ℚ) * M
  | [], M, _ => by simp
  | x :: xs, M, h => by
      have hx : x ≤ M := h x (by simp)
      have hxs : ∀ y ∈ xs, y ≤ M := by
        intro y hy
        exact h y (by simp [hy])
      have ih := list_sum_le_length_mul xs M hxs
      have hcast : ((x :: xs).length : ℚ) = (xs.length : ℚ) + 1 := by
        simp
      rw [List.sum_cons, hcast]
      nlinarith

/-- The sum of bounded per-comparison increases is bounded by the number of
comparisons times the maximum increase. -/
theorem sum_increments_le (cert : PotentialCertificate) :
    cert.increments.sum ≤ (cert.increments.length : ℚ) * cert.maxIncrease := by
  exact list_sum_le_length_mul cert.increments cert.maxIncrease cert.each_increment

/-- Generic telescoping potential bound. -/
theorem target_le_length_mul (cert : PotentialCertificate) :
    cert.target ≤ (cert.increments.length : ℚ) * cert.maxIncrease := by
  calc
    cert.target ≤ cert.terminal := cert.terminal_lower
    _ = cert.initial + cert.increments.sum := cert.telescope
    _ ≤ 0 + ((cert.increments.length : ℚ) * cert.maxIncrease) :=
      add_le_add cert.initial_nonpos cert.sum_increments_le
    _ = (cert.increments.length : ℚ) * cert.maxIncrease := zero_add _

/-- If the maximum increase is positive, the potential target yields an exact
lower bound on the number of comparisons. -/
theorem ratio_le_length (cert : PotentialCertificate) (hpositive : 0 < cert.maxIncrease) :
    cert.target / cert.maxIncrease ≤ (cert.increments.length : ℚ) := by
  apply (div_le_iff₀ hpositive).2
  simpa [mul_comm] using cert.target_le_length_mul

end PotentialCertificate
end SortingAdversary
