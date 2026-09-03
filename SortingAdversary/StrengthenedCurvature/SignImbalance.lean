import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An entrywise proof of the sign-imbalance estimate

The source proves Lemma 5.1 with Hoffman--Wielandt.  For formalization it is
more economical to square the entries of the self-adjoint involution
`J = 2P-I`.  Those squares form a doubly stochastic matrix, and a weighted
Cauchy--Schwarz argument gives exactly the same factor `1/2`.  This avoids
adding a general eigenvalue-perturbation theorem to the trust surface.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Schur's `ℓ²` test for a nonnegative matrix whose row and column sums are
at most one. -/
theorem weighted_cross_le
    (a : ι → ℝ) (b : κ → ℝ) (w : ι → κ → ℝ)
    (hw : ∀ i j, 0 ≤ w i j)
    (hrow : ∀ i, ∑ j, w i j ≤ 1)
    (hcol : ∀ j, ∑ i, w i j ≤ 1) :
    ∑ i, ∑ j, a i * b j * w i j ≤
      Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ j, b j ^ 2) := by
  let c : ι → ℝ := fun i => ∑ j, b j * w i j
  have hc_sq (i : ι) : c i ^ 2 ≤ ∑ j, w i j * b j ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j : κ => Real.sqrt (w i j))
      (fun j : κ => Real.sqrt (w i j) * b j)
    have hsqrt (j : κ) : Real.sqrt (w i j) ^ 2 = w i j :=
      Real.sq_sqrt (hw i j)
    have hsqrt_mul (j : κ) : Real.sqrt (w i j) * Real.sqrt (w i j) = w i j := by
      simpa [pow_two] using hsqrt j
    have hrewritten :
        c i ^ 2 ≤ (∑ j, w i j) * ∑ j, w i j * b j ^ 2 := by
      simpa [c, hsqrt, hsqrt_mul, mul_pow, mul_assoc, mul_left_comm, mul_comm] using hcs
    have hsecond : 0 ≤ ∑ j, w i j * b j ^ 2 := by
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hw i j) (sq_nonneg _)
    exact hrewritten.trans
      (mul_le_of_le_one_left hsecond (hrow i))
  have hc_total : ∑ i, c i ^ 2 ≤ ∑ j, b j ^ 2 := by
    calc
      ∑ i, c i ^ 2 ≤ ∑ i, ∑ j, w i j * b j ^ 2 :=
        Finset.sum_le_sum fun i _ => hc_sq i
      _ = ∑ j, b j ^ 2 * ∑ i, w i j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ j, b j ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_of_le_one_right (sq_nonneg _) (hcol j)
  calc
    ∑ i, ∑ j, a i * b j * w i j = ∑ i, a i * c i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, c i ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a c
    _ ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ j, b j ^ 2) := by
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hc_total) (Real.sqrt_nonneg _)

/-- Positive part of a scalar. -/
def positivePart (x : ℝ) : ℝ := max x 0

/-- Magnitude of the negative part of a scalar. -/
def negativePart (x : ℝ) : ℝ := max (-x) 0

theorem positivePart_sub_negativePart (x : ℝ) :
    positivePart x - negativePart x = x := by
  rcases le_total x 0 with hx | hx
  · simp [positivePart, negativePart, hx]
  · simp [positivePart, negativePart, hx]

/-- The quadratic form of a doubly substochastic matrix cannot couple the
positive and negative `ℓ²` masses by more than twice their product. -/
theorem doublySubstochastic_quadratic_lower
    (d : ι → ℝ) (w : ι → ι → ℝ)
    (hw : ∀ i j, 0 ≤ w i j)
    (hrow : ∀ i, ∑ j, w i j ≤ 1)
    (hcol : ∀ j, ∑ i, w i j ≤ 1) :
    -2 * Real.sqrt (∑ i, positivePart (d i) ^ 2) *
          Real.sqrt (∑ i, negativePart (d i) ^ 2) ≤
      ∑ i, ∑ j, d i * d j * w i j := by
  let p : ι → ℝ := fun i => positivePart (d i)
  let n : ι → ℝ := fun i => negativePart (d i)
  let crossPN := ∑ i, ∑ j, p i * n j * w i j
  let crossNP := ∑ i, ∑ j, n i * p j * w i j
  let pp := ∑ i, ∑ j, p i * p j * w i j
  let nn := ∑ i, ∑ j, n i * n j * w i j
  have hp : ∀ i, 0 ≤ p i := fun i => by simp [p, positivePart]
  have hn : ∀ i, 0 ≤ n i := fun i => by simp [n, negativePart]
  have hpp : 0 ≤ pp := by
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hp i) (hp j)) (hw i j)
  have hnn : 0 ≤ nn := by
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hn i) (hn j)) (hw i j)
  have hpn : crossPN ≤
      Real.sqrt (∑ i, p i ^ 2) * Real.sqrt (∑ i, n i ^ 2) :=
    weighted_cross_le p n w hw hrow hcol
  have hnp : crossNP ≤
      Real.sqrt (∑ i, n i ^ 2) * Real.sqrt (∑ i, p i ^ 2) :=
    weighted_cross_le n p w hw hrow hcol
  have hexpand :
      (∑ i, ∑ j, d i * d j * w i j) = pp + nn - crossPN - crossNP := by
    have hpoint (i j : ι) :
        d i * d j * w i j =
          (p i * p j * w i j + n i * n j * w i j -
            p i * n j * w i j - n i * p j * w i j) := by
      have hdi : d i = p i - n i := by
        simpa only [p, n] using (positivePart_sub_negativePart (d i)).symm
      have hdj : d j = p j - n j := by
        simpa only [p, n] using (positivePart_sub_negativePart (d j)).symm
      rw [hdi, hdj]
      ring
    calc
      (∑ i, ∑ j, d i * d j * w i j) =
          ∑ i, ∑ j, (p i * p j * w i j + n i * n j * w i j -
            p i * n j * w i j - n i * p j * w i j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hpoint i j
      _ = pp + nn - crossPN - crossNP := by
        simp only [pp, nn, crossPN, crossNP, Finset.sum_add_distrib,
          Finset.sum_sub_distrib]
  rw [hexpand]
  simp only [p, n] at hpn hnp ⊢
  nlinarith [Real.sqrt_nonneg (∑ i, positivePart (d i) ^ 2),
    Real.sqrt_nonneg (∑ i, negativePart (d i) ^ 2)]

end StrengthenedCurvature
end SortingAdversary
