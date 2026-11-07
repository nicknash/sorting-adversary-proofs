import SortingAdversary.Optimal.StageRecipe
import SortingAdversary.Optimal.PrimitiveWork

/-!
# Cached oracle radii from the actual capped stage table

The two sweep counts already belong to the fixed stage recipe. These
counted table reads and two multiplications obtain both radii without
evaluating the uncapped scalar formulas. Equality to those formulas is a
proof, and accepted table entries bound the actual computed products.
-/

namespace SortingAdversary.Optimal.StageRadiusWork

open PrimitiveWork StageParameters

def fieldGet (f : Field) : List (Field × ℕ) → Result ℕ
  | [] => ⟨0, 1⟩
  | (g, value) :: rest =>
    if f = g then ⟨value, 2⟩
    else let tail := fieldGet f rest; ⟨tail.value, tail.work + 2⟩

@[simp] theorem fieldGet_value (f : Field) (xs : List (Field × ℕ)) :
    (fieldGet f xs).value = (xs.lookup f).getD 0 := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨g, value⟩
    by_cases h : f = g
    · simp [fieldGet, h, List.lookup_cons, ih]
    · have hb : (f == g) = false := beq_eq_false_iff_ne.mpr h
      simp [fieldGet, h, List.lookup_cons, ih, hb]

theorem fieldGet_work (f : Field) (xs : List (Field × ℕ)) :
    (fieldGet f xs).work ≤ 2 * xs.length + 1 := by
  induction xs with
  | nil => exact le_rfl
  | cons p rest ih =>
    rcases p with ⟨g, value⟩
    simp only [fieldGet, List.length_cons]
    split_ifs <;> dsimp only <;> omega

def radii (table : StageRecipe.Table) : Result (ℕ × ℕ) :=
  let height := fieldGet .height table.values
  let comparison := fieldGet .comparisonSweeps table.values
  let cdf := fieldGet .cdfSweeps table.values
  ⟨(height.value * comparison.value, height.value * cdf.value),
    height.work + comparison.work + cdf.work + 4⟩

@[simp] theorem radii_value (table : StageRecipe.Table) :
    (radii table).value = (table.get .height * table.get .comparisonSweeps,
      table.get .height * table.get .cdfSweeps) := by
  simp only [radii, fieldGet_value, StageRecipe.Table.get]

theorem radii_work (table : StageRecipe.Table) : (radii table).work ≤ 6 * table.values.length + 7 := by
  have hh := fieldGet_work .height table.values
  have hc := fieldGet_work .comparisonSweeps table.values
  have hd := fieldGet_work .cdfSweeps table.values
  change _ + _ + _ + 4 ≤ _
  omega

def compute (cap j : ℕ) : Result (ℕ × ℕ) :=
  let table := StageRecipe.materialize cap j fields
  let answer := radii table
  ⟨answer.value, table.work + answer.work + 1⟩

theorem compute_value (cap j : ℕ) (hfit : StageRecipe.all.need j ≤ cap) :
    (compute cap j).value = (height j * comparisonSweeps j, height j * cdfSweeps j) := by
  simp only [compute, radii_value, StageRecipe.materialize_correct cap j hfit, value]

theorem compute_work (cap j : ℕ) (hcap : 1 ≤ cap) :
    (compute cap j).work ≤ fields.length * (StageRecipe.all.nodes * (5 * (cap + 1) + 2) + 1) +
      6 * fields.length + 8 := by
  have ht := StageRecipe.materialize_work cap j fields hcap
  have hr := radii_work (StageRecipe.materialize cap j fields)
  simp only [StageRecipe.materialize_values, List.length_map] at hr
  change _ + _ + 1 ≤ _
  omega

theorem compute_caps (cap j : ℕ) (hfit : StageRecipe.all.need j ≤ cap) :
    (compute cap j).value.1 ≤ cap * cap ∧ (compute cap j).value.2 ≤ cap * cap := by
  have hh := StageRecipe.evaluated_le cap j hfit .height
  have hc := StageRecipe.evaluated_le cap j hfit .comparisonSweeps
  have hd := StageRecipe.evaluated_le cap j hfit .cdfSweeps
  simp only [compute, radii_value, StageRecipe.materialize_get]
  exact ⟨Nat.mul_le_mul hh hc, Nat.mul_le_mul hh hd⟩

theorem comparison_exact (j : ℕ) (hj : 0 < j) (table : StageRecipe.Table)
    (hv : ∀ f, table.get f = value j f) :
    (radii table).value.1 =
      (fromValues j hj table.get hv).normalizer.scale.H * LocalParameters.sweepCount
        (fromValues j hj table.get hv).normalizer.scale.H
        (LocalAccuracy.influenceSize (fromValues j hj table.get hv).normalizer.scale.H
          (fromValues j hj table.get hv).normalizer.d)
        (fromValues j hj table.get hv).normalizer.scale.R (fromValues j hj table.get hv).ε := by
  simp only [radii_value, fromValues, hv, value, WidthRepair.ScaleParameters.R,
    WidthRepair.ScaleParameters.A, ScaleGeometry.scaleBase, LocalAccuracy.influenceSize]
  change height j * comparisonSweeps j = height j * LocalParameters.sweepCount
    (height j) (comparables j) (componentRatio j) (1 / (accuracyDen j : ℚ))
  rw [StageScalars.sweeps_eq _ _ _ _ (accuracyDen_pos hj)]
  rfl

theorem cdf_exact (j : ℕ) (hj : 0 < j) (table : StageRecipe.Table)
    (hv : ∀ f, table.get f = value j f) :
    (radii table).value.2 =
      (fromValues j hj table.get hv).normalizer.scale.H * LocalParameters.sweepCount
        (fromValues j hj table.get hv).normalizer.scale.H
        (LocalAccuracy.influenceSize (fromValues j hj table.get hv).normalizer.scale.H
          (fromValues j hj table.get hv).normalizer.d)
        (fromValues j hj table.get hv).normalizer.scale.R (1 / 16) := by
  simp only [radii_value, fromValues, hv, value, WidthRepair.ScaleParameters.R,
    WidthRepair.ScaleParameters.A, ScaleGeometry.scaleBase, LocalAccuracy.influenceSize]
  change height j * cdfSweeps j = height j * LocalParameters.sweepCount
    (height j) (comparables j) (componentRatio j) (1 / ((16 : ℕ) : ℚ))
  rw [StageScalars.sweeps_eq _ _ _ _ (by decide : 0 < 16)]
  rfl

end SortingAdversary.Optimal.StageRadiusWork
