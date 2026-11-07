import SortingAdversary.Optimal.UniformStage
import SortingAdversary.Optimal.StageRadiusWork
import SortingAdversary.Optimal.RationalWork

/-!
# Measured compilation of the accepted scalar table

The capped evaluator already counts construction of the scalar table. This
module pays for its twelve actual field searches and the rational accuracy
normalization. The reference compiler is used only in erased certificates;
the runtime record is assembled from the measured scalar results.
-/

namespace SortingAdversary.Optimal.StageCompileWork

open PrimitiveWork StageParameters UniformStage WidthRepair

def normalizer (reference : StructuralNormalize.Parameters)
    (W B L H J d D ordinaryH : ℕ)
    (hW : W = reference.scale.width.W₀) (hB : B = reference.scale.width.B)
    (hL : L = reference.scale.width.L) (hH : H = reference.scale.H)
    (hJ : J = reference.scale.J) (hd : d = reference.d)
    (hD : D = reference.D) (hO : ordinaryH = reference.H) : StructuralNormalize.Parameters where
  scale := {
    width := { W₀ := W, B := B, L := L
               large := by rw [hW]; exact reference.scale.width.large
               cutBudget := by rw [hB, hL]; exact reference.scale.width.cutBudget }
    H := H
    J := J
    group := by rw [hJ]; exact reference.scale.group }
  d := d
  D := D
  H := ordinaryH
  degree_pos := by rw [hD]; exact reference.degree_pos
  path_two := by rw [hO]; exact reference.path_two
  minimum := by
    simpa only [hW, hB, hL, hH, hJ, hd, ScaleParameters.R, ScaleParameters.A, ScaleGeometry.scaleBase]
      using reference.minimum

theorem normalizer_eq (reference : StructuralNormalize.Parameters)
    (W B L H J d D ordinaryH : ℕ)
    (hW : W = reference.scale.width.W₀) (hB : B = reference.scale.width.B)
    (hL : L = reference.scale.width.L) (hH : H = reference.scale.H)
    (hJ : J = reference.scale.J) (hd : d = reference.d)
    (hD : D = reference.D) (hO : ordinaryH = reference.H) :
    normalizer reference W B L H J d D ordinaryH hW hB hL hH hJ hd hD hO = reference := by
  subst W B L H J d D ordinaryH
  rfl

def runtime (reference : Runtime) (normal : StructuralNormalize.Parameters)
    (hn : normal = reference.normalizer) (error : ℚ) (he : error = reference.ε)
    (cheap comparisonBall cdfBall : ℕ)
    (hc : cheap = reference.cheap) (hcmp : comparisonBall = reference.comparisonBall)
    (hcdf : cdfBall = reference.cdfBall) : Runtime where
  normalizer := normal
  ε := error
  error_pos := by rw [he]; exact reference.error_pos
  error_small := by rw [he]; exact reference.error_small
  height_budget := by rw [hn]; exact reference.height_budget
  degree_budget := by rw [hn]; exact reference.degree_budget
  comparable_budget := by rw [hn]; exact reference.comparable_budget
  comparison_minimum := by rw [hn, he]; exact reference.comparison_minimum
  cheap := cheap
  cheap_eq := by rw [hn, hc]; exact reference.cheap_eq
  comparisonBall := comparisonBall
  comparisonBall_eq := by rw [hn, he, hcmp]; exact reference.comparisonBall_eq
  cdfBall := cdfBall
  cdfBall_eq := by rw [hn, hcdf]; exact reference.cdfBall_eq

theorem runtime_eq (reference : Runtime) (normal : StructuralNormalize.Parameters)
    (hn : normal = reference.normalizer) (error : ℚ) (he : error = reference.ε)
    (cheap comparisonBall cdfBall : ℕ)
    (hc : cheap = reference.cheap) (hcmp : comparisonBall = reference.comparisonBall)
    (hcdf : cdfBall = reference.cdfBall) :
    runtime reference normal hn error he cheap comparisonBall cdfBall hc hcmp hcdf = reference := by
  subst normal error cheap comparisonBall cdfBall
  rfl

def accepted {cap j : ℕ} (reference : Accepted cap j) (r : Runtime) (hr : r = reference.runtime) :
    Accepted cap j where
  runtime := r
  degree := by rw [hr]; exact reference.degree
  path := by rw [hr]; exact reference.path
  scale := by rw [hr]; exact reference.scale
  accuracy := by rw [hr]; exact reference.accuracy
  cut_error := by rw [hr]; exact reference.cut_error
  cheap_square := by rw [hr]; exact reference.cheap_square
  comparison_ball := by rw [hr]; exact reference.comparison_ball
  cdf_ball := by rw [hr]; exact reference.cdf_ball
  stage_cap := reference.stage_cap
  scale_cap := by rw [hr]; exact reference.scale_cap
  width_cap := by rw [hr]; exact reference.width_cap
  height_cap := by rw [hr]; exact reference.height_cap
  degree_cap := by rw [hr]; exact reference.degree_cap
  comparable_cap := by rw [hr]; exact reference.comparable_cap
  ratio_cap := by rw [hr]; exact reference.ratio_cap

theorem accepted_eq {cap j : ℕ} (reference : Accepted cap j) (r : Runtime) (hr : r = reference.runtime) :
    accepted reference r hr = reference := by subst r; rfl

structure Output {cap j : ℕ} (reference : Accepted cap j) where
  value : Accepted cap j
  actual : value = reference

def compile (cap j : ℕ) (hj : 0 < j) (hjcap : j ≤ cap) (table : StageRecipe.Table)
    (hvalues : ∀ f, table.get f = StageParameters.value j f)
    (hfit : StageRecipe.all.need j ≤ cap) : Result (Output (compileTable cap j hj hjcap table hvalues hfit)) := by
  let reference := compileTable cap j hj hjcap table hvalues hfit
  let W := StageRadiusWork.fieldGet .minimumWidth table.values
  let B := StageRadiusWork.fieldGet .comparables table.values
  let L := StageRadiusWork.fieldGet .edgeRatio table.values
  let H := StageRadiusWork.fieldGet .height table.values
  let J := StageRadiusWork.fieldGet .scaleLength table.values
  let d := StageRadiusWork.fieldGet .degreeCap table.values
  let D := StageRadiusWork.fieldGet .degree table.values
  let ordinaryH := StageRadiusWork.fieldGet .pathLength table.values
  let denominator := StageRadiusWork.fieldGet .accuracyDen table.values
  let error := RationalWork.ratio 1 denominator.value
  let cheap := StageRadiusWork.fieldGet .cheap table.values
  let comparison := StageRadiusWork.fieldGet .comparisonBall table.values
  let cdf := StageRadiusWork.fieldGet .cdfBall table.values
  have fields (f : Field) : (StageRadiusWork.fieldGet f table.values).value = table.get f :=
    StageRadiusWork.fieldGet_value f table.values
  let normal := normalizer reference.runtime.normalizer W.value B.value L.value H.value J.value
    d.value D.value ordinaryH.value (fields _) (fields _) (fields _) (fields _) (fields _)
    (fields _) (fields _) (fields _)
  have hn : normal = reference.runtime.normalizer := normalizer_eq ..
  have he : error.value = reference.runtime.ε := by
    change (RationalWork.ratio 1 denominator.value).value = 1 / (table.get .accuracyDen : ℚ)
    simp only [RationalWork.ratio_value, Nat.cast_one, denominator, fields]
  let r := runtime reference.runtime normal hn error.value he cheap.value comparison.value cdf.value
    (fields _) (fields _) (fields _)
  have hr : r = reference.runtime := runtime_eq ..
  exact ⟨⟨accepted reference r hr, accepted_eq reference r hr⟩,
    W.work + B.work + L.work + H.work + J.work + d.work + D.work + ordinaryH.work +
      denominator.work + error.work + cheap.work + comparison.work + cdf.work + 20⟩

theorem compile_work (cap j : ℕ) (hj : 0 < j) (hjcap : j ≤ cap) (table : StageRecipe.Table)
    (hvalues : ∀ f, table.get f = StageParameters.value j f)
    (hfit : StageRecipe.all.need j ≤ cap) :
    (compile cap j hj hjcap table hvalues hfit).work ≤ 24 * table.values.length + 3 * cap + 45 := by
  have hf (f : Field) := StageRadiusWork.fieldGet_work f table.values
  have hden : (StageRadiusWork.fieldGet .accuracyDen table.values).value ≤ cap := by
    rw [StageRadiusWork.fieldGet_value]
    change table.get .accuracyDen ≤ cap
    rw [hvalues .accuracyDen, ← StageRecipe.field_value]
    exact ((StageRecipe.field .accuracyDen).value_le_need j).trans
      ((StageRecipe.field_need_le j .accuracyDen).trans hfit)
  have hsize : Nat.size (StageRadiusWork.fieldGet .accuracyDen table.values).value ≤ cap :=
    (Nat.size_le.mpr (show (StageRadiusWork.fieldGet .accuracyDen table.values).value <
      2 ^ (StageRadiusWork.fieldGet .accuracyDen table.values).value from Nat.lt_two_pow_self)).trans hden
  have he := RationalWork.ratio_work_le 1 (StageRadiusWork.fieldGet .accuracyDen table.values).value
  have hs : Nat.size 1 = 1 := by decide
  rw [hs] at he
  have hW := hf .minimumWidth
  have hB := hf .comparables
  have hL := hf .edgeRatio
  have hH := hf .height
  have hJ := hf .scaleLength
  have hd := hf .degreeCap
  have hD := hf .degree
  have hO := hf .pathLength
  have hdenWork := hf .accuracyDen
  have hc := hf .cheap
  have hcmp := hf .comparisonBall
  have hcdf := hf .cdfBall
  dsimp only [compile]
  omega

end SortingAdversary.Optimal.StageCompileWork
