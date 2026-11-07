import SortingAdversary.Optimal.StageRecipe

/-!
# An actual bounded uniform stage constructor

The executed scan uses capped arithmetic throughout. When a stage is
accepted, its scalar table is materialized with the same capped evaluator,
and the controller package reads only those stored results. The enormous
uncapped formulas appear solely in equality and eventual-admission proofs.
-/

namespace SortingAdversary.Optimal.UniformStage

open StageParameters Parameters CappedArithmetic

def selectedStage (n : ℕ) : ℕ := CappedStageScan.stage StageRecipe.all n

theorem selectedStage_tendsto : Filter.Tendsto selectedStage Filter.atTop Filter.atTop :=
  CappedStageScan.stage_tendsto StageRecipe.all

theorem selectedStage_le (n : ℕ) : selectedStage n ≤ logCap n :=
  CappedStageScan.stage_le StageRecipe.all n

theorem selectedStage_fits (n : ℕ) (hj : 0 < selectedStage n) :
    StageRecipe.all.need (selectedStage n) ≤ logCap n :=
  CappedStageScan.stage_need StageRecipe.all n hj

theorem selected_field_le (n : ℕ) (hj : 0 < selectedStage n) (f : Field) :
    StageParameters.value (selectedStage n) f ≤ logCap n := by
  rw [← StageRecipe.field_value]
  exact ((StageRecipe.field f).value_le_need _).trans
    ((StageRecipe.field_need_le _ f).trans (selectedStage_fits n hj))

/-- The package produced on admission, tied to the actual degree, path,
scale, tolerance and oracle-work schedules. -/
structure Accepted (cap j : ℕ) where
  runtime : Runtime
  degree : runtime.normalizer.D = AsymptoticRates.stageDegree j
  path : runtime.normalizer.H = AsymptoticRates.stagePathLength j
  scale : runtime.normalizer.scale.J =
    AsymptoticRates.stageScaleLength j runtime.normalizer.scale.width.B
  accuracy : runtime.ε = 1 / (100 * (j : ℚ))
  cheap_square : runtime.cheap ^ 2 ≤ cap
  comparison_ball : runtime.comparisonBall ≤ cap
  cdf_ball : runtime.cdfBall ≤ cap
  stage_cap : j ≤ cap
  scale_cap : runtime.normalizer.scale.J ≤ cap
  width_cap : runtime.normalizer.scale.width.W₀ ≤ cap
  height_cap : runtime.normalizer.scale.H ≤ cap
  degree_cap : runtime.normalizer.d ≤ cap
  comparable_cap : runtime.normalizer.scale.width.B ≤ cap
  ratio_cap : runtime.normalizer.scale.R ≤ cap

def compileTable (cap j : ℕ) (hj : 0 < j) (hjcap : j ≤ cap) (table : StageRecipe.Table)
    (hvalues : ∀ f, table.get f = StageParameters.value j f)
    (hfit : StageRecipe.all.need j ≤ cap) : Accepted cap j where
  runtime := fromValues j hj table.get hvalues
  degree := fromValues_degree j hj table.get hvalues
  path := fromValues_path j hj table.get hvalues
  scale := fromValues_scale j hj table.get hvalues
  accuracy := by
    change 1 / (table.get .accuracyDen : ℚ) = _
    rw [hvalues .accuracyDen]
    simp only [value, accuracyDen, Nat.cast_mul, Nat.cast_ofNat]
  cheap_square := by
    change (table.get .cheap) ^ 2 ≤ cap
    rw [hvalues .cheap]
    have h := ((StageRecipe.field .cheapSquare).value_le_need j).trans
      ((StageRecipe.field_need_le j .cheapSquare).trans hfit)
    rw [StageRecipe.field_value] at h
    exact h
  comparison_ball := by
    change table.get .comparisonBall ≤ cap
    rw [hvalues .comparisonBall, ← StageRecipe.field_value]
    exact ((StageRecipe.field .comparisonBall).value_le_need j).trans
      ((StageRecipe.field_need_le j .comparisonBall).trans hfit)
  cdf_ball := by
    change table.get .cdfBall ≤ cap
    rw [hvalues .cdfBall, ← StageRecipe.field_value]
    exact ((StageRecipe.field .cdfBall).value_le_need j).trans
      ((StageRecipe.field_need_le j .cdfBall).trans hfit)
  stage_cap := hjcap
  scale_cap := by
    change table.get .scaleLength ≤ cap
    rw [hvalues .scaleLength, ← StageRecipe.field_value]
    exact ((StageRecipe.field .scaleLength).value_le_need j).trans
      ((StageRecipe.field_need_le j .scaleLength).trans hfit)
  width_cap := by
    change table.get .minimumWidth ≤ cap
    rw [hvalues .minimumWidth, ← StageRecipe.field_value]
    exact ((StageRecipe.field .minimumWidth).value_le_need j).trans
      ((StageRecipe.field_need_le j .minimumWidth).trans hfit)
  height_cap := by
    change table.get .height ≤ cap
    rw [hvalues .height, ← StageRecipe.field_value]
    exact ((StageRecipe.field .height).value_le_need j).trans
      ((StageRecipe.field_need_le j .height).trans hfit)
  degree_cap := by
    change table.get .degreeCap ≤ cap
    rw [hvalues .degreeCap, ← StageRecipe.field_value]
    exact ((StageRecipe.field .degreeCap).value_le_need j).trans
      ((StageRecipe.field_need_le j .degreeCap).trans hfit)
  comparable_cap := by
    change table.get .comparables ≤ cap
    rw [hvalues .comparables, ← StageRecipe.field_value]
    exact ((StageRecipe.field .comparables).value_le_need j).trans
      ((StageRecipe.field_need_le j .comparables).trans hfit)
  ratio_cap := by
    change (128 * table.get .scaleLength * (table.get .edgeRatio + 1) ^
      (2 * table.get .height + 3)) ^ (table.get .scaleLength + 1) ≤ cap
    rw [hvalues .scaleLength, hvalues .edgeRatio, hvalues .height]
    have h := ((StageRecipe.field .componentRatio).value_le_need j).trans
      ((StageRecipe.field_need_le j .componentRatio).trans hfit)
    rw [StageRecipe.field_value] at h
    exact h

inductive Decision (cap : ℕ) where
  | fallback
  | accepted (stage : ℕ) (positive : 0 < stage) (parameters : Accepted cap stage)

def Decision.stage {cap : ℕ} : Decision cap → ℕ
  | .fallback => 0
  | .accepted j _ _ => j

structure Selection (cap : ℕ) where
  decision : Decision cap
  arithmeticWork : ℕ
  arithmeticPeak : ℕ

/-- This is the complete executed selection procedure. The work counters
include the rejected attempts and the accepted stage's materialization. -/
def choose (n : ℕ) : Selection (logCap n) :=
  let scan := CappedStageScan.select StageRecipe.all n
  if hj : 0 < scan.stage then
    let table := StageRecipe.materialize (logCap n) scan.stage fields
    let hfit := selectedStage_fits n hj
    ⟨.accepted scan.stage hj
        (compileTable (logCap n) scan.stage hj (selectedStage_le n) table
          (StageRecipe.materialize_correct _ _ hfit) hfit),
      scan.work + table.work, max scan.peak table.peak⟩
  else ⟨.fallback, scan.work, scan.peak⟩

theorem choose_stage (n : ℕ) : (choose n).decision.stage = selectedStage n := by
  unfold choose
  dsimp only
  split
  · rfl
  · rename_i h
    change 0 = selectedStage n
    change ¬0 < selectedStage n at h
    omega

theorem choose_stage_tendsto :
    Filter.Tendsto (fun n => (choose n).decision.stage) Filter.atTop Filter.atTop := by
  simpa only [choose_stage] using selectedStage_tendsto

/-- A concrete, fixed syntax coefficient. This is independent of the
input and of the chosen stage; it can itself be evaluated directly. -/
def recipeSize : ℕ := StageRecipe.all.nodes

def arithmeticBudget (cap : ℕ) : ℕ :=
  (cap + fields.length) * (recipeSize * (5 * (cap + 1) + 2) + 1)

theorem choose_work (n : ℕ) : (choose n).arithmeticWork ≤ arithmeticBudget (logCap n) := by
  have hs := CappedStageScan.selected_work StageRecipe.all n
  unfold choose
  dsimp only
  split
  · rename_i hj
    have hcap : 1 ≤ logCap n := hj.trans_le (selectedStage_le n)
    have ht := StageRecipe.materialize_work (logCap n) (selectedStage n) fields hcap
    change (CappedStageScan.select StageRecipe.all n).work +
      (StageRecipe.materialize (logCap n) (selectedStage n) fields).work ≤ _
    unfold arithmeticBudget recipeSize
    nlinarith
  · change (CappedStageScan.select StageRecipe.all n).work ≤ _
    apply hs.trans
    unfold arithmeticBudget recipeSize
    exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

theorem choose_peak (n : ℕ) : (choose n).arithmeticPeak ≤ (logCap n + 129) ^ 2 := by
  have hs := CappedStageScan.selected_peak StageRecipe.all n 128 StageRecipe.all_literalMax
  unfold choose
  dsimp only
  split
  · rename_i hj
    have hcap : 1 ≤ logCap n := hj.trans_le (selectedStage_le n)
    have ht := StageRecipe.materialize_peak (logCap n) (selectedStage n) fields hcap (selectedStage_le n)
    exact max_le hs ht
  · exact hs

theorem choose_integer_bits (n : ℕ) :
    Nat.size (choose n).arithmeticPeak ≤ Nat.size ((logCap n + 129) ^ 2) :=
  Nat.size_le_size (choose_peak n)

/-- A coarse polynomial bound, with a fixed coefficient for this concrete
stage constructor. It holds even when every positive stage is rejected. -/
theorem choose_work_polynomial (n : ℕ) :
    (choose n).arithmeticWork ≤ (n + 22) * (recipeSize * (5 * (n + 1) + 2) + 1) := by
  apply (choose_work n).trans
  unfold arithmeticBudget
  have hlen : fields.length = 22 := rfl
  rw [hlen]
  apply Nat.mul_le_mul (Nat.add_le_add_right (logCap_le_input n) 22)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _
    (Nat.add_le_add_right (Nat.mul_le_mul_left 5 (Nat.add_le_add_right (logCap_le_input n) 1)) 2)) 1

/-- The evaluated arithmetic admits the usual quadratic-cost bit-operation
envelope: operation count times the square of the maximum operand bit size.
The statement records that model explicitly rather than assuming unit-cost
arithmetic for unbounded natural numbers. -/
def bitEnvelope (n : ℕ) : ℕ :=
  (choose n).arithmeticWork * (Nat.size (choose n).arithmeticPeak + 1) ^ 2

theorem bitEnvelope_bound (n : ℕ) :
    bitEnvelope n ≤ arithmeticBudget (logCap n) * (Nat.size ((logCap n + 129) ^ 2) + 1) ^ 2 := by
  apply Nat.mul_le_mul (choose_work n)
  exact Nat.pow_le_pow_left (Nat.add_le_add_right (choose_integer_bits n) 1) 2

/-- The cheap-price cap is part of the actual successful recipe, so the
uniform vanishing estimate is now instantiated by this concrete scan. -/
theorem cheap_ratio_tendsto : Filter.Tendsto
    (fun n => (StageParameters.cheap (selectedStage n) : ℝ) / Real.log n)
    Filter.atTop (nhds 0) := by
  apply AsymptoticRates.cheap_log_ratio_tendsto
  · exact Filter.Eventually.of_forall (fun n => Nat.cast_nonneg _)
  · filter_upwards [selectedStage_tendsto.eventually (Filter.eventually_gt_atTop 0)] with n hn
    exact_mod_cast selected_field_le n hn .cheapSquare

end SortingAdversary.Optimal.UniformStage
