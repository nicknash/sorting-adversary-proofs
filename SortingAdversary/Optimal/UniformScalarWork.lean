import SortingAdversary.Optimal.UniformController
import SortingAdversary.Optimal.WidthScalarWork
import SortingAdversary.Optimal.StageRadiusWork

/-!
# Counted radii and integer bounds for admitted runtime parameters

The cached radius is computed from the actual accepted runtime fields.
No coherence of an arbitrary accepted record with an unevaluated stage
formula is assumed. For records constructed from the stage table the same
value is also the table-derived radius. The enormous powers are bounded by
the already proved admission and minimum-width certificates.
-/

namespace SortingAdversary.Optimal.UniformScalarWork

open PrimitiveWork WidthRepair UniformStage StageParameters

variable {cap j n : ℕ}

theorem base_le_ratio (p : ScaleParameters) : p.A ≤ p.R := by
  simpa only [pow_one, ScaleParameters.R] using
    (show p.A ^ 1 ≤ p.A ^ (p.J + 1) from Nat.pow_le_pow_right p.one_le_A (by omega))

theorem edge_le_base (p : ScaleParameters) : p.width.L ≤ p.A := by
  have hpow : p.width.L + 1 ≤ (p.width.L + 1) ^ (2 * p.H + 3) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos p.width.L)
      (show 1 ≤ 2 * p.H + 3 by omega)
  have hmul := Nat.le_mul_of_pos_left ((p.width.L + 1) ^ (2 * p.H + 3))
    (Nat.mul_pos (by decide : 0 < 128) p.J_pos)
  exact (Nat.le_succ p.width.L).trans (hpow.trans hmul)

theorem edge_cap (a : Accepted cap j) : a.runtime.normalizer.scale.width.L ≤ cap :=
  (edge_le_base a.runtime.normalizer.scale).trans ((base_le_ratio _).trans a.ratio_cap)

theorem base_cap (a : Accepted cap j) : a.runtime.normalizer.scale.A ≤ cap :=
  (base_le_ratio _).trans a.ratio_cap

theorem influence_cap (a : Accepted cap j) :
    LocalAccuracy.influenceSize a.runtime.normalizer.scale.H a.runtime.normalizer.d ≤ cap :=
  a.runtime.comparable_budget.trans a.comparable_cap

theorem four_cap (a : Accepted cap j) : 4 ^ a.runtime.normalizer.scale.width.B ≤ cap := by
  have hb := a.runtime.normalizer.scale.width.cutBudget
  have hL := edge_cap a
  omega

theorem cheap_cap (a : Accepted cap j) : a.runtime.cheap ≤ cap := by
  have h := a.cheap_square
  nlinarith

theorem cap_large (a : Accepted cap j) : 32 ≤ cap :=
  a.runtime.normalizer.scale.width.large.trans a.width_cap

theorem input_pos (a : Accepted (Parameters.logCap n) j) : 0 < n := by
  have h := cap_large a
  have hl := Nat.log_le_self 2 (n + 1)
  change 32 ≤ Nat.log 2 (n + 1) at h
  omega

theorem height_pos (a : Accepted cap j) : 0 < a.runtime.normalizer.scale.H := by
  have h := a.runtime.height_budget
  have hp := a.runtime.normalizer.path_two
  omega

theorem influence_pos (H d : ℕ) : 0 < LocalAccuracy.influenceSize H d := by
  unfold LocalAccuracy.influenceSize
  positivity

/-- A counted construction of the actual natural sweep-radius formula.
All input stage fields are already stored. -/
def radius (p : ScaleParameters) (d E : ℕ) : Result ℕ :=
  let influence := WidthScalarWork.power (d + 1) (p.H + 1)
  let clock := 8 * influence.value * influence.value
  let momentPower := WidthScalarWork.power clock p.H
  let insertionPower := WidthScalarWork.power 4 (2 * influence.value)
  let ratio := WidthScalarWork.ratio p
  let moment := 8 * influence.value * momentPower.value
  let insertion := 2 * insertionPower.value
  let sweeps := moment * (32 * ratio.value * E * insertion) + 8 * E
  ⟨p.H * sweeps, influence.work + momentPower.work + insertionPower.work + ratio.work + 18⟩

theorem radius_value (p : ScaleParameters) (d E : ℕ) (hE : 0 < E) :
    (radius p d E).value = p.H * LocalParameters.sweepCount p.H
      (LocalAccuracy.influenceSize p.H d) p.R (1 / (E : ℚ)) := by
  rw [StageScalars.sweeps_eq _ _ _ _ hE]
  simp only [radius, WidthScalarWork.power_value, WidthScalarWork.ratio_value,
    LocalAccuracy.influenceSize, StageScalars.sweeps, LocalParameters.momentOrder,
    LocalParameters.clockScale, LocalParameters.insertionConstant]
  congr 3
  ring

theorem radius_work (p : ScaleParameters) (d E : ℕ) :
    (radius p d E).work = 8 * p.H + 4 * LocalAccuracy.influenceSize p.H d + 2 * p.J + 39 := by
  simp only [radius, WidthScalarWork.power_work, WidthScalarWork.power_value, WidthScalarWork.ratio_work,
    LocalAccuracy.influenceSize]
  omega

theorem radius_work_le (a : Accepted cap j) (E : ℕ) :
    (radius a.runtime.normalizer.scale a.runtime.normalizer.d E).work ≤ 14 * cap + 39 := by
  rw [radius_work]
  have hH := a.height_cap
  have hJ := a.scale_cap
  have hM := influence_cap a
  omega

/-- The minimum-width recipe bounds the radius itself, not merely its
binary length. -/
theorem radius_le_width (p : ScaleParameters) (d E : ℕ) (hE : 0 < E)
    (minimum : LocalParameters.minimumWidth p.H (LocalAccuracy.influenceSize p.H d) p.R
      (1 / (E : ℚ)) ≤ p.width.W₀) : (radius p d E).value ≤ p.width.W₀ := by
  rw [radius_value p d E hE, StageScalars.sweeps_eq _ _ _ _ hE]
  rw [StageScalars.widthNeed_eq _ _ _ _ hE] at minimum
  let M := LocalAccuracy.influenceSize p.H d
  let sweeps := StageScalars.sweeps p.H M p.R E
  have hi := LocalParameters.insertionConstant_pos M
  have h0 := Nat.le_mul_of_pos_left (p.H * sweeps) (by decide : 0 < 32)
  have h1 := Nat.le_mul_of_pos_right (32 * (p.H * sweeps)) hE
  have h2 := Nat.le_mul_of_pos_right (32 * (p.H * sweeps) * E) hi
  change max (32 * p.H * sweeps * E * LocalParameters.insertionConstant M)
    (4 * LocalParameters.insertionConstant M * E) + 1 ≤ p.width.W₀ at minimum
  simp only [Nat.mul_assoc] at h0 h1 h2 minimum
  change p.H * sweeps ≤ p.width.W₀
  omega

def cdf (a : Accepted cap j) : Result ℕ := radius a.runtime.normalizer.scale a.runtime.normalizer.d 16

@[simp] theorem cdf_value (a : Accepted cap j) :
    (cdf a).value = a.runtime.normalizer.scale.H * LocalParameters.sweepCount a.runtime.normalizer.scale.H
      (LocalAccuracy.influenceSize a.runtime.normalizer.scale.H a.runtime.normalizer.d)
      a.runtime.normalizer.scale.R (1 / 16) := by
  simpa only [cdf, Nat.cast_ofNat] using radius_value a.runtime.normalizer.scale a.runtime.normalizer.d 16 (by decide)

theorem cdf_work (a : Accepted cap j) : (cdf a).work ≤ 14 * cap + 39 := radius_work_le a 16

theorem cdf_cap (a : Accepted cap j) : (cdf a).value ≤ cap :=
  (radius_le_width a.runtime.normalizer.scale a.runtime.normalizer.d 16 (by decide)
    a.runtime.normalizer.minimum).trans a.width_cap

def comparison (a : Accepted cap j) : Result ℕ :=
  let result := radius a.runtime.normalizer.scale a.runtime.normalizer.d (100 * j)
  ⟨result.value, result.work + 1⟩

theorem stage_pos (a : Accepted cap j) : 0 < j := by
  have h := a.runtime.error_pos
  rw [a.accuracy] at h
  by_contra hj
  have hz : j = 0 := by omega
  simp [hz] at h

@[simp] theorem comparison_value (a : Accepted cap j) :
    (comparison a).value = a.runtime.normalizer.scale.H * LocalParameters.sweepCount a.runtime.normalizer.scale.H
      (LocalAccuracy.influenceSize a.runtime.normalizer.scale.H a.runtime.normalizer.d)
      a.runtime.normalizer.scale.R a.runtime.ε := by
  have hE : 0 < 100 * j := Nat.mul_pos (by decide) (stage_pos a)
  simp only [comparison, radius_value _ _ _ hE, Nat.cast_mul, Nat.cast_ofNat, a.accuracy]

theorem comparison_work (a : Accepted cap j) : (comparison a).work ≤ 14 * cap + 40 := by
  have h := radius_work_le a (100 * j)
  change _ + 1 ≤ _
  omega

theorem comparison_cap (a : Accepted cap j) : (comparison a).value ≤ cap := by
  have hE : 0 < 100 * j := Nat.mul_pos (by decide) (stage_pos a)
  apply (radius_le_width a.runtime.normalizer.scale a.runtime.normalizer.d (100 * j) hE _).trans a.width_cap
  simpa only [Nat.cast_mul, Nat.cast_ofNat, a.accuracy] using a.runtime.comparison_minimum

theorem cdf_table_exact (cap j : ℕ) (hj : 0 < j) (hjcap : j ≤ cap) (table : StageRecipe.Table)
    (hv : ∀ f, table.get f = StageParameters.value j f) (hfit : StageRecipe.all.need j ≤ cap) :
    (cdf (compileTable cap j hj hjcap table hv hfit)).value = (StageRadiusWork.radii table).value.2 := by
  rw [cdf_value]
  exact (StageRadiusWork.cdf_exact j hj table hv).symm

end SortingAdversary.Optimal.UniformScalarWork
