import SortingAdversary.Optimal.UniformScalarWork
import SortingAdversary.Optimal.MeasuredScalePlan

/-!
# Actual scalar operands of the admitted repair routines

The large radius recipe is bounded before it is used. This module also
bounds every partial power produced by its counted loops, and the width
products and scale receipts formed from finite palette coordinates.
-/

namespace SortingAdversary.Optimal.UniformScalarWork

open PrimitiveWork WidthRepair UniformStage LocalParameters

variable {cap j n : ℕ}

theorem radius_intermediates (p : ScaleParameters) (d E : ℕ) (hH : 0 < p.H) (hE : 0 < E)
    (minimum : minimumWidth p.H (LocalAccuracy.influenceSize p.H d) p.R (1 / (E : ℚ)) ≤ p.width.W₀) :
    let M := LocalAccuracy.influenceSize p.H d
    clockScale M ^ p.H ≤ p.width.W₀ ∧
      4 ^ (2 * M) ≤ p.width.W₀ ∧
      momentOrder p.H M ≤ p.width.W₀ ∧
      insertionConstant M ≤ p.width.W₀ ∧
      StageScalars.sweeps p.H M p.R E ≤ p.width.W₀ := by
  let M := LocalAccuracy.influenceSize p.H d
  have hM := influence_pos p.H d
  have hR : 0 < p.R := p.one_le_R
  have hI := insertionConstant_pos M
  have hr := radius_le_width p d E hE minimum
  rw [radius_value p d E hE, StageScalars.sweeps_eq _ _ _ _ hE] at hr
  have hs := (Nat.le_mul_of_pos_left (StageScalars.sweeps p.H M p.R E) hH).trans hr
  have hm : momentOrder p.H M ≤ StageScalars.sweeps p.H M p.R E := by
    have hf : 0 < 32 * p.R * E * insertionConstant M := by positivity
    have hh := Nat.le_mul_of_pos_right (momentOrder p.H M) hf
    unfold StageScalars.sweeps
    omega
  have hp : clockScale M ^ p.H ≤ momentOrder p.H M :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) hM)
  have hw := minimum
  rw [StageScalars.widthNeed_eq _ _ _ _ hE] at hw
  change max _ (4 * insertionConstant M * E) + 1 ≤ p.width.W₀ at hw
  have hi0 := Nat.le_mul_of_pos_left (insertionConstant M) (by decide : 0 < 4)
  have hi1 := Nat.le_mul_of_pos_right (4 * insertionConstant M) hE
  have hi : insertionConstant M ≤ p.width.W₀ := by omega
  have hfour : 4 ^ (2 * M) ≤ insertionConstant M := Nat.le_mul_of_pos_left _ (by decide : 0 < 2)
  exact ⟨hp.trans (hm.trans hs), hfour.trans hi, hm.trans hs, hi, hs⟩

theorem cdf_intermediates (a : Accepted cap j) :
    let H := a.runtime.normalizer.scale.H
    let M := LocalAccuracy.influenceSize H a.runtime.normalizer.d
    clockScale M ^ H ≤ cap ∧ 4 ^ (2 * M) ≤ cap ∧
      momentOrder H M ≤ cap ∧ insertionConstant M ≤ cap ∧
      StageScalars.sweeps H M a.runtime.normalizer.scale.R 16 ≤ cap := by
  have h := radius_intermediates a.runtime.normalizer.scale a.runtime.normalizer.d 16
    (height_pos a) (by decide) a.runtime.normalizer.minimum
  exact ⟨h.1.trans a.width_cap, h.2.1.trans a.width_cap, h.2.2.1.trans a.width_cap,
    h.2.2.2.1.trans a.width_cap, h.2.2.2.2.trans a.width_cap⟩

theorem comparison_intermediates (a : Accepted cap j) :
    let H := a.runtime.normalizer.scale.H
    let M := LocalAccuracy.influenceSize H a.runtime.normalizer.d
    clockScale M ^ H ≤ cap ∧ 4 ^ (2 * M) ≤ cap ∧
      momentOrder H M ≤ cap ∧ insertionConstant M ≤ cap ∧
      StageScalars.sweeps H M a.runtime.normalizer.scale.R (100 * j) ≤ cap := by
  have hE : 0 < 100 * j := Nat.mul_pos (by decide) (stage_pos a)
  have hmin : minimumWidth a.runtime.normalizer.scale.H
      (LocalAccuracy.influenceSize a.runtime.normalizer.scale.H a.runtime.normalizer.d)
      a.runtime.normalizer.scale.R (1 / ((100 * j : ℕ) : ℚ)) ≤ a.runtime.normalizer.scale.width.W₀ := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, a.accuracy] using a.runtime.comparison_minimum
  have h := radius_intermediates a.runtime.normalizer.scale a.runtime.normalizer.d (100 * j)
    (height_pos a) hE hmin
  exact ⟨h.1.trans a.width_cap, h.2.1.trans a.width_cap, h.2.2.1.trans a.width_cap,
    h.2.2.2.1.trans a.width_cap, h.2.2.2.2.trans a.width_cap⟩

/-- Every value returned inside each power loop is bounded, not just the
last result. The exponents include all recursive prefixes. -/
theorem cdf_power_prefixes (a : Accepted cap j) :
    (∀ e ≤ a.runtime.normalizer.scale.H + 1,
      (WidthScalarWork.power (a.runtime.normalizer.d + 1) e).value ≤ cap) ∧
    (∀ e ≤ a.runtime.normalizer.scale.H,
      (WidthScalarWork.power (clockScale (LocalAccuracy.influenceSize a.runtime.normalizer.scale.H
        a.runtime.normalizer.d)) e).value ≤ cap) ∧
    (∀ e ≤ 2 * LocalAccuracy.influenceSize a.runtime.normalizer.scale.H a.runtime.normalizer.d,
      (WidthScalarWork.power 4 e).value ≤ cap) := by
  have h := cdf_intermediates a
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    exact (WidthScalarWork.power_value_le (Nat.succ_pos _) he).trans (influence_cap a)
  · intro e he
    exact (WidthScalarWork.power_value_le (clockScale_pos (influence_pos _ _)) he).trans h.1
  · intro e he
    exact (WidthScalarWork.power_value_le (by decide : 1 ≤ 4) he).trans h.2.1

theorem scalar_size_of_le {value : ℕ} (h : value ≤ cap) : Nat.size value ≤ Nat.size cap :=
  Nat.size_le_size h

theorem width_le_palette (s : State n) (v : Fin n) : s.width v ≤ s.pool.palette + 1 := by
  have h := (s.pool.system.effectiveUpper v).isLt
  unfold State.width CutNormalization.width
  omega

theorem width_products (a : Accepted cap j) (s : State n) (v : Fin n) :
    a.runtime.normalizer.scale.width.L * s.width v ≤ cap * (s.pool.palette + 1) ∧
      a.runtime.normalizer.scale.R * s.width v ≤ cap * (s.pool.palette + 1) :=
  ⟨Nat.mul_le_mul (edge_cap a) (width_le_palette s v),
    Nat.mul_le_mul a.ratio_cap (width_le_palette s v)⟩

theorem threshold_product (a : Accepted cap j) (s : State n) (v : Fin n) (i : ℕ)
    (hi : i ≤ a.runtime.normalizer.scale.J + 1) :
    (WidthScalarWork.power a.runtime.normalizer.scale.A i).value * s.width v ≤ cap * (s.pool.palette + 1) :=
  Nat.mul_le_mul ((WidthScalarWork.power_value_le a.runtime.normalizer.scale.one_le_A hi).trans a.ratio_cap)
    (width_le_palette s v)

theorem scale_receipt (a : Accepted cap j) {length palette : ℕ} (hl : length ≤ palette + 1) :
    2 * 4 ^ a.runtime.normalizer.scale.width.B * length ≤ 2 * cap * (palette + 1) :=
  Nat.mul_le_mul (Nat.mul_le_mul_left 2 (four_cap a)) hl

theorem cut_receipt_sizes (a : Accepted cap j) :
    Nat.size (WidthScalarWork.cut a.runtime.normalizer.scale.width).value.num.natAbs ≤ Nat.size cap ∧
      Nat.size (WidthScalarWork.cut a.runtime.normalizer.scale.width).value.den ≤ Nat.size cap := by
  let p := a.runtime.normalizer.scale.width
  have hp : p.L - 2 * 4 ^ p.B ≠ 0 := by have h := p.cutBudget; omega
  have hn := RationalWork.ratio_num_size p.L (p.L - 2 * 4 ^ p.B)
  have hd := RationalWork.ratio_den_size_of_ne_zero p.L (p.L - 2 * 4 ^ p.B) hp
  have hL := edge_cap a
  have hsub := Nat.sub_le p.L (2 * 4 ^ p.B)
  simp only [WidthScalarWork.cut, WidthScalarWork.power_value]
  exact ⟨hn.trans (Nat.size_le_size hL), hd.trans (Nat.size_le_size (hsub.trans hL))⟩

end SortingAdversary.Optimal.UniformScalarWork
