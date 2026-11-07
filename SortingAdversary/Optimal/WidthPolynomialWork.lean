import SortingAdversary.Optimal.MeasuredWidthNormalize
import SortingAdversary.Optimal.UniformScalarWork

/-! A scalar-free polynomial envelope for the concrete width executor. -/

namespace SortingAdversary.Optimal.WidthPolynomialWork

open WidthRepair UniformStage

/-- `q` bounds the admitted stage's scalar fields. All powers in these
work bounds have fixed exponents. -/
def early (n palette q : ℕ) : ℕ :=
  RepairSelectWork.earlyBound n 2 +
    (CentralChoiceWork.workBound n 2 + 1 + (2 * q + 4) + (8 * q + 13) +
      MeasuredPin.workBound n palette 2 + 24) + 16

def vertices (n q : ℕ) : ℕ :=
  ScaleVerticesWork.pathBound n 2 + (4 * q + 12) + RepairSelectWork.widthBound n 2 +
    q * (ScaleVerticesWork.selectedBound n q (RepairSelectWork.widthBound n 2) + 2) + 3

def plan (n palette q : ℕ) : ℕ :=
  vertices n q + ScaleBlocksWork.workBound (palette + 1) q 2 2 (CentralChoiceWork.workBound n 2) + 8 * q + 4

def group (n palette q : ℕ) : ℕ :=
  plan n palette q + (3 * q + 1) +
    q * ((2 * q + 5 + MeasuredPin.workBound n palette 2 + 16) + 8) + 5

def kernel (n palette q : ℕ) : ℕ :=
  (n + n * n + 1) * early n palette q +
    (4 * q + 2 * q + 16 + RepairSelectWork.scaleBound n 2 + 2) +
    group n palette q + 4 * (n + n * n) + 32

def bound (n palette q : ℕ) : ℕ := (n + n * n + 1) * kernel n palette q

theorem early_le (p : WidthParameters) (n palette q : ℕ) (hB : p.B ≤ q) (hL : p.L ≤ q) :
    MeasuredEarlyNormalize.kernelBound n palette p ≤ early n palette q := by
  have hsize : Nat.size p.L ≤ q :=
    (Nat.size_le.mpr (show p.L < 2 ^ p.L from Nat.lt_two_pow_self)).trans hL
  unfold MeasuredEarlyNormalize.kernelBound MeasuredEarlyMove.workBound WidthScalarWork.cutBound early
  omega

theorem vertices_le (p : ScaleParameters) (n q : ℕ) (hH : p.H ≤ q) (hJ : p.J ≤ q) :
    ScaleVerticesWork.workBound n 2 p ≤ vertices n q := by
  unfold ScaleVerticesWork.workBound vertices ScaleVerticesWork.selectedBound
  gcongr

theorem plan_le (p : ScaleParameters) (n palette q : ℕ) (hH : p.H ≤ q) (hJ : p.J ≤ q) :
    MeasuredScalePlan.workBound n palette 2 p ≤ plan n palette q := by
  have hv := vertices_le p n q hH hJ
  have hs : ScaleBlocksWork.workBound (palette + 1) p.J 2 2 (CentralChoiceWork.workBound n 2) ≤
      ScaleBlocksWork.workBound (palette + 1) q 2 2 (CentralChoiceWork.workBound n 2) := by
    unfold ScaleBlocksWork.workBound ScaleBlocksWork.entryBound HubWork.groupPolynomial
    gcongr
  unfold MeasuredScalePlan.workBound plan
  omega

theorem group_le (p : ScaleParameters) (n palette q : ℕ)
    (hH : p.H ≤ q) (hJ : p.J ≤ q) (hB : p.width.B ≤ q) :
    MeasuredScaleGroup.workBound n palette p ≤ group n palette q := by
  have hp := plan_le p n palette q hH hJ
  have hm : p.J * (MeasuredScaleGroup.moveBound n palette p.width.B + 8) ≤
      q * ((2 * q + 5 + MeasuredPin.workBound n palette 2 + 16) + 8) := by
    unfold MeasuredScaleGroup.moveBound
    gcongr
  unfold MeasuredScaleGroup.workBound group
  omega

theorem kernel_le (p : ScaleParameters) (n palette q : ℕ)
    (hH : p.H ≤ q) (hJ : p.J ≤ q) (hB : p.width.B ≤ q) (hL : p.width.L ≤ q) :
    MeasuredWidthNormalize.kernelBound n palette p ≤ kernel n palette q := by
  have he := Nat.mul_le_mul_left (n + n * n + 1) (early_le p.width n palette q hB hL)
  have hg := group_le p n palette q hH hJ hB
  unfold MeasuredWidthNormalize.kernelBound MeasuredScaleDecision.workBound kernel
  omega

theorem admitted_bound {cap j : ℕ} (a : Accepted cap j) (n palette : ℕ) :
    MeasuredRepairBounds.WidthBound (MeasuredWidthNormalize.executor (n := n))
      a.runtime.normalizer.scale a.runtime.normalizer.d palette (bound n palette cap) := by
  intro s access cached g hB hsize
  have hw := MeasuredWidthNormalize.executor_bound a.runtime.normalizer.scale a.runtime.normalizer.d palette
    access cached g hB hsize
  exact hw.trans (Nat.mul_le_mul_left _ (kernel_le a.runtime.normalizer.scale n palette cap
    a.height_cap a.scale_cap a.comparable_cap (UniformScalarWork.edge_cap a)))

theorem bound_mono {n palette q q' : ℕ} (hq : q ≤ q') : bound n palette q ≤ bound n palette q' := by
  unfold bound kernel early group plan vertices ScaleVerticesWork.selectedBound
    ScaleBlocksWork.workBound ScaleBlocksWork.entryBound HubWork.groupPolynomial
  gcongr

end SortingAdversary.Optimal.WidthPolynomialWork
