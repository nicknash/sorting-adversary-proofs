import SortingAdversary.Continuous.Density
import Mathlib.MeasureTheory.Group.Integral

/-!
# Central quantile bounds from the two-point density inequality

The scalar argument used by the manuscript only needs the complementary
two-point inequality `f(s) f(t) ≤ f(c) f(s+t-c)`.  Integrating it over either
tail bounds every density value by the central value divided by its tail
mass.  A second integration over a central interval gives `1/(16 |J|)`.

The geometric proof that actual order-region densities satisfy the two-point
inequality is separate from this general integration argument.
-/

namespace SortingAdversary.Continuous.CentralQuantiles

open MeasureTheory Set

def TwoPoint (f : ℝ → ℝ) : Prop :=
  ∀ s c t, s ≤ c → c ≤ t → f s * f t ≤ f c * f (s + t - c)

theorem quantile_bound (f : ℝ → ℝ) (hf : Integrable f)
    (hnonneg : ∀ t, 0 ≤ f t) (hunit : ∫ t, f t = 1) (hshape : TwoPoint f)
    (c p : ℝ) (hleft : p ≤ ∫ s in Iic c, f s) (hright : p ≤ ∫ t in Ici c, f t)
    (z : ℝ) : p * f z ≤ f c := by
  rcases le_total z c with hzc | hcz
  · have hshift := hf.comp_add_right (z - c)
    have hineq := setIntegral_mono_on
      (hf.const_mul (f z)).integrableOn (hshift.const_mul (f c)).integrableOn
      measurableSet_Ici (fun t ht => by
        have h := hshape z c t hzc ht
        simpa only [add_sub_assoc, add_comm z] using h)
    rw [integral_const_mul, integral_const_mul] at hineq
    have hmass : (∫ t in Ici c, f (t + (z - c))) ≤ 1 := by
      calc
        _ ≤ ∫ t, f (t + (z - c)) := setIntegral_le_integral hshift
          (Filter.Eventually.of_forall (fun t => hnonneg _))
        _ = 1 := by rw [integral_add_right_eq_self, hunit]
    calc
      p * f z ≤ (∫ t in Ici c, f t) * f z :=
        mul_le_mul_of_nonneg_right hright (hnonneg z)
      _ = f z * ∫ t in Ici c, f t := mul_comm _ _
      _ ≤ f c * ∫ t in Ici c, f (t + (z - c)) := hineq
      _ ≤ f c * 1 := mul_le_mul_of_nonneg_left hmass (hnonneg c)
      _ = f c := mul_one _
  · have hshift := hf.comp_add_right (z - c)
    have hineq := setIntegral_mono_on
      (hf.mul_const (f z)).integrableOn (hshift.const_mul (f c)).integrableOn
      measurableSet_Iic (fun s hs => by
        simpa only [add_sub_assoc] using hshape s c z hs hcz)
    rw [integral_mul_const, integral_const_mul] at hineq
    have hmass : (∫ s in Iic c, f (s + (z - c))) ≤ 1 := by
      calc
        _ ≤ ∫ s, f (s + (z - c)) := setIntegral_le_integral hshift
          (Filter.Eventually.of_forall (fun s => hnonneg _))
        _ = 1 := by rw [integral_add_right_eq_self, hunit]
    calc
      p * f z ≤ (∫ s in Iic c, f s) * f z :=
        mul_le_mul_of_nonneg_right hleft (hnonneg z)
      _ ≤ f c * ∫ s in Iic c, f (s + (z - c)) := hineq
      _ ≤ f c * 1 := mul_le_mul_of_nonneg_left hmass (hnonneg c)
      _ = f c := mul_one _

/-- Three quarter-mass certificates imply the paper's pointwise density
bound throughout the entire certified interval, including its endpoints. -/
theorem central_interval_lower (f : ℝ → ℝ) (hf : Integrable f)
    (hnonneg : ∀ t, 0 ≤ f t) (hunit : ∫ t, f t = 1) (hshape : TwoPoint f)
    {u v c : ℝ} (huv : u < v) (hc : u ≤ c ∧ c ≤ v)
    (hleft : (1 / 4 : ℝ) ≤ ∫ s in Iic u, f s)
    (hinside : (1 / 4 : ℝ) ≤ ∫ s in Icc u v, f s)
    (hright : (1 / 4 : ℝ) ≤ ∫ s in Ici v, f s) :
    1 / (16 * (v - u)) ≤ f c := by
  have hleftc : (1 / 4 : ℝ) ≤ ∫ s in Iic c, f s := by
    apply hleft.trans
    exact setIntegral_mono_set hf.integrableOn
      (Filter.Eventually.of_forall (fun s => hnonneg s))
      (Filter.Eventually.of_forall (fun s hs => hs.trans hc.1))
  have hrightc : (1 / 4 : ℝ) ≤ ∫ s in Ici c, f s := by
    apply hright.trans
    exact setIntegral_mono_set hf.integrableOn
      (Filter.Eventually.of_forall (fun s => hnonneg s))
      (Filter.Eventually.of_forall (fun s hs => hc.2.trans hs))
  have hpoint (s : ℝ) : (1 / 4 : ℝ) * f s ≤ f c :=
    quantile_bound f hf hnonneg hunit hshape c (1 / 4) hleftc hrightc s
  have hmono := setIntegral_mono_on (hf.const_mul (1 / 4 : ℝ)).integrableOn
    (integrableOn_const (isCompact_Icc.measure_ne_top : volume (Icc u v) ≠ ⊤))
    measurableSet_Icc (fun s _ => hpoint s)
  rw [integral_const_mul, setIntegral_const, smul_eq_mul] at hmono
  have hvol : volume.real (Icc u v) = v - u := by
    simp [Measure.real_def, Real.volume_Icc, (sub_pos.mpr huv).le]
  rw [hvol] at hmono
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 16) (sub_pos.mpr huv))).mpr
  nlinarith

end SortingAdversary.Continuous.CentralQuantiles
