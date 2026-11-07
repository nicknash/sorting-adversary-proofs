import SortingAdversary.Optimal.RationalWork
import SortingAdversary.Optimal.WidthScaleSelect

/-!
# Counted arithmetic for repair constants and receipts

These routines compute the natural powers used by an admitted stage and
construct the actual reduced rational receipts. The stage selector has
already rejected oversized stages using capped arithmetic. Linear iteration
in the admitted exponent is sufficient here, and every multiplication is
included in the returned work counter.
-/

namespace SortingAdversary.Optimal.WidthScalarWork

open PrimitiveWork WidthRepair

def power (base : ℕ) : ℕ → Result ℕ
  | 0 => ⟨1, 1⟩
  | e + 1 => let previous := power base e
             ⟨previous.value * base, previous.work + 2⟩

@[simp] theorem power_value (base e : ℕ) : (power base e).value = base ^ e := by
  induction e <;> simp_all [power, pow_succ]

@[simp] theorem power_work (base e : ℕ) : (power base e).work = 2 * e + 1 := by
  induction e <;> simp_all [power]
  omega

theorem power_value_le {base e E : ℕ} (hb : 1 ≤ base) (he : e ≤ E) :
    (power base e).value ≤ base ^ E := by
  rw [power_value]
  exact Nat.pow_le_pow_right hb he

def cheap (p : WidthParameters) : Result ℚ :=
  let four := power 4 p.B
  ⟨(p.W₀ * four.value : ℕ), four.work + 3⟩

@[simp] theorem cheap_value (p : WidthParameters) : (cheap p).value = p.cheapCharge := by
  simp only [cheap, power_value, WidthParameters.cheapCharge, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

@[simp] theorem cheap_work (p : WidthParameters) : (cheap p).work = 2 * p.B + 4 := by
  simp only [cheap, power_work]

def cut (p : WidthParameters) : Result ℚ :=
  let four := power 4 p.B
  let result := RationalWork.ratio p.L (p.L - 2 * four.value)
  ⟨result.value, four.work + result.work + 2⟩

@[simp] theorem cut_value (p : WidthParameters) : (cut p).value = p.cutCharge := by
  have hle : 2 * 4 ^ p.B ≤ p.L := p.cutBudget.le
  simp only [cut, RationalWork.ratio_value, power_value, WidthParameters.cutCharge,
    WidthParameters.constant, Nat.cast_sub hle, Nat.cast_mul]

def cutBound (p : WidthParameters) : ℕ := 2 * p.B + 6 * Nat.size p.L + 13

theorem cut_work_le (p : WidthParameters) : (cut p).work ≤ cutBound p := by
  have h := RationalWork.ratio_work_le p.L (p.L - 2 * 4 ^ p.B)
  have hs := Nat.size_le_size (Nat.sub_le p.L (2 * 4 ^ p.B))
  simp only [cut, power_work, power_value]
  unfold cutBound
  omega

def scale (B length : ℕ) : Result ℚ :=
  let four := power 4 B
  ⟨(2 * four.value * length : ℕ), four.work + 4⟩

@[simp] theorem scale_value (B length : ℕ) :
    (scale B length).value = (2 * 4 ^ B * length : ℕ) := by simp only [scale, power_value]

@[simp] theorem scale_work (B length : ℕ) : (scale B length).work = 2 * B + 5 := by
  simp only [scale, power_work]

def base (p : ScaleParameters) : Result ℕ :=
  let exponent := 2 * p.H + 3
  let raised := power (p.width.L + 1) exponent
  ⟨128 * p.J * raised.value, raised.work + 5⟩

@[simp] theorem base_value (p : ScaleParameters) : (base p).value = p.A := by
  simp only [base, power_value, ScaleParameters.A, ScaleGeometry.scaleBase]

@[simp] theorem base_work (p : ScaleParameters) : (base p).work = 4 * p.H + 12 := by
  simp only [base, power_work]
  omega

def ratio (p : ScaleParameters) : Result ℕ :=
  let scaleBase := base p
  let raised := power scaleBase.value (p.J + 1)
  ⟨raised.value, scaleBase.work + raised.work + 1⟩

@[simp] theorem ratio_value (p : ScaleParameters) : (ratio p).value = p.R := by
  simp only [ratio, power_value, base_value, ScaleParameters.R]

@[simp] theorem ratio_work (p : ScaleParameters) : (ratio p).work = 4 * p.H + 2 * p.J + 16 := by
  simp only [ratio, power_work, base_work]
  omega

end SortingAdversary.Optimal.WidthScalarWork
