import SortingAdversary.Optimal.RationalWork
import SortingAdversary.Optimal.CalibrationWork

/-!
# Binary charging of the actual Euclidean rational arithmetic

`Model.charge words bits` is the bounded-operand model used here: one
primitive word operation is charged `(bits+1)^2` binary operations. This is
an explicit conservative schoolbook charging convention, not a theorem
about Lean's big-integer implementation.

The profiles below execute the same branches and exact remainder/quotient
operations as `RationalWork`. Their `result` is proved equal to the full
existing measured result, including its word count. Each Euclidean frame
uses its actual current operand width, and the final bounds prove that
these varying charges fit one polynomial input-width allowance.
-/

namespace SortingAdversary.Optimal.RationalBitWork

open PrimitiveWork

namespace Model

def unit (bits : ℕ) : ℕ := (bits + 1) ^ 2

def charge (words bits : ℕ) : ℕ := words * unit bits

theorem unit_mono {a b : ℕ} (h : a ≤ b) : unit a ≤ unit b := by
  exact Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2

theorem charge_mono {w W b B : ℕ} (hw : w ≤ W) (hb : b ≤ B) :
    charge w b ≤ charge W B := Nat.mul_le_mul hw (unit_mono hb)

theorem charge_add (first second bits : ℕ) :
    charge (first + second) bits = charge first bits + charge second bits := by
  exact Nat.add_mul ..

end Model

structure Profile (α : Type*) where
  result : Result α
  bitWork : ℕ

def euclid (a b : ℕ) (_hba : b ≤ a) : Profile ℕ :=
  if hb : b = 0 then
    ⟨⟨a, 1⟩, Model.unit (Nat.size a)⟩
  else
    let next := euclid b (a % b) (Nat.le_of_lt (Nat.mod_lt a (Nat.pos_of_ne_zero hb)))
    ⟨⟨next.result.value, next.result.work + 3⟩,
      next.bitWork + 3 * Model.unit (Nat.size a)⟩
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)

@[simp] theorem euclid_result (a b : ℕ) (hba : b ≤ a) :
    (euclid a b hba).result = RationalWork.euclid a b hba := by
  unfold euclid RationalWork.euclid
  split
  · rfl
  · rename_i hb
    dsimp only
    rw [euclid_result b (a % b)]
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)

/-- The maximum operand decreases at every Euclidean frame. -/
theorem remainder_sizes (a b : ℕ) (hba : b ≤ a) (hb : b ≠ 0) :
    Nat.size b ≤ Nat.size a ∧ Nat.size (a % b) ≤ Nat.size a := by
  exact ⟨Nat.size_le_size hba,
    Nat.size_le_size ((Nat.mod_lt a (Nat.pos_of_ne_zero hb)).le.trans hba)⟩

theorem euclid_bitWork_le (a b : ℕ) (hba : b ≤ a) (B : ℕ) (hB : Nat.size a ≤ B) :
    (euclid a b hba).bitWork ≤ Model.charge (euclid a b hba).result.work B := by
  unfold euclid
  split
  · dsimp only
    simpa only [Model.charge, one_mul] using Model.unit_mono hB
  · rename_i hb
    have ih := euclid_bitWork_le b (a % b)
      (Nat.le_of_lt (Nat.mod_lt a (Nat.pos_of_ne_zero hb))) B
      ((Nat.size_le_size hba).trans hB)
    have hu := Nat.mul_le_mul_left 3 (Model.unit_mono hB)
    dsimp only
    unfold Model.charge at ih ⊢
    calc
      _ ≤ (euclid b (a % b) _).result.work * Model.unit B + 3 * Model.unit B :=
        Nat.add_le_add ih hu
      _ = _ := by ring
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)

def gcd (a b : ℕ) : Profile ℕ :=
  if h : b ≤ a then
    let next := euclid a b h
    ⟨⟨next.result.value, next.result.work + 1⟩,
      next.bitWork + Model.unit (max (Nat.size a) (Nat.size b))⟩
  else
    let next := euclid b a (Nat.le_of_lt (Nat.lt_of_not_ge h))
    ⟨⟨next.result.value, next.result.work + 1⟩,
      next.bitWork + Model.unit (max (Nat.size a) (Nat.size b))⟩

@[simp] theorem gcd_result (a b : ℕ) : (gcd a b).result = RationalWork.gcd a b := by
  simp only [gcd, RationalWork.gcd]
  split <;> simp only [euclid_result]

theorem gcd_bitWork_le (a b B : ℕ) (ha : Nat.size a ≤ B) (hb : Nat.size b ≤ B) :
    (gcd a b).bitWork ≤ Model.charge (gcd a b).result.work B := by
  have hu := Model.unit_mono (max_le ha hb)
  unfold gcd
  split
  · rename_i h
    have ih := euclid_bitWork_le a b h B ha
    dsimp only
    unfold Model.charge at ih ⊢
    calc
      _ ≤ (euclid a b h).result.work * Model.unit B + Model.unit B := Nat.add_le_add ih hu
      _ = _ := by ring
  · rename_i h
    have ih := euclid_bitWork_le b a (Nat.le_of_lt (Nat.lt_of_not_ge h)) B hb
    dsimp only
    unfold Model.charge at ih ⊢
    calc
      _ ≤ (euclid b a _).result.work * Model.unit B + Model.unit B := Nat.add_le_add ih hu
      _ = _ := by ring

theorem gcd_value_size (a b B : ℕ) (ha : Nat.size a ≤ B) (hb : Nat.size b ≤ B) :
    Nat.size (gcd a b).result.value ≤ B := by
  rw [gcd_result, RationalWork.gcd_value]
  by_cases hz : a = 0
  · simpa only [hz, Nat.gcd_zero_left] using hb
  · exact (Nat.size_le_size (Nat.gcd_le_left b (Nat.pos_of_ne_zero hz))).trans ha

/-- Only the measured common divisor supplies the two quotient operands. -/
def normalize (num : ℤ) (den : ℕ) (hden : den ≠ 0) : Profile ℚ :=
  let divisor := gcd num.natAbs den
  ⟨⟨{ num := num / (divisor.result.value : ℤ),
       den := den / divisor.result.value,
       den_nz := Rat.normalize.den_nz hden (by
         rw [gcd_result, RationalWork.gcd_value]),
       reduced := Rat.normalize.reduced hden (by
         rw [gcd_result, RationalWork.gcd_value]) },
      divisor.result.work + 6⟩,
    divisor.bitWork + 6 * Model.unit (max (Nat.size num.natAbs) (Nat.size den))⟩

@[simp] theorem normalize_result (num : ℤ) (den : ℕ) (hden : den ≠ 0) :
    (normalize num den hden).result = RationalWork.normalize num den hden := by
  simp only [normalize, RationalWork.normalize, gcd_result]

theorem normalize_bitWork_le (num : ℤ) (den : ℕ) (hden : den ≠ 0) (B : ℕ)
    (hn : Nat.size num.natAbs ≤ B) (hd : Nat.size den ≤ B) :
    (normalize num den hden).bitWork ≤ Model.charge (normalize num den hden).result.work B := by
  have hg := gcd_bitWork_le num.natAbs den B hn hd
  have hu := Nat.mul_le_mul_left 6 (Model.unit_mono (max_le hn hd))
  change (gcd num.natAbs den).bitWork + _ ≤ _
  unfold Model.charge at hg ⊢
  change (gcd num.natAbs den).bitWork + _ ≤
    ((gcd num.natAbs den).result.work + 6) * Model.unit B
  exact (Nat.add_le_add hg hu).trans_eq (by ring)

/-- The two exact quotient outputs and their common-divisor operand all
fit the same input-width bound. -/
theorem normalize_operand_sizes (num : ℤ) (den : ℕ) (hden : den ≠ 0) (B : ℕ)
    (hn : Nat.size num.natAbs ≤ B) (hd : Nat.size den ≤ B) :
    Nat.size (gcd num.natAbs den).result.value ≤ B ∧
      Nat.size (normalize num den hden).result.value.num.natAbs ≤ B ∧
      Nat.size (normalize num den hden).result.value.den ≤ B := by
  have h := RationalWork.normalize_sizes num den hden
  rw [normalize_result]
  exact ⟨gcd_value_size num.natAbs den B hn hd, h.1.trans hn, h.2.trans hd⟩

def ratio (num den : ℕ) : Profile ℚ :=
  if hden : den = 0 then
    ⟨⟨0, 1⟩, Model.unit (max (Nat.size num) (Nat.size den))⟩
  else
    let next := normalize (num : ℤ) den hden
    ⟨⟨next.result.value, next.result.work + 2⟩,
      next.bitWork + 2 * Model.unit (max (Nat.size num) (Nat.size den))⟩

@[simp] theorem ratio_result (num den : ℕ) : (ratio num den).result = RationalWork.ratio num den := by
  simp only [ratio, RationalWork.ratio]
  split
  · rfl
  · simp only [normalize_result]

theorem ratio_bitWork_le (num den B : ℕ) (hn : Nat.size num ≤ B) (hd : Nat.size den ≤ B) :
    (ratio num den).bitWork ≤ Model.charge (ratio num den).result.work B := by
  have hu := Model.unit_mono (max_le hn hd)
  unfold ratio
  split
  · dsimp only
    simpa only [Model.charge, one_mul] using hu
  · rename_i hden
    have hg := normalize_bitWork_le (num : ℤ) den hden B (by simpa only [Int.natAbs_natCast]) hd
    dsimp only
    unfold Model.charge at hg ⊢
    exact (Nat.add_le_add hg (Nat.mul_le_mul_left 2 hu)).trans_eq (by ring)

theorem ratio_bitWork_polynomial (num den B : ℕ)
    (hn : Nat.size num ≤ B) (hd : Nat.size den ≤ B) :
    (ratio num den).bitWork ≤ (6 * B + 10) * (B + 1) ^ 2 := by
  apply (ratio_bitWork_le num den B hn hd).trans
  rw [ratio_result]
  exact Nat.mul_le_mul_right _ ((RationalWork.ratio_work_le num den).trans (by omega))

/-- The exact signed products of the seven-operation comparator. -/
def lessEqual (left right : ℚ) : Profile Bool :=
  let bits := max (max (Nat.size left.num.natAbs) (Nat.size left.den))
    (max (Nat.size right.num.natAbs) (Nat.size right.den))
  ⟨⟨decide (left.num * (right.den : ℤ) ≤ right.num * (left.den : ℤ)), 7⟩,
    7 * Model.unit (2 * bits)⟩

@[simp] theorem lessEqual_result (left right : ℚ) :
    (lessEqual left right).result = CalibrationWork.lessEqual left right := rfl

theorem lessEqual_bitWork_le (left right : ℚ) (B : ℕ)
    (hl : Nat.size left.num.natAbs ≤ B ∧ Nat.size left.den ≤ B)
    (hr : Nat.size right.num.natAbs ≤ B ∧ Nat.size right.den ≤ B) :
    (lessEqual left right).bitWork ≤ 7 * (2 * B + 1) ^ 2 := by
  exact Nat.mul_le_mul_left 7 (Model.unit_mono (Nat.mul_le_mul_left 2
    (max_le (max_le hl.1 hl.2) (max_le hr.1 hr.2))))

end SortingAdversary.Optimal.RationalBitWork
