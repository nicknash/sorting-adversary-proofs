import SortingAdversary.Optimal.Accounting
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Sigma

/-!
# A finite dictionary for immutable dyadic batches

Give each new colour its consecutive birth number. A binary-counter batch of
size `2^a` consists of one of the consecutive birth intervals
`[j * 2^a, (j + 1) * 2^a)`. Sorting the colours within this immutable batch
changes their palette order, but not the batch's identity.

For a lifetime birth cap `2^M`, a block of size `2^(M-d)` can occur in a batch
at any of the `d+1` larger scales. At each such scale there are exactly `2^d`
possible pairs of batch and block indices. `HubSlot M` supplies these slots
and one extra row at each scale for exceptional singleton choices. It is a
finite, executable envelope dictionary; unused slots are harmless.

The cubic code below is proved to have total mass at most one. Consequently
any set of distinct colours, each supplied with a slot that decodes to that
colour, inherits a subprobability code. No probabilistic coding estimate or
asymptotic counting bound is assumed.
-/

namespace SortingAdversary.Optimal.DyadicDictionary

open scoped BigOperators

/-- A computable power-of-two envelope for an arbitrary positive birth cap. -/
def capExponent (births : ℕ) : ℕ := Nat.log 2 births + 1

theorem le_dyadic_cap (births : ℕ) : births ≤ 2 ^ capExponent births :=
  (Nat.lt_pow_succ_log_self (by decide : 1 < 2) births).le

theorem dyadic_cap_le_twice {births : ℕ} (hbirths : 0 < births) :
    2 ^ capExponent births ≤ 2 * births := by
  unfold capExponent
  rw [pow_succ]
  have h := Nat.pow_log_le_self 2 hbirths.ne'
  omega

/-- A scale deficit, a batch-scale row, and a batch/block index. Rows below
`d+1` are the ordinary dyadic records; the last row is available for exceptions.
-/
abbrev HubSlot (M : ℕ) := Σ d : Fin (M + 1), Fin (d.val + 2) × Fin (2 ^ d.val)

/-- Encode an actual aligned block in an actual immutable batch. `e` is the
block exponent, `a` is the batch exponent, `batch` its chronological index,
and `block` its index inside the batch after sorting in palette order. -/
def batchSlot (M e a : ℕ) (hea : e ≤ a) (haM : a ≤ M)
    (batch : Fin (2 ^ (M - a))) (block : Fin (2 ^ (a - e))) : HubSlot M :=
  ⟨⟨M - e, by omega⟩, ⟨⟨a - e, by change a - e < M - e + 2; omega⟩,
    ⟨batch.val * 2 ^ (a - e) + block.val, by
    calc
      batch.val * 2 ^ (a - e) + block.val <
          (batch.val + 1) * 2 ^ (a - e) := by
        have h := block.isLt
        nlinarith
      _ ≤ 2 ^ (M - a) * 2 ^ (a - e) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt batch.isLt)
      _ = 2 ^ (M - e) := by rw [← pow_add]; congr 1; omega⟩⟩⟩

@[simp] theorem batchSlot_deficit (M e a : ℕ) (hea : e ≤ a) (haM : a ≤ M)
    (batch : Fin (2 ^ (M - a))) (block : Fin (2 ^ (a - e))) :
    (batchSlot M e a hea haM batch block).1.val = M - e := rfl

/-- A batch fully born before the cap has an admissible chronological index.
This proves the history bound for retired batches as well as current ones. -/
theorem batch_index_lt {M a batch births : ℕ} (haM : a ≤ M)
    (hborn : (batch + 1) * 2 ^ a ≤ births) (hcap : births ≤ 2 ^ M) :
    batch < 2 ^ (M - a) := by
  have hmul : (batch + 1) * 2 ^ a ≤ 2 ^ (M - a) * 2 ^ a := by
    rw [Nat.pow_sub_mul_pow 2 haM]
    exact hborn.trans hcap
  have h := Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos a)
  omega

/-- Distinct batches at a fixed scale have disjoint birth intervals. -/
theorem batch_intervals_disjoint {a i j colour : ℕ} (hij : i ≠ j)
    (hi : i * 2 ^ a ≤ colour) (hi' : colour < (i + 1) * 2 ^ a)
    (hj : j * 2 ^ a ≤ colour) (hj' : colour < (j + 1) * 2 ^ a) : False := by
  rcases lt_or_gt_of_ne hij with h | h
  · have hbound := Nat.mul_le_mul_right (2 ^ a) (Nat.succ_le_of_lt h)
    change (i + 1) * 2 ^ a ≤ j * 2 ^ a at hbound
    omega
  · have hbound := Nat.mul_le_mul_right (2 ^ a) (Nat.succ_le_of_lt h)
    change (j + 1) * 2 ^ a ≤ i * 2 ^ a at hbound
    omega

/-- One-based position of the midpoint hub of a nonsingleton aligned block
of size `2^(e+1)`. -/
def hubPosition (e block : ℕ) : ℕ := (2 * block + 1) * 2 ^ e

private theorem odd_mul_pow_two_ne_of_lt {e f i j : ℕ} (hef : e < f) :
    (2 * i + 1) * 2 ^ e ≠ (2 * j + 1) * 2 ^ f := by
  intro heq
  have hf : f = e + (f - e - 1) + 1 := by omega
  rw [hf, pow_succ, pow_add] at heq
  have hcancel : (2 * i + 1) * 2 ^ e =
      (2 * ((2 * j + 1) * 2 ^ (f - e - 1))) * 2 ^ e := by
    nlinarith [heq]
  have h := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos e) hcancel
  omega

/-- A colour is the hub of at most one nonsingleton aligned block in a
fixed immutable batch, even when blocks of different sizes are considered.
Singletons are deliberately a separate kind. -/
theorem hubPosition_injective {e f i j : ℕ}
    (heq : hubPosition e i = hubPosition f j) : e = f ∧ i = j := by
  have hef : e = f := by
    rcases lt_trichotomy e f with h | h | h
    · exact False.elim (odd_mul_pow_two_ne_of_lt h heq)
    · exact h
    · exact False.elim (odd_mul_pow_two_ne_of_lt h heq.symm)
  subst f
  have h := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos e) heq
  exact ⟨rfl, by omega⟩

/-- The represented block size. -/
def blockSize {M : ℕ} (slot : HubSlot M) : ℕ := 2 ^ (M - slot.1.val)

/-- The cubic dictionary code. This uses the binary scale deficit directly;
the logarithm in the price accounting is natural. -/
noncomputable def code {M : ℕ} (slot : HubSlot M) : ℝ :=
  1 / ((2 : ℝ) ^ slot.1.val * (slot.1.val + 2 : ℝ) ^ 3)

theorem code_pos {M : ℕ} (slot : HubSlot M) : 0 < code slot := by
  unfold code
  positivity

/-- The represented block and its deficit multiply to the common birth cap. -/
theorem blockSize_mul_pow_deficit {M : ℕ} (slot : HubSlot M) :
    blockSize slot * 2 ^ slot.1.val = 2 ^ M := by
  rw [blockSize, ← pow_add, Nat.sub_add_cancel (by omega : slot.1.val ≤ M)]

/-- A completely explicit real bound used to sum the finite code. -/
theorem inverse_square_le_telescope (d : ℕ) :
    1 / (d + 2 : ℝ) ^ 2 ≤ 1 / (d + 1 : ℝ) - 1 / (d + 2 : ℝ) := by
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  have hd2 : (0 : ℝ) < d + 2 := by positivity
  field_simp
  nlinarith

theorem sum_inverse_square_le_one (N : ℕ) :
    (∑ d ∈ Finset.range N, 1 / (d + 2 : ℝ) ^ 2) ≤ 1 - 1 / (N + 1 : ℝ) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have h := inverse_square_le_telescope N
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc]
      linarith

/-- Summing over every record, including unused and exceptional slots, costs
at most one. This is a finite telescoping proof, independent of `M`. -/
theorem sum_code_le_one (M : ℕ) :
    (∑ slot : HubSlot M, code slot) ≤ 1 := by
  have hsum : (∑ slot : HubSlot M, code slot) =
      ∑ d ∈ Finset.range (M + 1), 1 / (d + 2 : ℝ) ^ 2 := by
    rw [Fintype.sum_sigma]
    simp only [code, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    calc
      _ = ∑ d : Fin (M + 1), 1 / (d.val + 2 : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro d hd
        have hd2 : (d.val + 2 : ℝ) ≠ 0 := by positivity
        have hpow : (2 : ℝ) ^ d.val ≠ 0 := by positivity
        push_cast
        field_simp
      _ = _ := Fin.sum_univ_eq_sum_range (fun d : ℕ => 1 / (d + 2 : ℝ) ^ 2) (M + 1)
  rw [hsum]
  exact (sum_inverse_square_le_one (M + 1)).trans (by
    have h : 0 ≤ 1 / (((M + 1 : ℕ) : ℝ) + 1) := by positivity
    linarith)

/-- A decoder makes distinct destinations have distinct selected slots.
Thus the code bound follows from the concrete dictionary, rather than being
an additional hypothesis about the selected destinations. -/
theorem selected_code_le_one {M : ℕ} {Colour : Type*} [DecidableEq Colour]
    (destinations : Finset Colour) (selected : Colour → HubSlot M)
    (decode : HubSlot M → Colour)
    (hdecode : ∀ c ∈ destinations, decode (selected c) = c) :
    (∑ c ∈ destinations, code (selected c)) ≤ 1 := by
  have hinj : Set.InjOn selected destinations := by
    intro c hc c' hc' heq
    calc
      c = decode (selected c) := (hdecode c hc).symm
      _ = decode (selected c') := congrArg decode heq
      _ = c' := hdecode c' hc'
  calc
    _ = ∑ slot ∈ destinations.image selected, code slot :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ slot : HubSlot M, code slot :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun slot _ _ => (code_pos slot).le)
    _ ≤ 1 := sum_code_le_one M

/-! ## Joining dictionaries from all pools -/

/-- A node identity followed by its finite hub record. -/
abbrev GlobalSlot {Node : Type*} (exponent : Node → ℕ) :=
  Σ v : Node, HubSlot (exponent v)

/-- Total capacity of all dyadic dictionaries. -/
def totalCapacity {Node : Type*} [Fintype Node] (exponent : Node → ℕ) : ℕ :=
  ∑ v, 2 ^ exponent v

theorem totalCapacity_pos {Node : Type*} [Fintype Node] [Nonempty Node]
    (exponent : Node → ℕ) : 0 < totalCapacity exponent := by
  exact Finset.sum_pos (fun v _ => Nat.two_pow_pos (exponent v)) Finset.univ_nonempty

/-- Node capacities normalize the disjoint union of the finite codes. -/
noncomputable def globalCode {Node : Type*} [Fintype Node]
    {exponent : Node → ℕ} (slot : GlobalSlot exponent) : ℝ :=
  ((2 : ℝ) ^ exponent slot.1 / totalCapacity exponent) * code slot.2

theorem globalCode_pos {Node : Type*} [Fintype Node] [Nonempty Node]
    {exponent : Node → ℕ} (slot : GlobalSlot exponent) : 0 < globalCode slot := by
  have htotal : (0 : ℝ) < totalCapacity exponent := by
    exact_mod_cast totalCapacity_pos exponent
  exact mul_pos (div_pos (by positivity) htotal) (code_pos slot.2)

theorem sum_globalCode_le_one {Node : Type*} [Fintype Node] [Nonempty Node]
    (exponent : Node → ℕ) :
    (∑ slot : GlobalSlot exponent, globalCode slot) ≤ 1 := by
  have htotal : (0 : ℝ) < totalCapacity exponent := by
    exact_mod_cast totalCapacity_pos exponent
  rw [Fintype.sum_sigma]
  simp only [globalCode, ← Finset.mul_sum]
  calc
    _ ≤ ∑ v, (2 : ℝ) ^ exponent v / totalCapacity exponent := by
      apply Finset.sum_le_sum
      intro v hv
      exact mul_le_of_le_one_right (by positivity) (sum_code_le_one (exponent v))
    _ = 1 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      have hsum : (∑ v, (2 : ℝ) ^ exponent v) = (totalCapacity exponent : ℝ) := by
        simp [totalCapacity]
      rw [hsum, mul_inv_cancel₀ htotal.ne']

/-- The global code bound for selected distinct destinations, including the
entire histories of all nodes' dictionaries. -/
theorem selected_globalCode_le_one {Node Colour : Type*} [Fintype Node]
    [Nonempty Node] [DecidableEq Colour] {exponent : Node → ℕ}
    (destinations : Finset Colour) (selected : Colour → GlobalSlot exponent)
    (decode : GlobalSlot exponent → Colour)
    (hdecode : ∀ c ∈ destinations, decode (selected c) = c) :
    (∑ c ∈ destinations, globalCode (selected c)) ≤ 1 := by
  classical
  have hinj : Set.InjOn selected destinations := by
    intro c hc c' hc' heq
    calc
      c = decode (selected c) := (hdecode c hc).symm
      _ = decode (selected c') := congrArg decode heq
      _ = c' := hdecode c' hc'
  calc
    _ = ∑ slot ∈ destinations.image selected, globalCode slot :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ slot : GlobalSlot exponent, globalCode slot :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun slot _ _ => (globalCode_pos slot).le)
    _ ≤ 1 := sum_globalCode_le_one exponent

end SortingAdversary.Optimal.DyadicDictionary
