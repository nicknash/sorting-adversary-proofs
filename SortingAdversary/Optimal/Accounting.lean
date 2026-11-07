import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Accounting for recursive colour assignments

This file proves finite accounting lemmas used by the November 7 recursive
sorting-adversary manuscript. All logarithms here are **natural logarithms**.
The conversion to comparison bits is the explicit factor `Real.log 2`.

The results do not assume an optimal-adversary theorem. They establish the
factorial credit, tree telescoping, incidence counting, and signed update
accounting from their stated elementary hypotheses. In particular, the final
clock bound is conditional on the individual update inequalities and on the
terminal and promotion budgets. This file does not establish those hypotheses
for the controller, or claim a polynomial-time implementation of it.
-/

namespace SortingAdversary.Optimal.Accounting

open scoped BigOperators

/-! ## Daughter admissions and factorial credits -/

/-- At the `j`th admission, numbered starting with one, a free daughter birth
has at least `j` possible colours. Thus the product of the birth multipliers
dominates the factorial of the number of admissions. Other kinds of admissions
may be interleaved; only this pointwise lower bound is needed. -/
theorem factorial_le_birth_product (k : ℕ) (birth : ℕ → ℕ)
    (hbirth : ∀ j < k, j + 1 ≤ birth j) :
    k.factorial ≤ ∏ j ∈ Finset.range k, birth j := by
  rw [Nat.factorial_eq_prod_range_add_one]
  exact Finset.prod_le_prod' fun j hj => hbirth j (Finset.mem_range.mp hj)

/-- The logarithmic version of the birthday product credit. -/
theorem log_factorial_le_birth_credit (k : ℕ) (birth : ℕ → ℕ)
    (hbirth : ∀ j < k, j + 1 ≤ birth j) :
    Real.log (k.factorial : ℝ) ≤
      ∑ j ∈ Finset.range k, Real.log (birth j : ℝ) := by
  have hpos : ∀ j ∈ Finset.range k, (0 : ℝ) < birth j := by
    intro j hj
    have h := hbirth j (Finset.mem_range.mp hj)
    exact_mod_cast (show 0 < birth j by omega)
  rw [← Real.log_prod (fun j hj => (hpos j hj).ne')]
  apply Real.log_le_log (by positivity)
  exact_mod_cast factorial_le_birth_product k birth hbirth

/-- A bounded individual pin price has a bounded *total signed* price at one
daughter, regardless of how often that daughter receives a cheap admission.
The factorial credit is essential here: the bound is independent of `k`.

For a pin retaining fraction at least `1 / A`, its natural-log debit is at most
`log A`; after the daughter credits the net debit is at most `A`.
-/
theorem cheap_signed_debit_le (A : ℝ) (hA : 0 < A) (k : ℕ) :
    (k : ℝ) * Real.log A - Real.log (k.factorial : ℝ) ≤ A := by
  have hterm : 0 < A ^ k / (k.factorial : ℝ) := by positivity
  have hbound := (Real.log_le_iff_le_exp hterm).mpr
    (Real.pow_div_factorial_le_exp A hA.le k)
  have hfactorial : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [Real.log_div (pow_pos hA k).ne' hfactorial, Real.log_pow] at hbound
  exact hbound

/-- Summing cheap signed prices costs at most one constant per daughter,
not one constant per admission. -/
theorem sum_cheap_signed_debit_le {ι : Type*} (s : Finset ι)
    (admissions : ι → ℕ) (A : ℝ) (hA : 0 < A) :
    (∑ c ∈ s, ((admissions c : ℝ) * Real.log A -
      Real.log ((admissions c).factorial : ℝ))) ≤ (s.card : ℝ) * A := by
  calc
    _ ≤ ∑ _c ∈ s, A :=
      Finset.sum_le_sum fun c _hc => cheap_signed_debit_le A hA (admissions c)
    _ = _ := by simp

/-- The same estimate can be used with measured admission credits and measured
pin debits. Neither of the two sums has to be nonnegative. -/
theorem cheap_debit_with_births (A debit : ℝ) (hA : 0 < A)
    (k : ℕ) (birth : ℕ → ℕ)
    (hdebit : debit ≤ (k : ℝ) * Real.log A)
    (hbirth : ∀ j < k, j + 1 ≤ birth j) :
    debit - (∑ j ∈ Finset.range k, Real.log (birth j : ℝ)) ≤ A := by
  have hcredit := log_factorial_le_birth_credit k birth hbirth
  have hcheap := cheap_signed_debit_le A hA k
  linarith

/-- The elementary logarithmic factorial lower bound, obtained directly from
one nonnegative term in the exponential series. No asymptotic Stirling formula
is needed for the accounting argument. -/
theorem log_factorial_lower_bound (k : ℕ) :
    (k : ℝ) * Real.log (k : ℝ) - k ≤ Real.log (k.factorial : ℝ) := by
  by_cases hk : k = 0
  · simp [hk]
  · have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have h := cheap_signed_debit_le (k : ℝ) hkpos k
    linarith

/-! ## Finite codes and signed prices -/

/-- The log-sum inequality for a subprobability code. `weight` gives the
positive multiplicities on the retained support; `code` gives positive code
masses whose sum is at most one. The proof uses only `log x ≤ x - 1`.
-/
theorem log_sum_subprobability {ι : Type*} (s : Finset ι)
    (weight code : ι → ℝ)
    (hweight : ∀ i ∈ s, 0 < weight i)
    (hcode : ∀ i ∈ s, 0 < code i)
    (hcodesum : (∑ i ∈ s, code i) ≤ 1) :
    (∑ i ∈ s, weight i * Real.log (code i / weight i)) ≤
      -(∑ i ∈ s, weight i) * Real.log (∑ i ∈ s, weight i) := by
  by_cases hs : s.Nonempty
  · let P := ∑ i ∈ s, weight i
    have hP : 0 < P := Finset.sum_pos hweight hs
    have hlocal (i : ι) (hi : i ∈ s) :
        weight i * Real.log (code i / weight i) + weight i * Real.log P ≤
          P * code i - weight i := by
      have hlog := Real.log_le_sub_one_of_pos
        (div_pos (mul_pos (hcode i hi) hP) (hweight i hi))
      have hexpand : Real.log (code i * P / weight i) =
          Real.log (code i / weight i) + Real.log P := by
        rw [show code i * P / weight i = (code i / weight i) * P by ring,
          Real.log_mul (div_pos (hcode i hi) (hweight i hi)).ne' hP.ne']
      rw [hexpand] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog (hweight i hi).le
      have hcancel : weight i * (code i * P / weight i - 1) =
          P * code i - weight i := by
        field_simp [(hweight i hi).ne']
      rw [hcancel] at hmul
      nlinarith
    have hsum := Finset.sum_le_sum hlocal
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum] at hsum
    have hcodeP : P * (∑ i ∈ s, code i) ≤ P := by
      simpa using mul_le_mul_of_nonneg_left hcodesum hP.le
    change (∑ i ∈ s, weight i * Real.log (code i / weight i)) + P * Real.log P ≤
      P * (∑ i ∈ s, code i) - P at hsum
    change (∑ i ∈ s, weight i * Real.log (code i / weight i)) ≤ -P * Real.log P
    nlinarith
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hempty]

/-- Scaling the code masses changes the bound by one logarithmic term for the
total weight. This is the form used for the dyadic-hub dictionary. -/
theorem coded_debit_le {ι : Type*} (s : Finset ι) (weight code : ι → ℝ)
    (A : ℝ) (hA : 0 < A)
    (hweight : ∀ i ∈ s, 0 < weight i)
    (hcode : ∀ i ∈ s, 0 < code i)
    (hcodesum : (∑ i ∈ s, code i) ≤ 1) :
    (∑ i ∈ s, weight i * Real.log (A * code i / weight i)) ≤
      (∑ i ∈ s, weight i) * Real.log (A / (∑ i ∈ s, weight i)) := by
  by_cases hs : s.Nonempty
  · have hP : 0 < ∑ i ∈ s, weight i := Finset.sum_pos hweight hs
    have hlogsum := log_sum_subprobability s weight code hweight hcode hcodesum
    have hrewrite :
        (∑ i ∈ s, weight i * Real.log (A * code i / weight i)) =
        (∑ i ∈ s, weight i) * Real.log A +
          ∑ i ∈ s, weight i * Real.log (code i / weight i) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [show A * code i / weight i = A * (code i / weight i) by ring,
        Real.log_mul hA.ne' (div_pos (hcode i hi) (hweight i hi)).ne']
      ring
    rw [hrewrite, Real.log_div hA.ne' hP.ne']
    nlinarith
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hempty]

/-- A code bound together with the actual factorial daughter credits. This
is the signed-price estimate before the manuscript's logarithmic hub surcharge
is added. All quantities on the right depend on the total number of admissions,
rather than the number of pools in which an ordinary pin happened.
-/
theorem factorial_coded_debit_le {ι : Type*} (s : Finset ι)
    (admissions : ι → ℕ) (code : ι → ℝ) (A : ℝ) (hA : 0 < A)
    (hadmissions : ∀ i ∈ s, 0 < admissions i)
    (hcode : ∀ i ∈ s, 0 < code i)
    (hcodesum : (∑ i ∈ s, code i) ≤ 1) :
    (∑ i ∈ s, ((admissions i : ℝ) * Real.log (A * code i) -
      Real.log ((admissions i).factorial : ℝ))) ≤
      (∑ i ∈ s, (admissions i : ℝ)) *
        Real.log (A / (∑ i ∈ s, (admissions i : ℝ))) +
          ∑ i ∈ s, (admissions i : ℝ) := by
  have hpositive (i : ι) (hi : i ∈ s) : (0 : ℝ) < admissions i := by
    exact_mod_cast hadmissions i hi
  have hlocal (i : ι) (hi : i ∈ s) :
      (admissions i : ℝ) * Real.log (A * code i) -
        Real.log ((admissions i).factorial : ℝ) ≤
      (admissions i : ℝ) * Real.log (A * code i / admissions i) + admissions i := by
    rw [Real.log_div (mul_pos hA (hcode i hi)).ne' (hpositive i hi).ne']
    have hfactorial := log_factorial_lower_bound (admissions i)
    nlinarith
  calc
    _ ≤ ∑ i ∈ s, ((admissions i : ℝ) *
        Real.log (A * code i / admissions i) + admissions i) :=
      Finset.sum_le_sum hlocal
    _ = (∑ i ∈ s, (admissions i : ℝ) * Real.log (A * code i / admissions i)) +
        ∑ i ∈ s, (admissions i : ℝ) := Finset.sum_add_distrib
    _ ≤ _ := by
      have h := coded_debit_le s (fun i => (admissions i : ℝ)) code A hA hpositive hcode hcodesum
      linarith

/-- Additional per-admission charges, such as the scale surcharge or the hub
length correction, can be kept separate without losing the factorial credit. -/
theorem factorial_coded_debit_le_with_surcharge {ι : Type*} (s : Finset ι)
    (admissions : ι → ℕ) (code surcharge : ι → ℝ) (A : ℝ) (hA : 0 < A)
    (hadmissions : ∀ i ∈ s, 0 < admissions i)
    (hcode : ∀ i ∈ s, 0 < code i)
    (hcodesum : (∑ i ∈ s, code i) ≤ 1) :
    (∑ i ∈ s, ((admissions i : ℝ) * (Real.log (A * code i) + surcharge i) -
      Real.log ((admissions i).factorial : ℝ))) ≤
      (∑ i ∈ s, (admissions i : ℝ)) *
        Real.log (A / (∑ i ∈ s, (admissions i : ℝ))) +
          (∑ i ∈ s, (admissions i : ℝ)) +
            ∑ i ∈ s, (admissions i : ℝ) * surcharge i := by
  have hbase := factorial_coded_debit_le s admissions code A hA hadmissions hcode hcodesum
  have hrewrite :
      (∑ i ∈ s, ((admissions i : ℝ) * (Real.log (A * code i) + surcharge i) -
        Real.log ((admissions i).factorial : ℝ))) =
      (∑ i ∈ s, ((admissions i : ℝ) * Real.log (A * code i) -
        Real.log ((admissions i).factorial : ℝ))) +
        ∑ i ∈ s, (admissions i : ℝ) * surcharge i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hrewrite]
  linarith

/-- Finite weighted Jensen inequality for the logarithm, derived from the
same elementary code inequality. The weights need not be normalized. -/
theorem weighted_log_le {ι : Type*} (s : Finset ι) (weight value : ι → ℝ)
    (hweight : ∀ i ∈ s, 0 < weight i)
    (hvalue : ∀ i ∈ s, 0 < value i) :
    (∑ i ∈ s, weight i * Real.log (value i)) ≤
      (∑ i ∈ s, weight i) *
        Real.log ((∑ i ∈ s, weight i * value i) / (∑ i ∈ s, weight i)) := by
  by_cases hs : s.Nonempty
  · let total := ∑ i ∈ s, weight i * value i
    have htotal : 0 < total :=
      Finset.sum_pos (fun i hi => mul_pos (hweight i hi) (hvalue i hi)) hs
    let code := fun i => weight i * value i / total
    have hcode (i : ι) (hi : i ∈ s) : 0 < code i :=
      div_pos (mul_pos (hweight i hi) (hvalue i hi)) htotal
    have hcodesum : (∑ i ∈ s, code i) ≤ 1 := by
      dsimp only [code]
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      change total / total ≤ 1
      rw [div_self htotal.ne']
    have h := coded_debit_le s weight code total htotal hweight hcode hcodesum
    have hrewrite :
        (∑ i ∈ s, weight i * Real.log (total * code i / weight i)) =
          ∑ i ∈ s, weight i * Real.log (value i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have harg : total * code i / weight i = value i := by
        dsimp only [code]
        field_simp [htotal.ne', (hweight i hi).ne']
      rw [harg]
    rw [hrewrite] at h
    exact h
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hempty]

/-! ## Terminal weak-map counts -/

/-- A finite logarithmic binomial bound. This proves the needed factorial
estimate directly, instead of invoking an asymptotic approximation. -/
theorem log_choose_le (N r : ℕ) (hr : 0 < r) (hrN : r ≤ N) :
    Real.log (N.choose r : ℝ) ≤
      (r : ℝ) * (1 + Real.log ((N : ℝ) / (r : ℝ))) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hr hrN)
  have hchoosepos : (0 : ℝ) < N.choose r := by
    exact_mod_cast Nat.choose_pos hrN
  have hfactorial : (r.factorial : ℝ) ≠ 0 := by positivity
  have hlog := Real.log_le_log hchoosepos (Nat.choose_le_pow_div (α := ℝ) r N)
  rw [Real.log_div (pow_pos hNpos r).ne' hfactorial, Real.log_pow] at hlog
  rw [Real.log_div hNpos.ne' hrpos.ne']
  have hfact := log_factorial_lower_bound r
  nlinarith

/-- Analytic stars-and-bars envelope for `r` free labels in known order and
`K` available colours. The combinatorial identification of this binomial as
the number of weakly increasing assignments is independent of this lemma. -/
theorem log_weak_sequence_count_le (K r : ℕ) (hK : 1 ≤ K) :
    Real.log ((K + r - 1).choose r : ℝ) ≤
      (r : ℝ) * (1 + Real.log (1 + (K : ℝ) / (r : ℝ))) := by
  by_cases hrzero : r = 0
  · simp [hrzero]
  · have hr : 0 < r := Nat.pos_of_ne_zero hrzero
    have hrN : r ≤ K + r - 1 := by omega
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
    have hNpos : (0 : ℝ) < (K + r - 1 : ℕ) := by
      exact_mod_cast (lt_of_lt_of_le hr hrN)
    have hNle : ((K + r - 1 : ℕ) : ℝ) ≤ (K : ℝ) + r := by
      exact_mod_cast (Nat.sub_le (K + r) 1)
    have hratio : ((K + r - 1 : ℕ) : ℝ) / r ≤ 1 + (K : ℝ) / r := by
      apply (div_le_iff₀ hrpos).mpr
      have hcancel : (1 + (K : ℝ) / r) * r = (K : ℝ) + r := by
        field_simp [hrpos.ne']
        ring
      rw [hcancel]
      exact hNle
    have hlogs := Real.log_le_log (div_pos hNpos hrpos) hratio
    have hchoose := log_choose_le (K + r - 1) r hr hrN
    nlinarith

/-- Averaging the terminal binomial envelopes costs only the total palette
size. The index set contains the nodes with a positive number of free labels;
nodes with no free labels contribute zero to the terminal log count.
-/
theorem terminal_entropy_average {ι : Type*} (s : Finset ι)
    (free palette : ι → ℝ)
    (hfree : ∀ i ∈ s, 0 < free i)
    (hpalette : ∀ i ∈ s, 0 ≤ palette i) :
    (∑ i ∈ s, free i * (1 + Real.log (1 + palette i / free i))) ≤
      (∑ i ∈ s, free i) *
        (1 + Real.log (1 + (∑ i ∈ s, palette i) / (∑ i ∈ s, free i))) := by
  by_cases hs : s.Nonempty
  · have hP : 0 < ∑ i ∈ s, free i := Finset.sum_pos hfree hs
    have hvalue (i : ι) (hi : i ∈ s) : 0 < 1 + palette i / free i := by
      have h := div_nonneg (hpalette i hi) (hfree i hi).le
      linarith
    have hmean : (∑ i ∈ s, free i * (1 + palette i / free i)) =
        (∑ i ∈ s, free i) + ∑ i ∈ s, palette i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [(hfree i hi).ne']
    have h := weighted_log_le s free (fun i => 1 + palette i / free i) hfree hvalue
    rw [hmean] at h
    have hratio :
        ((∑ i ∈ s, free i) + ∑ i ∈ s, palette i) / (∑ i ∈ s, free i) =
          1 + (∑ i ∈ s, palette i) / (∑ i ∈ s, free i) := by
      field_simp [hP.ne']
    rw [hratio] at h
    have hrewrite :
        (∑ i ∈ s, free i * (1 + Real.log (1 + palette i / free i))) =
          (∑ i ∈ s, free i) +
            ∑ i ∈ s, free i * Real.log (1 + palette i / free i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    rw [hrewrite]
    nlinarith
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hempty]

/-! ## Tree telescoping

Index the root by `0 : Fin (m+1)` and the other nodes by `i.succ`, for
`i : Fin m`. A child's parent is `parent i`. For the algebra below it is enough
that every nonroot node appears once as a child. Acyclicity and the online
meaning of these indices are separate controller invariants.
-/

/-- Sum a child quantity at its parent. -/
def childSum {m : ℕ} (parent : Fin m → Fin (m + 1))
    (f : Fin m → ℝ) (v : Fin (m + 1)) : ℝ :=
  ∑ i : Fin m with parent i = v, f i

/-- Every child quantity is charged at exactly one parent. -/
theorem sum_childSum {m : ℕ} (parent : Fin m → Fin (m + 1))
    (f : Fin m → ℝ) :
    (∑ v : Fin (m + 1), childSum parent f v) = ∑ i : Fin m, f i := by
  classical
  exact Finset.sum_fiberwise Finset.univ parent f

/-- Any node potential telescopes to its root potential when each child
potential is subtracted at its parent. -/
theorem tree_telescope {m : ℕ} (parent : Fin m → Fin (m + 1))
    (potential : Fin (m + 1) → ℝ) :
    (∑ v : Fin (m + 1),
      (potential v - childSum parent (fun i => potential i.succ) v)) =
        potential 0 := by
  rw [Finset.sum_sub_distrib, sum_childSum, Fin.sum_univ_succ]
  ring

/-- The sum of all node populations is the original population plus the
number of parent-to-child admissions, counted with multiplicity. -/
theorem sum_populations_eq_root_add_promotions {m : ℕ}
    (size : Fin (m + 1) → ℝ) :
    (∑ v : Fin (m + 1), size v) = size 0 + ∑ i : Fin m, size i.succ :=
  Fin.sum_univ_succ size

/-- The labels which stop at the various pools sum to the root population. -/
theorem sum_stopping_populations {m : ℕ}
    (parent : Fin m → Fin (m + 1)) (size : Fin (m + 1) → ℝ) :
    (∑ v : Fin (m + 1),
      (size v - childSum parent (fun i => size i.succ) v)) = size 0 :=
  tree_telescope parent size

/-- A finite rooted tree has one fewer edges than nodes. If every node with
fewer than two children retains at least one stopping label, there are at most
`2n-1` nodes for `n` stopping labels. This proves the degree-counting part
without assuming any node-count bound in the hypotheses.
-/
theorem pool_node_count_bound {Node : Type*} [Fintype Node]
    (children stopping : Node → ℕ)
    (hedges : (∑ v, children v) + 1 = Fintype.card Node)
    (hstopping : ∀ v, children v < 2 → 1 ≤ stopping v) :
    Fintype.card Node + 1 ≤ 2 * ∑ v, stopping v := by
  have hlocal (v : Node) : 2 ≤ children v + 2 * stopping v := by
    by_cases hsmall : children v < 2
    · have h := hstopping v hsmall
      omega
    · omega
  have hsum := Finset.sum_le_sum (fun v (_hv : v ∈ Finset.univ) => hlocal v)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at hsum
  omega

/-- Entropy spent separating labels into children is at most the initial
`n log n` potential. The explicit hypotheses say that every nonempty pool has
at least one label and that its children contain at most its population.

This is the manuscript's `H* ≤ n log n`, in natural-log units.
-/
theorem pool_entropy_le_root {m : ℕ}
    (parent : Fin m → Fin (m + 1)) (size : Fin (m + 1) → ℝ)
    (hsize : ∀ v, 1 ≤ size v)
    (hchildren : ∀ v, childSum parent (fun i => size i.succ) v ≤ size v) :
    (∑ i : Fin m, size i.succ * Real.log (size (parent i) / size i.succ)) ≤
      size 0 * Real.log (size 0) := by
  classical
  have hpositive (v : Fin (m + 1)) : 0 < size v := lt_of_lt_of_le zero_lt_one (hsize v)
  have hnode (v : Fin (m + 1)) :
      childSum parent (fun i =>
        size i.succ * Real.log (size (parent i) / size i.succ)) v ≤
      size v * Real.log (size v) -
        childSum parent (fun i => size i.succ * Real.log (size i.succ)) v := by
    have hrewrite :
        childSum parent (fun i =>
          size i.succ * Real.log (size (parent i) / size i.succ)) v =
        childSum parent (fun i => size i.succ) v * Real.log (size v) -
          childSum parent (fun i => size i.succ * Real.log (size i.succ)) v := by
      unfold childSum
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hparent : parent i = v := (Finset.mem_filter.mp hi).2
      dsimp only
      rw [hparent, Real.log_div (hpositive v).ne' (hpositive i.succ).ne']
      ring
    rw [hrewrite]
    exact sub_le_sub_right
      (mul_le_mul_of_nonneg_right (hchildren v) (Real.log_nonneg (hsize v))) _
  calc
    _ = ∑ v : Fin (m + 1), childSum parent (fun i =>
          size i.succ * Real.log (size (parent i) / size i.succ)) v :=
      (sum_childSum parent _).symm
    _ ≤ ∑ v : Fin (m + 1), (size v * Real.log (size v) -
          childSum parent (fun i => size i.succ * Real.log (size i.succ)) v) :=
      Finset.sum_le_sum fun v _hv => hnode v
    _ = _ := tree_telescope parent (fun v => size v * Real.log (size v))

/-! ## Charging promotions to comparisons -/

/-- Once a promotion has an injective witness consisting of a comparison and
one of its two endpoints, there are at most two promotions per comparison.
Constructing that witness for the controller is a separate combinatorial step.
-/
theorem promotion_count_le_twice_comparisons {Promotion Comparison : Type*}
    [Fintype Promotion] [Fintype Comparison]
    (witness : Promotion → Comparison × Bool) (hinj : Function.Injective witness) :
    Fintype.card Promotion ≤ 2 * Fintype.card Comparison := by
  simpa [Nat.mul_comm] using Fintype.card_le_of_injective witness hinj

/-! ## Signed update losses and the comparison clock -/

/-- Logarithmic losses telescope exactly; in particular increases in the
auxiliary count have negative loss and must not be discarded. -/
theorem sum_log_losses (count : ℕ → ℝ) (steps : ℕ) :
    (∑ t ∈ Finset.range steps, (Real.log (count t) - Real.log (count (t + 1)))) =
      Real.log (count 0) - Real.log (count steps) := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- A retained fraction gives an upper bound on the log loss. The fraction
may exceed one, so this also accounts for daughter births and palette growth.
-/
theorem log_loss_le_of_retained_fraction (old new fraction : ℝ)
    (hold : 0 < old) (hfraction : 0 < fraction)
    (hretain : fraction * old ≤ new) :
    Real.log old - Real.log new ≤ -Real.log fraction := by
  have hlog := Real.log_le_log (mul_pos hfraction hold) hretain
  rw [Real.log_mul hfraction.ne' hold.ne'] at hlog
  linarith

/-- Sum any finite sequence of retained-fraction guarantees. This form keeps
all positive and negative accounting contributions in the same telescope. -/
theorem log_loss_le_sum_of_retained_fractions (count fraction : ℕ → ℝ)
    (steps : ℕ) (hcount : ∀ t ≤ steps, 0 < count t)
    (hfraction : ∀ t < steps, 0 < fraction t)
    (hretain : ∀ t < steps, fraction t * count t ≤ count (t + 1)) :
    Real.log (count 0) - Real.log (count steps) ≤
      ∑ t ∈ Finset.range steps, -Real.log (fraction t) := by
  rw [← sum_log_losses]
  exact Finset.sum_le_sum fun t ht =>
    log_loss_le_of_retained_fraction (count t) (count (t + 1)) (fraction t)
      (hcount t (Finset.mem_range.mp ht).le)
      (hfraction t (Finset.mem_range.mp ht)) (hretain t (Finset.mem_range.mp ht))

/-- The finite clock bound from explicit update losses and three separately
stated budgets. `physical` and `cuts` charge comparisons; `pin - birth` is the
signed promotion price. No bound on the complete controller is assumed here.

In the intended application `rate` is `log 2 + O(ε)`, `terminal` is
`O(n log log n)`, and `promotion` is the promotion estimate of the manuscript.
Those estimates still have to be proved for the concrete controller.
-/
theorem clock_bound_of_update_losses
    (count physical cuts pin birth : ℕ → ℝ) (steps q : ℕ)
    (rate terminal promotion : ℝ) (hrate : 0 < rate)
    (hstep : ∀ t < steps,
      Real.log (count t) - Real.log (count (t + 1)) ≤
        physical t + cuts t + pin t - birth t)
    (hphysical : (∑ t ∈ Finset.range steps, (physical t + cuts t)) ≤ rate * q)
    (hpromotion : (∑ t ∈ Finset.range steps, (pin t - birth t)) ≤ promotion)
    (hterminal : Real.log (count steps) ≤ terminal) :
    (Real.log (count 0) - terminal - promotion) / rate ≤ (q : ℝ) := by
  have hloss : Real.log (count 0) - Real.log (count steps) ≤
      (∑ t ∈ Finset.range steps, (physical t + cuts t)) +
        ∑ t ∈ Finset.range steps, (pin t - birth t) := by
    rw [← sum_log_losses, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t ht
    have htstep := hstep t (Finset.mem_range.mp ht)
    linarith
  apply (div_le_iff₀ hrate).mpr
  nlinarith

end SortingAdversary.Optimal.Accounting
