import SortingAdversary.Optimal.LocalOracle

/-!
# Work and integer storage of the actual local dynamic programs

The instrumented routines below execute the same materialized tables as the
local oracles. Their counters measure candidate transition and stored-row
visits, exactly as in `IdealCounting`. Under the logarithmic ball cap and a
linear palette cap these visits have a uniform polynomial bound. Evaluating
an arbitrary input function is not silently charged as a constant-time
operation; graph construction and the representation of stored rows remain
separate costs.
-/

namespace SortingAdversary.Optimal.LocalOracleWork

open WeakMaps WeakMaps.WeakSystem LocalChoice LocalOracle
open NumericalRepresentation

/-- Bound for one materialized finite DP with `b` labels and `K` colors. -/
def countWorkBound (b K : ℕ) : ℕ :=
  2 * 2 ^ b + K * (2 ^ b + 3 ^ b * (1 + 2 ^ b))

/-- The uniform polynomial obtained once `b≤log₂N` and `K≤cN`. -/
def polynomialBound (N c : ℕ) : ℕ :=
  2 * N + c * N * (N + N ^ 2 * (1 + N))

section Counting

variable {α : Type*} [Fintype α] [DecidableEq α] {K : ℕ}

/-- Instrumentation of both actual weak-branch ratio counts. -/
def branchWithWork (S : WeakSystem α K) (x y : α) : ℚ × ℕ :=
  let numerator := IdealCounting.countWithWork (S.addRow x y)
  let denominator := IdealCounting.countWithWork S
  ((numerator.1 : ℚ) / denominator.1, numerator.2 + denominator.2)

theorem branchWithWork_fst (S : WeakSystem α K) (x y : α) :
    (branchWithWork S x y).1 = branchEstimate S x y := by
  simp only [branchWithWork, IdealCounting.countWithWork_fst, branchEstimate, IdealCounting.count_eq]

theorem branchWithWork_le (S : WeakSystem α K) (x y : α) :
    (branchWithWork S x y).2 ≤ 2 * countWorkBound (Fintype.card α) K := by
  have hn := IdealCounting.countWithWork_le (S.addRow x y)
  have hd := IdealCounting.countWithWork_le S
  change _ + _ ≤ _
  exact (Nat.add_le_add hn hd).trans_eq (by unfold countWorkBound; ring)

theorem branchWithWork_polynomial (S : WeakSystem α K) (x y : α) (N c : ℕ) (hN : N ≠ 0)
    (hb : Fintype.card α ≤ Nat.log 2 N) (hK : K ≤ c * N) :
    (branchWithWork S x y).2 ≤ 2 * polynomialBound N c := by
  have hn := IdealCounting.countWithWork_polynomial (S.addRow x y) N c hN hb hK
  have hd := IdealCounting.countWithWork_polynomial S N c hN hb hK
  change _ + _ ≤ _
  exact (Nat.add_le_add hn hd).trans_eq (by unfold polynomialBound; ring)

def cdfCountWithWork (S : WeakSystem α (K + 1)) (x : α) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | c + 1 => IdealCounting.countWithWork (ceilingSystem S x c)

theorem cdfCountWithWork_fst (S : WeakSystem α (K + 1)) (x : α) (cut : ℕ) :
    (cdfCountWithWork S x cut).1 = cdfCount S x cut := by
  cases cut <;> simp only [cdfCountWithWork, cdfCount, IdealCounting.countWithWork_fst,
    IdealCounting.count_eq]

theorem cdfCountWithWork_le (S : WeakSystem α (K + 1)) (x : α) (cut : ℕ) :
    (cdfCountWithWork S x cut).2 ≤ countWorkBound (Fintype.card α) (K + 1) := by
  cases cut with
  | zero => exact Nat.zero_le _
  | succ c => exact IdealCounting.countWithWork_le (ceilingSystem S x c)

theorem cdfCountWithWork_polynomial (S : WeakSystem α (K + 1)) (x : α) (cut N c : ℕ)
    (hN : N ≠ 0) (hb : Fintype.card α ≤ Nat.log 2 N) (hK : K + 1 ≤ c * N) :
    (cdfCountWithWork S x cut).2 ≤ polynomialBound N c := by
  cases cut with
  | zero => exact Nat.zero_le _
  | succ k => exact IdealCounting.countWithWork_polynomial (ceilingSystem S x k) N c hN hb hK

/-- Instrumentation of the actual exclusive-CDF numerator and denominator. -/
def cdfWithWork (S : WeakSystem α (K + 1)) (x : α) (cut : ℕ) : ℚ × ℕ :=
  let numerator := cdfCountWithWork S x cut
  let denominator := IdealCounting.countWithWork S
  ((numerator.1 : ℚ) / denominator.1, numerator.2 + denominator.2)

theorem cdfWithWork_fst (S : WeakSystem α (K + 1)) (x : α) (cut : ℕ) :
    (cdfWithWork S x cut).1 = cdfEstimate S x cut := by
  simp only [cdfWithWork, cdfCountWithWork_fst, IdealCounting.countWithWork_fst,
    cdfEstimate, IdealCounting.count_eq]

theorem cdfWithWork_le (S : WeakSystem α (K + 1)) (x : α) (cut : ℕ) :
    (cdfWithWork S x cut).2 ≤ 2 * countWorkBound (Fintype.card α) (K + 1) := by
  have hn := cdfCountWithWork_le S x cut
  have hd := IdealCounting.countWithWork_le S
  change _ + _ ≤ _
  exact (Nat.add_le_add hn hd).trans_eq (by unfold countWorkBound; ring)

theorem cdfWithWork_polynomial (S : WeakSystem α (K + 1)) (x : α) (cut N c : ℕ) (hN : N ≠ 0)
    (hb : Fintype.card α ≤ Nat.log 2 N) (hK : K + 1 ≤ c * N) :
    (cdfWithWork S x cut).2 ≤ 2 * polynomialBound N c := by
  have hn := cdfCountWithWork_polynomial S x cut N c hN hb hK
  have hd := IdealCounting.countWithWork_polynomial S N c hN hb hK
  change _ + _ ≤ _
  exact (Nat.add_le_add hn hd).trans_eq (by unfold polynomialBound; ring)

/-- Each actual DP count, including queried-event numerators, fits the same
binary bound as its materialized terminal table entry. -/
theorem count_size (S : WeakSystem α K) :
    Nat.size (IdealCounting.count S) ≤ Fintype.card α * (Nat.log 2 (K + 1) + 1) + 1 :=
  IdealCounting.lookup_table_size_le S K le_rfl Finset.univ

theorem count_size_logCap (S : WeakSystem α K) (N c : ℕ)
    (hb : Fintype.card α ≤ Nat.log 2 N) (hK : K ≤ c * N) :
    Nat.size (IdealCounting.count S) ≤ Nat.log 2 N * (Nat.log 2 (c * N + 1) + 1) + 1 :=
  IdealCounting.lookup_table_size_logCap S K le_rfl Finset.univ N c hb hK

theorem branch_integer_sizes (S : WeakSystem α K) (x y : α) (N c : ℕ)
    (hb : Fintype.card α ≤ Nat.log 2 N) (hK : K ≤ c * N) :
    Nat.size (IdealCounting.count (S.addRow x y)) ≤
        Nat.log 2 N * (Nat.log 2 (c * N + 1) + 1) + 1 ∧
      Nat.size (IdealCounting.count S) ≤
        Nat.log 2 N * (Nat.log 2 (c * N + 1) + 1) + 1 :=
  ⟨count_size_logCap _ N c hb hK, count_size_logCap _ N c hb hK⟩

theorem cdf_integer_sizes (S : WeakSystem α (K + 1)) (x : α) (cut N c : ℕ)
    (hb : Fintype.card α ≤ Nat.log 2 N) (hK : K + 1 ≤ c * N) :
    Nat.size (cdfCount S x cut) ≤ Nat.log 2 N * (Nat.log 2 (c * N + 1) + 1) + 1 ∧
      Nat.size (IdealCounting.count S) ≤
        Nat.log 2 N * (Nat.log 2 (c * N + 1) + 1) + 1 := by
  refine ⟨?_, count_size_logCap _ N c hb hK⟩
  cases cut with
  | zero => simp [cdfCount]
  | succ k => exact count_size_logCap (ceilingSystem S x k) N c hb hK

end Counting

variable {n K : ℕ} {S : WeakSystem (Fin n) (K + 1)}
variable {pins : Fin n → Option (Fin (K + 1))}

def branchOnBallWithWork (V : WeakSystem (Fin n) (K + 1)) (H d : ℕ) (R ε : ℚ)
    (x y : Fin n) : ℚ × ℕ :=
  branchWithWork (induced V (LocalAccuracy.queryBall V H d R ε x y))
    ⟨x, LocalAccuracy.left_mem_queryBall V H d R ε x y⟩
    ⟨y, LocalAccuracy.right_mem_queryBall V H d R ε x y⟩

/-- Measured execution of the unchanged actual comparison oracle. -/
def qBranchWithWork (P : SourcePartition S pins) (H d : ℕ) (R ε : ℚ) (x y : Fin n) : ℚ × ℕ :=
  let V := Materialize.system P.view
  branchOnBallWithWork V H d R ε x y

theorem qBranchWithWork_fst (P : SourcePartition S pins) (H d : ℕ) (R ε : ℚ) (x y : Fin n) :
    (qBranchWithWork P H d R ε x y).1 = qBranch P H d R ε x y := branchWithWork_fst _ _ _

theorem qBranchWithWork_le (P : SourcePartition S pins) (H d : ℕ) (R ε : ℚ) (x y : Fin n) :
    (qBranchWithWork P H d R ε x y).2 ≤
      2 * countWorkBound (LocalAccuracy.queryBall P.view H d R ε x y).card (K + 1) := by
  change (branchOnBallWithWork (Materialize.system P.view) H d R ε x y).2 ≤ _
  rw [Materialize.system_eq]
  simpa only [branchOnBallWithWork, Fintype.card_coe] using branchWithWork_le
    (induced P.view (LocalAccuracy.queryBall P.view H d R ε x y))
    ⟨x, LocalAccuracy.left_mem_queryBall P.view H d R ε x y⟩
    ⟨y, LocalAccuracy.right_mem_queryBall P.view H d R ε x y⟩

/-- The stage cap controls actual inspected labels, not a merely postulated
operation count. Under that cap this exact DP execution is polynomial. -/
theorem qBranchWithWork_polynomial (P : SourcePartition S pins) (H d : ℕ) (R ε : ℚ)
    (x y : Fin n) (N c : ℕ) (hN : N ≠ 0)
    (hb : (LocalAccuracy.queryBall P.view H d R ε x y).card ≤ Nat.log 2 N)
    (hK : K + 1 ≤ c * N) :
    (qBranchWithWork P H d R ε x y).2 ≤ 2 * polynomialBound N c := by
  change (branchOnBallWithWork (Materialize.system P.view) H d R ε x y).2 ≤ _
  rw [Materialize.system_eq]
  apply branchWithWork_polynomial _ _ _ N c hN _ hK
  simpa only [Fintype.card_coe] using hb

def cdfOnBallWithWork (V : WeakSystem (Fin n) (K + 1)) (H d : ℕ) (R ε : ℚ)
    (x : Fin n) (cut : ℕ) : ℚ × ℕ :=
  cdfWithWork (induced V (CDFAccuracy.queryBall V H d R ε x))
    ⟨x, CDFAccuracy.mark_mem_queryBall V H d R ε x⟩ cut

def qCDFWithWork (P : SourcePartition S pins) (H d : ℕ) (R ε : ℚ) (x : Fin n) (cut : ℕ) : ℚ × ℕ :=
  let V := Materialize.system P.view
  cdfOnBallWithWork V H d R ε x cut

theorem qCDFWithWork_fst (P : SourcePartition S pins) (H d : ℕ) (R ε : ℚ) (x : Fin n) (cut : ℕ) :
    (qCDFWithWork P H d R ε x cut).1 = qCDF P H d R ε x cut := cdfWithWork_fst _ _ _

theorem qCDFWithWork_le (P : SourcePartition S pins) (H d : ℕ) (R ε : ℚ) (x : Fin n) (cut : ℕ) :
    (qCDFWithWork P H d R ε x cut).2 ≤
      2 * countWorkBound (CDFAccuracy.queryBall P.view H d R ε x).card (K + 1) := by
  change (cdfOnBallWithWork (Materialize.system P.view) H d R ε x cut).2 ≤ _
  rw [Materialize.system_eq]
  simpa only [cdfOnBallWithWork, Fintype.card_coe] using cdfWithWork_le
    (induced P.view (CDFAccuracy.queryBall P.view H d R ε x))
    ⟨x, CDFAccuracy.mark_mem_queryBall P.view H d R ε x⟩ cut

theorem qCDFWithWork_polynomial (P : SourcePartition S pins) (H d : ℕ) (R ε : ℚ)
    (x : Fin n) (cut N c : ℕ) (hN : N ≠ 0)
    (hb : (CDFAccuracy.queryBall P.view H d R ε x).card ≤ Nat.log 2 N)
    (hK : K + 1 ≤ c * N) :
    (qCDFWithWork P H d R ε x cut).2 ≤ 2 * polynomialBound N c := by
  change (cdfOnBallWithWork (Materialize.system P.view) H d R ε x cut).2 ≤ _
  rw [Materialize.system_eq]
  apply cdfWithWork_polynomial _ _ _ N c hN _ hK
  simpa only [Fintype.card_coe] using hb

/-- The finite scalar comparison-ball allowance used by the stage selector. -/
def comparisonBallBound (H d : ℕ) (R ε : ℚ) : ℕ :=
  2 * (d + 1) ^ (H * LocalParameters.sweepCount H (LocalAccuracy.influenceSize H d) R ε)

def cdfBallBound (H d : ℕ) (R ε : ℚ) : ℕ :=
  (d + 1) ^ (H * LocalParameters.sweepCount H (LocalAccuracy.influenceSize H d) R ε)

/-- The actual graph-cardinality premise is discharged by degree and the
computed radius allowance. This is the direct stage-budget interface. -/
theorem comparison_work_of_radius_cap (P : SourcePartition S pins) (H d : ℕ)
    (g : SparseBounds P H d) (R ε : ℚ) (x y : Fin n) (N c : ℕ) (hN : N ≠ 0)
    (hball : comparisonBallBound H d R ε ≤ Nat.log 2 N) (hK : K + 1 ≤ c * N) :
    (qBranchWithWork P H d R ε x y).2 ≤ 2 * polynomialBound N c := by
  apply qBranchWithWork_polynomial P H d R ε x y N c hN _ hK
  exact (LocalAccuracy.queryBall_card P.view H d R ε g.degree x y).trans hball

theorem cdf_work_of_radius_cap (P : SourcePartition S pins) (H d : ℕ)
    (g : SparseBounds P H d) (R ε : ℚ) (x : Fin n) (cut N c : ℕ) (hN : N ≠ 0)
    (hball : cdfBallBound H d R ε ≤ Nat.log 2 N) (hK : K + 1 ≤ c * N) :
    (qCDFWithWork P H d R ε x cut).2 ≤ 2 * polynomialBound N c := by
  apply qCDFWithWork_polynomial P H d R ε x cut N c hN _ hK
  exact (CDFAccuracy.queryBall_card P.view H d R ε g.degree x).trans hball

/-- All counts used in either local weak child obey the same binary bound.
The same theorem applies after swapping the two query labels. -/
theorem local_branch_integer_sizes (P : SourcePartition S pins) (H d : ℕ) (R ε : ℚ)
    (x y : Fin n) (N c : ℕ)
    (hb : (LocalAccuracy.queryBall P.view H d R ε x y).card ≤ Nat.log 2 N)
    (hK : K + 1 ≤ c * N) :
    let T := induced P.view (LocalAccuracy.queryBall P.view H d R ε x y)
    let a : ↥(LocalAccuracy.queryBall P.view H d R ε x y) :=
      ⟨x, LocalAccuracy.left_mem_queryBall P.view H d R ε x y⟩
    let b : ↥(LocalAccuracy.queryBall P.view H d R ε x y) :=
      ⟨y, LocalAccuracy.right_mem_queryBall P.view H d R ε x y⟩
    Nat.size (IdealCounting.count (T.addRow a b)) ≤
        Nat.log 2 N * (Nat.log 2 (c * N + 1) + 1) + 1 ∧
      Nat.size (IdealCounting.count T) ≤
        Nat.log 2 N * (Nat.log 2 (c * N + 1) + 1) + 1 := by
  apply branch_integer_sizes _ _ _ N c _ hK
  simpa only [Fintype.card_coe] using hb

theorem local_cdf_integer_sizes (P : SourcePartition S pins) (H d : ℕ) (R ε : ℚ)
    (x : Fin n) (cut N c : ℕ)
    (hb : (CDFAccuracy.queryBall P.view H d R ε x).card ≤ Nat.log 2 N)
    (hK : K + 1 ≤ c * N) :
    let T := induced P.view (CDFAccuracy.queryBall P.view H d R ε x)
    let a : ↥(CDFAccuracy.queryBall P.view H d R ε x) :=
      ⟨x, CDFAccuracy.mark_mem_queryBall P.view H d R ε x⟩
    Nat.size (cdfCount T a cut) ≤ Nat.log 2 N * (Nat.log 2 (c * N + 1) + 1) + 1 ∧
      Nat.size (IdealCounting.count T) ≤
        Nat.log 2 N * (Nat.log 2 (c * N + 1) + 1) + 1 := by
  apply cdf_integer_sizes _ _ _ N c _ hK
  simpa only [Fintype.card_coe] using hb

end SortingAdversary.Optimal.LocalOracleWork
