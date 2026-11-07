import SortingAdversary.Optimal.LocalListDPWork
import SortingAdversary.Optimal.RepresentationCells
import SortingAdversary.Optimal.ScaleWalksWork
import SortingAdversary.Optimal.LocalOracle
import SortingAdversary.Optimal.RationalWork

/-!
# Measured preparation and actual local probability queries

The numerical view is evaluated into arrays before the ball or DP is built.
Breadth expansion saturates at the finite carrier size, even if a stage has
a much larger proof radius. The induced carrier is a counted filtered list
of original labels, and all local counts use the measured subset DP.
-/

namespace SortingAdversary.Optimal.MeasuredLocalOracle

open PrimitiveWork WeakMaps LocalChoice GraphBalls BallSchedule RepresentationWork WidthRepair

variable {n K : ℕ} {s : State n}

def prepare (a : LocalAccess s) : Result (LocalDPWork.Input n (s.pool.palette + 1)) :=
  let rows := ClosureWork.tabulate a.active
  let lowers := PrimitiveWork.vector (WindowWork.effectiveLower a.windows)
  let uppers := PrimitiveWork.vector (WindowWork.effectiveUpper a.windows)
  ⟨{ edge := fun x y => ⟨rows.value[x][y], 2⟩
     lower := fun x => ⟨lowers.value[x], 1⟩
     upper := fun x => ⟨uppers.value[x], 1⟩ },
    rows.work + lowers.work + uppers.work + 3⟩

@[simp] theorem prepare_system (a : LocalAccess s) : (prepare a).value.system = s.rows.view := by
  apply Reindexing.system_ext
  · funext x y
    simp [prepare, LocalDPWork.Input.system, ClosureWork.tabulate_value, SparseClosure.tabulate,
      NumericalRepresentation.SourcePartition.view]
  · funext x
    simp [prepare, LocalDPWork.Input.system, WindowWork.effectiveLower_value,
      LocalAccess.windows_system, NumericalRepresentation.SourcePartition.view]
  · funext x
    simp [prepare, LocalDPWork.Input.system, WindowWork.effectiveUpper_value,
      LocalAccess.windows_system, NumericalRepresentation.SourcePartition.view]

theorem prepare_cost (a : LocalAccess s) : (prepare a).value.Cost 2 := by
  constructor
  · intro x y
    exact le_rfl
  · constructor <;> intro x <;> exact Nat.le_succ 1

def prepareBound (n A : ℕ) : ℕ :=
  n * (n * (A + 2) + 2) + 2 * (n * (WindowWork.endpointWorkBound n A A + 2)) + 3

theorem prepare_work (a : LocalAccess s) (A : ℕ) (cost : AccessBound a A) :
    (prepare a).work ≤ prepareBound n A := by
  have hr := ClosureWork.tabulate_work_le a.active A cost.active
  have hl := PrimitiveWork.vector_work_le (WindowWork.effectiveLower a.windows)
    (WindowWork.endpointWorkBound n A A)
    (fun v => WindowWork.effectiveLower_work_le a.windows v A A (fun u => cost.publicRow u v) cost.lower)
  have hu := PrimitiveWork.vector_work_le (WindowWork.effectiveUpper a.windows)
    (WindowWork.endpointWorkBound n A A)
    (fun v => WindowWork.effectiveUpper_work_le a.windows v A A (cost.publicRow v) cost.upper)
  change _ + _ + _ + 3 ≤ _
  unfold prepareBound
  omega

theorem ball_min (E : Fin n → Fin n → Bool) (x : Fin n) (r : ℕ) :
    ball E x (min r n) = ball E x r := by
  by_cases h : r ≤ n
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (Nat.le_of_not_ge h)]
    apply Finset.Subset.antisymm
    · exact ball_mono E x (Nat.le_of_not_ge h)
    · intro y hy
      exact ScaleWalks.connected_mem_ball E x y ⟨r, hy⟩

def labels (data : LocalDPWork.Input n K) (r : ℕ) (x y : Fin n) : Result (List (Fin n)) :=
  let table := ScaleWalksWork.reach data.edge (min r n)
  let domain := FiniteLoopWork.indices n
  let selected := FiniteLoopWork.filter
    (fun z => ⟨table.value[x][z] || table.value[y][z], 5⟩) domain.value
  ⟨selected.value, table.work + domain.work + selected.work + 2⟩

@[simp] theorem labels_value (data : LocalDPWork.Input n K) (r : ℕ) (x y : Fin n) :
    (labels data r x y).value = (List.finRange n).filter (fun z => decide (z ∈ twoBalls data.system.edge x y r)) := by
  simp only [labels, FiniteLoopWork.indices, FiniteLoopWork.filter_value]
  apply congrArg (fun f => (List.finRange n).filter f)
  funext z
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, ScaleWalksWork.reach_true, decide_eq_true_eq, twoBalls, Finset.mem_union]
  change (z ∈ ball data.system.edge x (min r n) ∨ z ∈ ball data.system.edge y (min r n)) ↔ _
  rw [ball_min, ball_min]

theorem labels_nodup (data : LocalDPWork.Input n K) (r : ℕ) (x y : Fin n) :
    (labels data r x y).value.Nodup := by
  rw [labels_value]
  exact (List.nodup_finRange n).filter _

theorem labels_set (data : LocalDPWork.Input n K) (r : ℕ) (x y : Fin n) :
    (labels data r x y).value.toFinset = twoBalls data.system.edge x y r := by
  ext z
  simp [labels_value]

theorem labels_length (data : LocalDPWork.Input n K) (r : ℕ) (x y : Fin n) :
    (labels data r x y).value.length = (twoBalls data.system.edge x y r).card := by
  rw [← labels_set, List.toFinset_card_of_nodup (labels_nodup data r x y)]

def labelsBound (n C : ℕ) : ℕ := ScaleWalksWork.reachBound n n C + 11 * n + 4

theorem labels_work (data : LocalDPWork.Input n K) (C : ℕ) (cost : data.Cost C)
    (r : ℕ) (x y : Fin n) : (labels data r x y).work ≤ labelsBound n C := by
  have ht := (ScaleWalksWork.reach_work data.edge (min r n) C cost.1).trans
    (ScaleWalksWork.reachBound_mono n C (min_le_right r n))
  have hs := FiniteLoopWork.filter_work_le
    (fun z => (⟨(ScaleWalksWork.reach data.edge (min r n)).value[x][z] ||
      (ScaleWalksWork.reach data.edge (min r n)).value[y][z], 5⟩ : Result Bool))
    (List.finRange n) 5 (fun _ _ => le_rfl)
  simp only [List.length_finRange, Nat.reduceAdd] at hs
  change (ScaleWalksWork.reach data.edge (min r n)).work + (3 * n + 1) + _ + 2 ≤ _
  dsimp only [FiniteLoopWork.indices]
  unfold labelsBound
  omega

def addRow (data : LocalDPWork.Input n K) (x y : Fin n) : LocalDPWork.Input n K where
  edge u v := let old := data.edge u v; ⟨old.value || decide (u = x ∧ v = y), old.work + 4⟩
  lower := data.lower
  upper := data.upper

@[simp] theorem addRow_system (data : LocalDPWork.Input n K) (x y : Fin n) :
    (addRow data x y).system = data.system.addRow x y := rfl

theorem addRow_cost (data : LocalDPWork.Input n K) (C : ℕ) (cost : data.Cost C) (x y : Fin n) :
    (addRow data x y).Cost (C + 4) :=
  ⟨fun u v => Nat.add_le_add_right (cost.1 u v) 4,
    fun u => (cost.2.1 u).trans (Nat.le_add_right C 4),
    fun u => (cost.2.2 u).trans (Nat.le_add_right C 4)⟩

def ceiling (data : LocalDPWork.Input n (K + 1)) (x : Fin n) (c : ℕ) : LocalDPWork.Input n (K + 1) where
  edge := data.edge
  lower := data.lower
  upper y :=
    let old := data.upper y
    ⟨if y = x then min old.value ⟨min c K, (min_le_right c K).trans_lt (Nat.lt_succ_self K)⟩ else old.value,
      old.work + 5⟩

@[simp] theorem ceiling_system (data : LocalDPWork.Input n (K + 1)) (x : Fin n) (c : ℕ) :
    (ceiling data x c).system = LocalOracle.ceilingSystem data.system x c := rfl

theorem ceiling_cost (data : LocalDPWork.Input n (K + 1)) (C : ℕ) (cost : data.Cost C) (x : Fin n) (c : ℕ) :
    (ceiling data x c).Cost (C + 5) :=
  ⟨fun u v => (cost.1 u v).trans (Nat.le_add_right C 5),
    fun u => (cost.2.1 u).trans (Nat.le_add_right C 5),
    fun u => Nat.add_le_add_right (cost.2.2 u) 5⟩

def countLabels (data : LocalDPWork.Input n K) (xs : List (Fin n)) : Result ℕ :=
  LocalListDPWork.count xs data.edge data.lower data.upper

theorem countLabels_value (data : LocalDPWork.Input n K) (B : Finset (Fin n))
    (xs : List (Fin n)) (hn : xs.Nodup) (hs : xs.toFinset = B) :
    (countLabels data xs).value = IdealCounting.count (induced data.system B) :=
  LocalListDPWork.count_value data.system B xs hn hs data.edge data.lower data.upper
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

def branchCounts (data : LocalDPWork.Input n K) (r : ℕ) (x y : Fin n) : Result (ℕ × ℕ) :=
  let xs := labels data r x y
  let numerator := countLabels (addRow data x y) xs.value
  let denominator := countLabels data xs.value
  ⟨(numerator.value, denominator.value), xs.work + numerator.work + denominator.work + 3⟩

def branchReference (V : WeakSystem (Fin n) K) (r : ℕ) (x y : Fin n) : ℕ × ℕ :=
  (IdealCounting.count (induced (V.addRow x y) (twoBalls V.edge x y r)),
    IdealCounting.count (induced V (twoBalls V.edge x y r)))

theorem branchCounts_value (data : LocalDPWork.Input n K) (r : ℕ) (x y : Fin n) :
    (branchCounts data r x y).value = branchReference data.system r x y := by
  simp only [branchCounts]
  rw [countLabels_value (addRow data x y) _ _ (labels_nodup data r x y) (labels_set data r x y),
    countLabels_value data _ _ (labels_nodup data r x y) (labels_set data r x y)]
  rfl

def cdfNumerator (data : LocalDPWork.Input n (K + 1)) (xs : List (Fin n)) (x : Fin n) : ℕ → Result ℕ
  | 0 => ⟨0, 1⟩
  | c + 1 =>
    let answer := countLabels (ceiling data x c) xs
    ⟨answer.value, answer.work + 1⟩

def cdfCounts (data : LocalDPWork.Input n (K + 1)) (r : ℕ) (x : Fin n) (cut : ℕ) : Result (ℕ × ℕ) :=
  let xs := labels data r x x
  let numerator := cdfNumerator data xs.value x cut
  let denominator := countLabels data xs.value
  ⟨(numerator.value, denominator.value), xs.work + numerator.work + denominator.work + 3⟩

def cdfReferenceNumerator (V : WeakSystem (Fin n) (K + 1)) (r : ℕ) (x : Fin n) : ℕ → ℕ
  | 0 => 0
  | c + 1 => IdealCounting.count (induced (LocalOracle.ceilingSystem V x c) (ball V.edge x r))

def cdfReference (V : WeakSystem (Fin n) (K + 1)) (r : ℕ) (x : Fin n) (cut : ℕ) : ℕ × ℕ :=
  (cdfReferenceNumerator V r x cut, IdealCounting.count (induced V (ball V.edge x r)))

theorem cdfCounts_value (data : LocalDPWork.Input n (K + 1)) (r : ℕ) (x : Fin n) (cut : ℕ) :
    (cdfCounts data r x cut).value = cdfReference data.system r x cut := by
  have hs : (labels data r x x).value.toFinset = ball data.system.edge x r := by
    simpa [twoBalls] using labels_set data r x x
  cases cut <;>
    simp only [cdfCounts, cdfNumerator, cdfReference, cdfReferenceNumerator]
  · rw [countLabels_value data _ _ (labels_nodup data r x x) hs]
  · rw [countLabels_value _ _ _ (labels_nodup data r x x) hs,
      countLabels_value data _ _ (labels_nodup data r x x) hs]
    rfl

theorem cost_mono (data : LocalDPWork.Input n K) {C D : ℕ} (h : data.Cost C) (hle : C ≤ D) : data.Cost D :=
  ⟨fun x y => (h.1 x y).trans hle, fun x => (h.2.1 x).trans hle, fun x => (h.2.2 x).trans hle⟩

def oneCountBound (n c C : ℕ) : ℕ := 2 * n + LocalDPWork.polynomialBound n c (4 * n + C + 9) + 2

theorem countLabels_work (data : LocalDPWork.Input n K) (C : ℕ) (cost : data.Cost C)
    (xs : List (Fin n)) (c : ℕ) (hn : n ≠ 0) (hb : xs.length ≤ Nat.log 2 n) (hK : K ≤ c * n) :
    (countLabels data xs).work ≤ oneCountBound n c C := by
  have hc := cost_mono data cost (Nat.le_add_right C 5)
  exact LocalListDPWork.count_polynomial xs data.edge data.lower data.upper n c (C + 5)
    hn hb hK hc.1 hc.2.1 hc.2.2

theorem branchCounts_work (data : LocalDPWork.Input n K) (C : ℕ) (cost : data.Cost C)
    (r : ℕ) (x y : Fin n) (c : ℕ) (hn : n ≠ 0)
    (hb : (twoBalls data.system.edge x y r).card ≤ Nat.log 2 n) (hK : K ≤ c * n) :
    (branchCounts data r x y).work ≤ labelsBound n C + 2 * oneCountBound n c (C + 4) + 3 := by
  have hlen : (labels data r x y).value.length ≤ Nat.log 2 n := by rw [labels_length]; exact hb
  have hl := labels_work data C cost r x y
  have hnum := countLabels_work (addRow data x y) (C + 4) (addRow_cost data C cost x y)
    (labels data r x y).value c hn hlen hK
  have hden := countLabels_work data (C + 4) (cost_mono data cost (Nat.le_add_right C 4))
    (labels data r x y).value c hn hlen hK
  change _ + _ + _ + 3 ≤ _
  omega

theorem cdfNumerator_work (data : LocalDPWork.Input n (K + 1)) (C : ℕ) (cost : data.Cost C)
    (xs : List (Fin n)) (x : Fin n) (cut c : ℕ) (hn : n ≠ 0)
    (hb : xs.length ≤ Nat.log 2 n) (hK : K + 1 ≤ c * n) :
    (cdfNumerator data xs x cut).work ≤ oneCountBound n c (C + 5) + 1 := by
  cases cut with
  | zero => exact Nat.le_add_left 1 _
  | succ cut =>
    exact Nat.add_le_add_right (countLabels_work (ceiling data x cut) (C + 5)
      (ceiling_cost data C cost x cut) xs c hn hb hK) 1

theorem cdfCounts_work (data : LocalDPWork.Input n (K + 1)) (C : ℕ) (cost : data.Cost C)
    (r : ℕ) (x : Fin n) (cut c : ℕ) (hn : n ≠ 0)
    (hb : (ball data.system.edge x r).card ≤ Nat.log 2 n) (hK : K + 1 ≤ c * n) :
    (cdfCounts data r x cut).work ≤ labelsBound n C + 2 * oneCountBound n c (C + 5) + 4 := by
  have hlen : (labels data r x x).value.length ≤ Nat.log 2 n := by
    simpa only [labels_length, twoBalls, Finset.union_self] using hb
  have hl := labels_work data C cost r x x
  have hnum := cdfNumerator_work data C cost (labels data r x x).value x cut c hn hlen hK
  have hden := countLabels_work data (C + 5) (cost_mono data cost (Nat.le_add_right C 5))
    (labels data r x x).value c hn hlen hK
  change _ + _ + _ + 3 ≤ _
  omega

def bitBound (n c : ℕ) : ℕ := n * (Nat.log 2 (c * n + 1) + 1) + 1

theorem ideal_count_size (V : WeakSystem (Fin n) K) (B : Finset (Fin n)) (c : ℕ)
    (hK : K ≤ c * n) : Nat.size (IdealCounting.count (induced V B)) ≤ bitBound n c := by
  have hh := IdealCounting.lookup_table_size_le (induced V B) K le_rfl Finset.univ
  simp only [Fintype.card_coe] at hh
  apply hh.trans
  unfold bitBound
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul (show B.card ≤ n by simpa only [Fintype.card_fin] using Finset.card_le_univ B)
  exact Nat.add_le_add_right (Nat.log_mono_right (Nat.add_le_add_right hK 1)) 1

theorem branchCounts_sizes (data : LocalDPWork.Input n K) (r : ℕ) (x y : Fin n) (c : ℕ)
    (hK : K ≤ c * n) : Nat.size (branchCounts data r x y).value.1 ≤ bitBound n c ∧
      Nat.size (branchCounts data r x y).value.2 ≤ bitBound n c := by
  rw [branchCounts_value]
  exact ⟨ideal_count_size _ _ c hK, ideal_count_size _ _ c hK⟩

theorem cdfCounts_sizes (data : LocalDPWork.Input n (K + 1)) (r : ℕ) (x : Fin n) (cut c : ℕ)
    (hK : K + 1 ≤ c * n) : Nat.size (cdfCounts data r x cut).value.1 ≤ bitBound n c ∧
      Nat.size (cdfCounts data r x cut).value.2 ≤ bitBound n c := by
  rw [cdfCounts_value]
  refine ⟨?_, ideal_count_size _ _ c hK⟩
  cases cut with
  | zero => exact Nat.zero_le _
  | succ cut => exact ideal_count_size _ _ c hK

theorem induced_addRow (V : WeakSystem (Fin n) K) (B : Finset (Fin n)) (x y : B) :
    induced (V.addRow x.val y.val) B = (induced V B).addRow x y := by
  apply Reindexing.system_ext
  · funext u v
    simp only [induced, WeakSystem.addRow, Subtype.ext_iff]
  · rfl
  · rfl

theorem induced_ceiling (V : WeakSystem (Fin n) (K + 1)) (B : Finset (Fin n)) (x : B) (cut : ℕ) :
    induced (LocalOracle.ceilingSystem V x.val cut) B = LocalOracle.ceilingSystem (induced V B) x cut := by
  apply Reindexing.system_ext
  · rfl
  · rfl
  · funext u
    simp only [induced, LocalOracle.ceilingSystem, Subtype.ext_iff]

theorem branchReference_ratio (V : WeakSystem (Fin n) (K + 1)) (H d : ℕ) (R ε : ℚ)
    (x y : Fin n) :
    ((branchReference V (H * LocalParameters.sweepCount H (LocalAccuracy.influenceSize H d) R ε) x y).1 : ℚ) /
      (branchReference V (H * LocalParameters.sweepCount H (LocalAccuracy.influenceSize H d) R ε) x y).2 =
      LocalOracle.branchOnBall V H d R ε x y := by
  change (IdealCounting.count (induced (V.addRow x y) (LocalAccuracy.queryBall V H d R ε x y)) : ℚ) /
    IdealCounting.count (induced V (LocalAccuracy.queryBall V H d R ε x y)) =
    (IdealCounting.count ((induced V (LocalAccuracy.queryBall V H d R ε x y)).addRow
      ⟨x, LocalAccuracy.left_mem_queryBall V H d R ε x y⟩
      ⟨y, LocalAccuracy.right_mem_queryBall V H d R ε x y⟩) : ℚ) /
    IdealCounting.count (induced V (LocalAccuracy.queryBall V H d R ε x y))
  rw [induced_addRow V _ ⟨x, LocalAccuracy.left_mem_queryBall V H d R ε x y⟩
    ⟨y, LocalAccuracy.right_mem_queryBall V H d R ε x y⟩]

theorem cdfReference_ratio (V : WeakSystem (Fin n) (K + 1)) (H d : ℕ) (R ε : ℚ)
    (x : Fin n) (cut : ℕ) :
    ((cdfReference V (H * LocalParameters.sweepCount H (LocalAccuracy.influenceSize H d) R ε) x cut).1 : ℚ) /
      (cdfReference V (H * LocalParameters.sweepCount H (LocalAccuracy.influenceSize H d) R ε) x cut).2 =
      LocalOracle.cdfOnBall V H d R ε x cut := by
  cases cut with
  | zero => rfl
  | succ cut =>
    change (IdealCounting.count (induced (LocalOracle.ceilingSystem V x cut) (CDFAccuracy.queryBall V H d R ε x)) : ℚ) /
      IdealCounting.count (induced V (CDFAccuracy.queryBall V H d R ε x)) =
      (IdealCounting.count (LocalOracle.ceilingSystem (induced V (CDFAccuracy.queryBall V H d R ε x))
        ⟨x, CDFAccuracy.mark_mem_queryBall V H d R ε x⟩ cut) : ℚ) /
      IdealCounting.count (induced V (CDFAccuracy.queryBall V H d R ε x))
    rw [induced_ceiling V _ ⟨x, CDFAccuracy.mark_mem_queryBall V H d R ε x⟩ cut]

def branch (a : LocalAccess s) (r : ℕ) (x y : Fin n) : Result ℚ :=
  let data := prepare a
  let counts := branchCounts data.value r x y
  let answer := RationalWork.ratio counts.value.1 counts.value.2
  ⟨answer.value, data.work + counts.work + answer.work + 2⟩

def cdf (a : LocalAccess s) (r : ℕ) (x : Fin n) (cut : ℕ) : Result ℚ :=
  let data := prepare a
  let counts := cdfCounts data.value r x cut
  let answer := RationalWork.ratio counts.value.1 counts.value.2
  ⟨answer.value, data.work + counts.work + answer.work + 2⟩

theorem branch_value (a : LocalAccess s) (H d : ℕ) (R ε : ℚ) (x y : Fin n) :
    (branch a (H * LocalParameters.sweepCount H (LocalAccuracy.influenceSize H d) R ε) x y).value =
      LocalOracle.qBranch s.rows H d R ε x y := by
  simp only [branch, RationalWork.ratio_value, branchCounts_value, prepare_system]
  rw [branchReference_ratio]
  simp only [LocalOracle.qBranch, Materialize.system_eq]

theorem cdf_value (a : LocalAccess s) (H d : ℕ) (R ε : ℚ) (x : Fin n) (cut : ℕ) :
    (cdf a (H * LocalParameters.sweepCount H (LocalAccuracy.influenceSize H d) R ε) x cut).value =
      LocalOracle.qCDF s.rows H d R ε x cut := by
  simp only [cdf, RationalWork.ratio_value, cdfCounts_value, prepare_system]
  rw [cdfReference_ratio]
  simp only [LocalOracle.qCDF, Materialize.system_eq]

def branchBound (n c A : ℕ) : ℕ :=
  prepareBound n A + labelsBound n 2 + 2 * oneCountBound n c 6 + 6 * bitBound n c + 15

def cdfBound (n c A : ℕ) : ℕ :=
  prepareBound n A + labelsBound n 2 + 2 * oneCountBound n c 7 + 6 * bitBound n c + 16

theorem branch_work (a : LocalAccess s) (A : ℕ) (cost : AccessBound a A)
    (r : ℕ) (x y : Fin n) (c : ℕ) (hn : n ≠ 0)
    (hb : (twoBalls s.rows.active x y r).card ≤ Nat.log 2 n) (hK : s.pool.palette + 1 ≤ c * n) :
    (branch a r x y).work ≤ branchBound n c A := by
  have hp := prepare_work a A cost
  have hc := branchCounts_work (prepare a).value 2 (prepare_cost a) r x y c hn
    (by simpa only [prepare_system, NumericalRepresentation.SourcePartition.view] using hb) hK
  simp only [Nat.reduceAdd] at hc
  have hs := branchCounts_sizes (prepare a).value r x y c hK
  have hr := RationalWork.ratio_work_le (branchCounts (prepare a).value r x y).value.1
    (branchCounts (prepare a).value r x y).value.2
  change (prepare a).work + (branchCounts (prepare a).value r x y).work + _ + 2 ≤ _
  unfold branchBound
  omega

theorem cdf_work (a : LocalAccess s) (A : ℕ) (cost : AccessBound a A)
    (r : ℕ) (x : Fin n) (cut c : ℕ) (hn : n ≠ 0)
    (hb : (ball s.rows.active x r).card ≤ Nat.log 2 n) (hK : s.pool.palette + 1 ≤ c * n) :
    (cdf a r x cut).work ≤ cdfBound n c A := by
  have hp := prepare_work a A cost
  have hc := cdfCounts_work (prepare a).value 2 (prepare_cost a) r x cut c hn
    (by simpa only [prepare_system, NumericalRepresentation.SourcePartition.view] using hb) hK
  simp only [Nat.reduceAdd] at hc
  have hs := cdfCounts_sizes (prepare a).value r x cut c hK
  have hr := RationalWork.ratio_work_le (cdfCounts (prepare a).value r x cut).value.1
    (cdfCounts (prepare a).value r x cut).value.2
  change (prepare a).work + (cdfCounts (prepare a).value r x cut).work + _ + 2 ≤ _
  unfold cdfBound
  omega

theorem branch_sizes (a : LocalAccess s) (r : ℕ) (x y : Fin n) (c : ℕ)
    (hK : s.pool.palette + 1 ≤ c * n) :
    Nat.size (branch a r x y).value.num.natAbs ≤ bitBound n c ∧
      Nat.size (branch a r x y).value.den ≤ bitBound n c + 1 := by
  have hs := branchCounts_sizes (prepare a).value r x y c hK
  exact ⟨(RationalWork.ratio_num_size _ _).trans hs.1,
    (RationalWork.ratio_den_size _ _).trans (Nat.add_le_add_right hs.2 1)⟩

theorem cdf_sizes (a : LocalAccess s) (r : ℕ) (x : Fin n) (cut c : ℕ)
    (hK : s.pool.palette + 1 ≤ c * n) :
    Nat.size (cdf a r x cut).value.num.natAbs ≤ bitBound n c ∧
      Nat.size (cdf a r x cut).value.den ≤ bitBound n c + 1 := by
  have hs := cdfCounts_sizes (prepare a).value r x cut c hK
  exact ⟨(RationalWork.ratio_num_size _ _).trans hs.1,
    (RationalWork.ratio_den_size _ _).trans (Nat.add_le_add_right hs.2 1)⟩

theorem bitBound_polynomial (n c : ℕ) : bitBound n c ≤ n * (c * n + 2) + 1 := by
  have hh := Nat.log_le_self 2 (c * n + 1)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left n (Nat.add_le_add_right hh 1)) 1

end SortingAdversary.Optimal.MeasuredLocalOracle
