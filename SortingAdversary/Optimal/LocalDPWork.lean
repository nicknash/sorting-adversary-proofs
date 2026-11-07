import SortingAdversary.Optimal.SubsetWork
import SortingAdversary.Optimal.Reindexing

/-!
# Primitive-work accounting for exact local ideal counting

This implementation stores subsets as Boolean arrays and palette layers as
lists of subset/count pairs. Each target state scans the previous materialized
layer once, including every raw-row and interval test. Thus no table lookup
recomputes an earlier layer. The output agrees with `IdealCounting.count`.

The work model charges input callbacks explicitly, as well as subset
generation, array reads, label scans, comparisons, branches and additions.
Arithmetic operations are counted as word operations; proved count-bit bounds
permit their separate translation into bit operations.
-/

namespace SortingAdversary.Optimal.LocalDPWork

open scoped BigOperators
open PrimitiveWork SubsetWork WeakMaps

variable {b K : ℕ}

structure Input (b K : ℕ) where
  edge : Fin b → Fin b → Result Bool
  lower : Fin b → Result (Fin K)
  upper : Fin b → Result (Fin K)

def Input.system (data : Input b K) : WeakSystem (Fin b) K where
  edge x y := (data.edge x y).value
  lower x := (data.lower x).value
  upper x := (data.upper x).value

def Input.Cost (data : Input b K) (C : ℕ) : Prop :=
  (∀ x y, (data.edge x y).work ≤ C) ∧
  (∀ x, (data.lower x).work ≤ C) ∧ (∀ x, (data.upper x).work ≤ C)

def subset (I J : Mask b) : Result Bool :=
  allFin (fun x => ⟨decide (I[x] = true → J[x] = true), 3⟩)

@[simp] theorem subset_true (I J : Mask b) :
    (subset I J).value = true ↔ asSet I ⊆ asSet J := by
  simp only [subset, allFin_true, decide_eq_true_eq, Finset.subset_iff, mem_asSet]

def ideal (data : Input b K) (J : Mask b) : Result Bool :=
  allFin (fun u => allFin (fun v =>
    let row := data.edge u v
    ⟨decide (row.value = true → J[v] = true → J[u] = true), row.work + 4⟩))

@[simp] theorem ideal_true (data : Input b K) (J : Mask b) :
    (ideal data J).value = true ↔ IdealCounting.IsIdeal data.system (asSet J) := by
  simp only [ideal, allFin_true, decide_eq_true_eq, IdealCounting.IsIdeal, Input.system, mem_asSet]

def future (data : Input b K) (k : ℕ) (J : Mask b) : Result Bool :=
  allFin (fun x =>
    let lo := data.lower x
    ⟨decide (J[x] = true → lo.value.val < k), lo.work + 3⟩)

def expired (data : Input b K) (k : ℕ) (J : Mask b) : Result Bool :=
  allFin (fun x =>
    let hi := data.upper x
    ⟨decide (J[x] ≠ true → k ≤ hi.value.val), hi.work + 3⟩)

def fresh (data : Input b K) (k : ℕ) (I J : Mask b) : Result Bool :=
  allFin (fun x =>
    let lo := data.lower x
    let hi := data.upper x
    ⟨decide (J[x] = true → I[x] ≠ true → lo.value.val ≤ k ∧ k ≤ hi.value.val), lo.work + hi.work + 7⟩)

def allowed (data : Input b K) (k : ℕ) (I J : Mask b) : Result Bool :=
  let contained := subset I J
  let closed := ideal data J
  let begun := future data (k + 1) J
  let unexpired := expired data (k + 1) J
  let block := fresh data k I J
  ⟨contained.value && closed.value && begun.value && unexpired.value && block.value,
    contained.work + closed.work + begun.work + unexpired.work + block.work + 5⟩

@[simp] theorem allowed_true (data : Input b K) (k : ℕ) (I J : Mask b) :
    (allowed data k I J).value = true ↔ IdealCounting.AllowedStep data.system k (asSet I) (asSet J) := by
  simp only [allowed, Bool.and_eq_true, subset_true, ideal_true, future, expired, fresh,
    allFin_true, decide_eq_true_eq, IdealCounting.AllowedStep, IdealCounting.Admissible,
    Input.system, mem_asSet]
  tauto

def predicateBound (b C : ℕ) : ℕ := b * (b * (C + 10) + 10) + 4 * b * (2 * C + 20) + 30

theorem allowed_work (data : Input b K) (C : ℕ) (cost : data.Cost C) (k : ℕ) (I J : Mask b) :
    (allowed data k I J).work ≤ predicateBound b C := by
  have hsub : (subset I J).work ≤ b * 9 + 4 := allFin_work _ 3 (fun _ => le_rfl)
  have hi (u : Fin b) :
      (allFin (fun v => (⟨decide ((data.edge u v).value = true → J[v] = true → J[u] = true),
        (data.edge u v).work + 4⟩ : Result Bool))).work ≤ b * (C + 10) + 4 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using allFin_work _ (C + 4)
      (fun v => Nat.add_le_add_right (cost.1 u v) 4)
  have hideal : (ideal data J).work ≤ b * (b * (C + 10) + 10) + 4 := by
    unfold ideal
    simpa only [Nat.add_assoc, Nat.reduceAdd] using allFin_work _ (b * (C + 10) + 4) hi
  have hfuture : (future data (k + 1) J).work ≤ b * (C + 9) + 4 := by
    unfold future
    simpa only [Nat.add_assoc, Nat.reduceAdd] using allFin_work _ (C + 3)
      (fun x => Nat.add_le_add_right (cost.2.1 x) 3)
  have hexpired : (expired data (k + 1) J).work ≤ b * (C + 9) + 4 := by
    unfold expired
    simpa only [Nat.add_assoc, Nat.reduceAdd] using allFin_work _ (C + 3)
      (fun x => Nat.add_le_add_right (cost.2.2 x) 3)
  have hfresh : (fresh data k I J).work ≤ b * (2 * C + 13) + 4 := by
    have hc (x : Fin b) : (data.lower x).work + (data.upper x).work + 7 ≤ 2 * C + 7 := by
      have hl := cost.2.1 x
      have hu := cost.2.2 x
      omega
    unfold fresh
    simpa only [Nat.add_assoc, Nat.reduceAdd] using allFin_work _ (2 * C + 7) hc
  change (subset I J).work + (ideal data J).work + (future data (k + 1) J).work +
    (expired data (k + 1) J).work + (fresh data k I J).work + 5 ≤ _
  unfold predicateBound
  nlinarith

abbrev Table (b : ℕ) := List (Mask b × ℕ)

def stepSum (data : Input b K) (k : ℕ) (J : Mask b) : Table b → Result ℕ
  | [] => ⟨0, 1⟩
  | (I, value) :: rest =>
    let accept := allowed data k I J
    let tail := stepSum data k J rest
    ⟨(if accept.value then value else 0) + tail.value, accept.work + tail.work + 3⟩

@[simp] theorem stepSum_value (data : Input b K) (k : ℕ) (J : Mask b) (old : Table b) :
    (stepSum data k J old).value =
      (old.map (fun p => if IdealCounting.AllowedStep data.system k (asSet p.1) (asSet J) then p.2 else 0)).sum := by
  induction old with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨I, value⟩
    simp only [stepSum, List.map_cons, List.sum_cons, ih]
    simp only [allowed_true]

theorem stepSum_work (data : Input b K) (C : ℕ) (cost : data.Cost C) (k : ℕ) (J : Mask b) (old : Table b) :
    (stepSum data k J old).work ≤ old.length * (predicateBound b C + 3) + 1 := by
  induction old with
  | nil => simp [stepSum]
  | cons p rest ih =>
    have ha := allowed_work data C cost k p.1 J
    rcases p with ⟨I, value⟩
    dsimp only at ha
    simp only [stepSum, List.length_cons, Nat.add_mul, one_mul]
    omega

def initial (masks : List (Mask b)) : Result (Table b) :=
  PrimitiveWork.map (fun I =>
    let test := empty I
    ⟨(I, if test.value then 1 else 0), test.work + 2⟩) masks

def step (data : Input b K) (k : ℕ) (masks : List (Mask b)) (old : Table b) : Result (Table b) :=
  PrimitiveWork.map (fun J =>
    let value := stepSum data k J old
    ⟨(J, value.value), value.work + 1⟩) masks

def table (data : Input b K) (masks : List (Mask b)) : ℕ → Result (Table b)
  | 0 => initial masks
  | k + 1 =>
    let old := table data masks k
    let next := step data k masks old.value
    ⟨next.value, old.work + next.work + 1⟩

@[simp] theorem table_length (data : Input b K) (masks : List (Mask b)) (k : ℕ) :
    (table data masks k).value.length = masks.length := by
  cases k <;> simp [table, initial, step]

theorem full_predecessor_sum (S : WeakSystem (Fin b) K) (k : ℕ) (J : Finset (Fin b))
    (value : Finset (Fin b) → ℕ) :
    (∑ I : Finset (Fin b), if IdealCounting.AllowedStep S k I J then value I else 0) =
      ∑ I ∈ J.powerset, if IdealCounting.AllowedStep S k I J then value I else 0 := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro I _ hI
  have hn : ¬ IdealCounting.AllowedStep S k I J := fun hs => hI (Finset.mem_powerset.mpr hs.1)
  simp [hn]

theorem table_value (data : Input b K) (k : ℕ) :
    (table data (enumerate b).value k).value = (enumerate b).value.map
      (fun I => (I, IdealCounting.lookup (IdealCounting.table data.system k) (asSet I))) := by
  induction k with
  | zero =>
    simp only [table, initial, PrimitiveWork.map_value, IdealCounting.table, IdealCounting.lookup_tabulate]
    apply List.map_congr_left
    intro I _
    simp only [empty_true]
  | succ k ih =>
    simp only [table, step, PrimitiveWork.map_value, ih, stepSum_value, List.map_map,
      IdealCounting.table, IdealCounting.lookup_tabulate]
    apply List.map_congr_left
    intro J _
    congr 1
    change ((enumerate b).value.map (fun I => if IdealCounting.AllowedStep data.system k (asSet I) (asSet J)
      then IdealCounting.lookup (IdealCounting.table data.system k) (asSet I) else 0)).sum = _
    exact (sum_enumerate b (fun I => if IdealCounting.AllowedStep data.system k I (asSet J)
      then IdealCounting.lookup (IdealCounting.table data.system k) I else 0)).trans
      (full_predecessor_sum data.system k (asSet J) (IdealCounting.lookup (IdealCounting.table data.system k)))

def baseBound (b N : ℕ) : ℕ := N * (8 * b + 8) + 1
def layerBound (b C N : ℕ) : ℕ := N * (N * (predicateBound b C + 3) + 4) + 2

theorem initial_work (masks : List (Mask b)) :
    (initial masks).work ≤ baseBound b masks.length := by
  have hh := PrimitiveWork.map_work_le (fun I : Mask b =>
    (⟨(I, if (empty I).value then 1 else 0), (empty I).work + 2⟩ : Result (Mask b × ℕ)))
    masks (8 * b + 6) (fun I _ => by dsimp only; have hi := empty_work I; omega)
  exact hh

theorem step_work (data : Input b K) (C : ℕ) (cost : data.Cost C) (k : ℕ)
    (masks : List (Mask b)) (old : Table b) (hlen : old.length = masks.length) :
    (step data k masks old).work + 1 ≤ layerBound b C masks.length := by
  have hc (J : Mask b) : (stepSum data k J old).work + 1 ≤ masks.length * (predicateBound b C + 3) + 2 := by
    have hh := stepSum_work data C cost k J old
    rw [hlen] at hh
    omega
  have hh := PrimitiveWork.map_work_le (fun J : Mask b =>
    (⟨(J, (stepSum data k J old).value), (stepSum data k J old).work + 1⟩ : Result (Mask b × ℕ)))
    masks (masks.length * (predicateBound b C + 3) + 2) (fun J _ => hc J)
  exact Nat.add_le_add_right hh 1

theorem table_work (data : Input b K) (C : ℕ) (cost : data.Cost C)
    (masks : List (Mask b)) (k : ℕ) :
    (table data masks k).work ≤ baseBound b masks.length + k * layerBound b C masks.length := by
  induction k with
  | zero => simpa only [table, Nat.zero_mul, Nat.add_zero] using initial_work masks
  | succ k ih =>
    have hn := step_work data C cost k masks (table data masks k).value (table_length data masks k)
    change (table data masks k).work + (step data k masks (table data masks k).value).work + 1 ≤ _
    rw [Nat.add_mul, one_mul]
    omega

def read (target : Mask b) : Table b → Result ℕ
  | [] => ⟨0, 1⟩
  | (I, value) :: rest =>
    let test := equal I target
    let tail := read target rest
    ⟨(if test.value then value else 0) + tail.value, test.work + tail.work + 3⟩

@[simp] theorem read_value (target : Mask b) (entries : Table b) :
    (read target entries).value = (entries.map (fun p => if p.1 = target then p.2 else 0)).sum := by
  induction entries with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨I, value⟩
    simp only [read, List.map_cons, List.sum_cons, equal_true, ih]

theorem read_work (target : Mask b) (entries : Table b) :
    (read target entries).work ≤ entries.length * (9 * b + 7) + 1 := by
  induction entries with
  | nil => simp [read]
  | cons p rest ih =>
    rcases p with ⟨I, value⟩
    have hh := equal_work I target
    simp only [read, List.length_cons, Nat.add_mul, one_mul]
    omega

theorem read_tabulate (target : Mask b) (value : Finset (Fin b) → ℕ) :
    (read target ((enumerate b).value.map (fun I => (I, value (asSet I))))).value = value (asSet target) := by
  rw [read_value]
  simp only [List.map_map, Function.comp_def]
  have heq (I : Mask b) : I = target ↔ asSet I = asSet target :=
    ⟨congrArg asSet, fun h => asSet_injective h⟩
  simp only [heq]
  have hh := sum_enumerate b (fun I => if I = asSet target then value I else 0)
  exact hh.trans (by simp)

def full (b : ℕ) : Result (Mask b) := ⟨Vector.replicate b true, 3 * b + 1⟩

@[simp] theorem full_set (b : ℕ) : asSet (full b).value = Finset.univ := by
  ext x
  simp [full]

/-- Count one local system. The mask enumeration is computed once and shared
by every materialized palette layer. -/
def count (data : Input b K) : Result ℕ :=
  let masks := enumerate b
  let final := table data masks.value K
  let target := full b
  let answer := read target.value final.value
  ⟨answer.value, masks.work + final.work + target.work + answer.work + 3⟩

@[simp] theorem count_value (data : Input b K) : (count data).value = IdealCounting.count data.system := by
  simp only [count, table_value, read_tabulate, full_set, IdealCounting.count]

theorem count_eq (data : Input b K) : (count data).value = data.system.count :=
  (count_value data).trans (IdealCounting.count_eq data.system)

def countBound (b K C : ℕ) : ℕ :=
  enumerationBound b + baseBound b (2 ^ b) + K * layerBound b C (2 ^ b) +
    3 * b + (2 ^ b) * (9 * b + 7) + 5

theorem count_work (data : Input b K) (C : ℕ) (cost : data.Cost C) :
    (count data).work ≤ countBound b K C := by
  have he := enumerate_work b
  have ht := table_work data C cost (enumerate b).value K
  rw [enumerate_length] at ht
  have hr := read_work (full b).value (table data (enumerate b).value K).value
  rw [table_length, enumerate_length] at hr
  change (enumerate b).work + (table data (enumerate b).value K).work + (3 * b + 1) +
    (read (full b).value (table data (enumerate b).value K).value).work + 3 ≤ _
  unfold countBound
  omega

theorem predicateBound_mono {b b' C C' : ℕ} (hb : b ≤ b') (hC : C ≤ C') :
    predicateBound b C ≤ predicateBound b' C' := by
  unfold predicateBound
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · exact Nat.mul_le_mul hb (Nat.add_le_add_right (Nat.mul_le_mul hb (Nat.add_le_add_right hC 10)) 10)
  · exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hb) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hC) 20)

theorem baseBound_mono {b b' N N' : ℕ} (hb : b ≤ b') (hN : N ≤ N') :
    baseBound b N ≤ baseBound b' N' :=
  Nat.add_le_add_right (Nat.mul_le_mul hN (Nat.add_le_add_right (Nat.mul_le_mul_left 8 hb) 8)) 1

theorem layerBound_mono {b b' C C' N N' : ℕ} (hb : b ≤ b') (hC : C ≤ C') (hN : N ≤ N') :
    layerBound b C N ≤ layerBound b' C' N' := by
  unfold layerBound
  exact Nat.add_le_add_right (Nat.mul_le_mul hN (Nat.add_le_add_right
    (Nat.mul_le_mul hN (Nat.add_le_add_right (predicateBound_mono hb hC) 3)) 4)) 2

/-- A single fixed polynomial in the outer input size and callback work.
Only the local label count is exponential; the logarithmic cap removes it. -/
def polynomialBound (n c C : ℕ) : ℕ :=
  8 * (n + 1) * n + baseBound n n + c * n * layerBound n C n +
    3 * n + n * (9 * n + 7) + 5

theorem count_polynomial (data : Input b K) (n c C : ℕ) (hn : n ≠ 0)
    (hb : b ≤ Nat.log 2 n) (hK : K ≤ c * n) (cost : data.Cost C) :
    (count data).work ≤ polynomialBound n c C := by
  have hpow : 2 ^ b ≤ n := Nat.pow_le_of_le_log hn hb
  have hbn : b ≤ n := hb.trans (Nat.log_le_self 2 n)
  have he : enumerationBound b ≤ 8 * (n + 1) * n :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 8 (Nat.add_le_add_right hbn 1)) hpow
  have hbase := baseBound_mono hbn hpow
  have hlayer := Nat.mul_le_mul hK (layerBound_mono hbn le_rfl hpow (C := C))
  have hlast := Nat.mul_le_mul hpow (Nat.add_le_add_right (Nat.mul_le_mul_left 9 hbn) 7)
  have hthree := Nat.mul_le_mul_left 3 hbn
  apply (count_work data C cost).trans
  unfold countBound polynomialBound
  omega

/-- The exact stored integers, rather than just semantic query values,
satisfy the established binary-length bound. -/
theorem stored_size (data : Input b K) (k : ℕ) (hk : k ≤ K)
    {entry : Mask b × ℕ} (hentry : entry ∈ (table data (enumerate b).value k).value) :
    Nat.size entry.2 ≤ b * (Nat.log 2 (K + 1) + 1) + 1 := by
  rw [table_value] at hentry
  obtain ⟨I, _, rfl⟩ := List.mem_map.mp hentry
  simpa only [Fintype.card_fin] using IdealCounting.lookup_table_size_le data.system k hk (asSet I)

theorem stepSum_table_value (data : Input b K) (k : ℕ) (J : Mask b) :
    (stepSum data k J (table data (enumerate b).value k).value).value =
      IdealCounting.lookup (IdealCounting.table data.system (k + 1)) (asSet J) := by
  rw [table_value, stepSum_value]
  simp only [List.map_map, Function.comp_def, IdealCounting.table, IdealCounting.lookup_tabulate]
  exact (sum_enumerate b (fun I => if IdealCounting.AllowedStep data.system k I (asSet J)
    then IdealCounting.lookup (IdealCounting.table data.system k) I else 0)).trans
    (full_predecessor_sum data.system k (asSet J) (IdealCounting.lookup (IdealCounting.table data.system k)))

theorem stepSum_mono (data : Input b K) (k : ℕ) (J : Mask b) {small large : Table b}
    (h : small.Sublist large) : (stepSum data k J small).value ≤ (stepSum data k J large).value := by
  rw [stepSum_value, stepSum_value]
  exact (h.map _).sum_le_sum (fun _ _ => Nat.zero_le _)

theorem read_mono (J : Mask b) {small large : Table b} (h : small.Sublist large) :
    (read J small).value ≤ (read J large).value := by
  rw [read_value, read_value]
  exact (h.map _).sum_le_sum (fun _ _ => Nat.zero_le _)

/-- Every partial transition sum, including each recursive suffix, has the
same bit bound as the completed next-layer entry. -/
theorem stepSum_partial_size (data : Input b K) (k : ℕ) (hk : k + 1 ≤ K) (J : Mask b)
    (entries : Table b) (h : entries.Sublist (table data (enumerate b).value k).value) :
    Nat.size (stepSum data k J entries).value ≤ b * (Nat.log 2 (K + 1) + 1) + 1 := by
  apply (Nat.size_le_size (stepSum_mono data k J h)).trans
  rw [stepSum_table_value]
  simpa only [Fintype.card_fin] using IdealCounting.lookup_table_size_le data.system (k + 1) hk (asSet J)

theorem read_partial_size (data : Input b K) (k : ℕ) (hk : k ≤ K) (J : Mask b)
    (entries : Table b) (h : entries.Sublist (table data (enumerate b).value k).value) :
    Nat.size (read J entries).value ≤ b * (Nat.log 2 (K + 1) + 1) + 1 := by
  apply (Nat.size_le_size (read_mono J h)).trans
  rw [table_value, read_tabulate]
  simpa only [Fintype.card_fin] using IdealCounting.lookup_table_size_le data.system k hk (asSet J)

/-- Adapt an explicitly stored label enumeration. Only forward array reads
occur in the code; its proof-only inverse is never evaluated. -/
def onLabels {α : Type*} (labels : Vector α b)
    (edge : α → α → Result Bool) (lower upper : α → Result (Fin K)) : Input b K where
  edge i j := let row := edge labels[i] labels[j]; ⟨row.value, row.work + 2⟩
  lower i := let value := lower labels[i]; ⟨value.value, value.work + 1⟩
  upper i := let value := upper labels[i]; ⟨value.value, value.work + 1⟩

theorem onLabels_cost {α : Type*} (labels : Vector α b)
    (edge : α → α → Result Bool) (lower upper : α → Result (Fin K)) (C : ℕ)
    (he : ∀ x y, (edge x y).work ≤ C) (hl : ∀ x, (lower x).work ≤ C) (hu : ∀ x, (upper x).work ≤ C) :
    (onLabels labels edge lower upper).Cost (C + 2) := by
  refine ⟨fun i j => Nat.add_le_add_right (he labels[i] labels[j]) 2, ?_, ?_⟩
  · intro i
    change (lower labels[i]).work + 1 ≤ C + 2
    have hh := hl labels[i]
    omega
  · intro i
    change (upper labels[i]).work + 1 ≤ C + 2
    have hh := hu labels[i]
    omega

theorem count_onLabels {α : Type*} [Fintype α] [DecidableEq α]
    (S : WeakSystem α K) (labels : Vector α b) (hlabels : Function.Bijective (fun i : Fin b => labels[i]))
    (edge : α → α → Result Bool) (lower upper : α → Result (Fin K))
    (he : ∀ x y, (edge x y).value = S.edge x y)
    (hl : ∀ x, (lower x).value = S.lower x) (hu : ∀ x, (upper x).value = S.upper x) :
    (count (onLabels labels edge lower upper)).value = IdealCounting.count S := by
  let e : Fin b ≃ α := Equiv.ofBijective (fun i : Fin b => labels[i]) hlabels
  have hs : (onLabels labels edge lower upper).system = Reindexing.relabel S e.symm := by
    apply Reindexing.system_ext
    · funext x y
      exact he labels[x] labels[y]
    · funext x
      exact hl labels[x]
    · funext x
      exact hu labels[x]
  rw [count_eq, hs, Reindexing.count_relabel, IdealCounting.count_eq]

theorem onLabels_polynomial {α : Type*} (labels : Vector α b)
    (edge : α → α → Result Bool) (lower upper : α → Result (Fin K))
    (n c C : ℕ) (hn : n ≠ 0) (hb : b ≤ Nat.log 2 n) (hK : K ≤ c * n)
    (he : ∀ x y, (edge x y).work ≤ C) (hl : ∀ x, (lower x).work ≤ C) (hu : ∀ x, (upper x).work ≤ C) :
    (count (onLabels labels edge lower upper)).work ≤ polynomialBound n c (C + 2) :=
  count_polynomial _ n c (C + 2) hn hb hK (onLabels_cost labels edge lower upper C he hl hu)

end SortingAdversary.Optimal.LocalDPWork
