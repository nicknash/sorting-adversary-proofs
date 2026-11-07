import SortingAdversary.Optimal.WeakMaps
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Fintype.BigOperators

/-!
# Exact counting by a palette-level ideal dynamic program

The table states are subsets of labels which have already received a colour.
An admissible state is an ideal of the raw row relation, contains no label
whose lower endpoint is still in the future, and omits no label whose upper
endpoint has expired.  A transition adds an entire equal-colour block.

The executable algorithm materializes a finite table of subset/count pairs after
each palette level.  Looking up a previous value therefore reads a stored
integer: it does not recursively recompute an earlier table.  The reference
prefix maps below are used only to prove correctness, not by the algorithm.
The implementation scans every palette level; its polynomial visit bound
assumes the palette size is at most a fixed multiple of the input size.
-/

namespace SortingAdversary.Optimal.IdealCounting

open Finset
open WeakMaps

variable {α : Type*} [Fintype α] [DecidableEq α] {K : ℕ}

/-- Downward closure under every generating row also gives closure under
their reflexive transitive closure.  Antisymmetry is not required. -/
def IsIdeal (S : WeakSystem α K) (I : Finset α) : Prop :=
  ∀ u v, S.edge u v = true → v ∈ I → u ∈ I

instance (S : WeakSystem α K) (I : Finset α) : Decidable (IsIdeal S I) := by
  unfold IsIdeal
  infer_instance

/-- State validity just before colour `k` is processed.  The second and third
conditions explicitly remove future and expired unary intervals. -/
def Admissible (S : WeakSystem α K) (k : ℕ) (I : Finset α) : Prop :=
  IsIdeal S I ∧
    (∀ x ∈ I, (S.lower x).val < k) ∧
    ∀ x, x ∉ I → k ≤ (S.upper x).val

instance (S : WeakSystem α K) (k : ℕ) (I : Finset α) :
    Decidable (Admissible S k I) := by
  unfold Admissible
  infer_instance

/-- A single palette level can assign any newly added block, including an
entire strongly connected block of the weak relation. -/
def AllowedStep (S : WeakSystem α K) (k : ℕ) (I J : Finset α) : Prop :=
  I ⊆ J ∧ Admissible S (k + 1) J ∧
    ∀ x, x ∈ J → x ∉ I → (S.lower x).val ≤ k ∧ k ≤ (S.upper x).val

instance (S : WeakSystem α K) (k : ℕ) (I J : Finset α) :
    Decidable (AllowedStep S k I J) := by
  unfold AllowedStep
  infer_instance

/-- Prefix witnesses use `K` as the unique unassigned sentinel.  Their actual
assigned values lie in `Fin K`; this ambient type also handles empty palettes. -/
abbrev PrefixMap (α : Type*) (K : ℕ) := α → Fin (K + 1)

/-- Semantic specification of a partial map after the first `k` colours. -/
def PrefixValid (S : WeakSystem α K) (k : ℕ) (I : Finset α)
    (f : PrefixMap α K) : Prop :=
  Admissible S k I ∧
    (∀ x ∈ I, (f x).val < k ∧
      (S.lower x).val ≤ (f x).val ∧ (f x).val ≤ (S.upper x).val) ∧
    (∀ x, x ∉ I → f x = Fin.last K) ∧
    ∀ u v, S.edge u v = true → v ∈ I → (f u).val ≤ (f v).val

instance (S : WeakSystem α K) (k : ℕ) (I : Finset α) (f : PrefixMap α K) :
    Decidable (PrefixValid S k I f) := by
  unfold PrefixValid
  infer_instance

/-- Finite reference semantics; the dynamic program does not call this. -/
def prefixMaps (S : WeakSystem α K) (k : ℕ) (I : Finset α) :
    Finset (PrefixMap α K) := univ.filter (PrefixValid S k I)

@[simp] theorem mem_prefixMaps (S : WeakSystem α K) (k : ℕ) (I : Finset α)
    (f : PrefixMap α K) :
    f ∈ prefixMaps S k I ↔ PrefixValid S k I f := by
  simp [prefixMaps]

/-- Forget the colours outside `I`. -/
def restrictPrefix (I : Finset α) (f : PrefixMap α K) : PrefixMap α K :=
  fun x => if x ∈ I then f x else Fin.last K

/-- Add the colour-`k` block `J \ I`, preserving the already assigned values. -/
def extendPrefix (k : Fin K) (I J : Finset α) (f : PrefixMap α K) :
    PrefixMap α K :=
  fun x => if x ∈ I then f x else if x ∈ J then k.castSucc else Fin.last K

/-- The unique predecessor state of a prefix at the next level. -/
def previousState (k : ℕ) (J : Finset α) (f : PrefixMap α K) : Finset α :=
  J.filter (fun x => (f x).val < k)

omit [Fintype α] [DecidableEq α] in
@[simp] theorem mem_previousState (k : ℕ) (J : Finset α) (f : PrefixMap α K)
    (x : α) : x ∈ previousState k J f ↔ x ∈ J ∧ (f x).val < k := by
  simp [previousState]

omit [Fintype α] in
theorem prefixValid_extend {S : WeakSystem α K} {k : Fin K} {I J : Finset α}
    {f : PrefixMap α K} (hf : PrefixValid S k.val I f)
    (hstep : AllowedStep S k.val I J) :
    PrefixValid S (k.val + 1) J (extendPrefix k I J f) := by
  refine ⟨hstep.2.1, ?_, ?_, ?_⟩
  · intro x hxJ
    by_cases hxI : x ∈ I
    · simpa [extendPrefix, hxI] using
        ⟨Nat.lt_succ_of_lt (hf.2.1 x hxI).1, (hf.2.1 x hxI).2⟩
    · simp only [extendPrefix, if_neg hxI, if_pos hxJ, Fin.val_castSucc]
      exact ⟨Nat.lt_succ_self k.val, hstep.2.2 x hxJ hxI⟩
  · intro x hxJ
    have hxI : x ∉ I := fun h => hxJ (hstep.1 h)
    simp [extendPrefix, hxI, hxJ]
  · intro u v huv hvJ
    have huJ := hstep.2.1.1 u v huv hvJ
    by_cases hvI : v ∈ I
    · have huI := hf.1.1 u v huv hvI
      simpa [extendPrefix, huI, hvI] using hf.2.2.2 u v huv hvI
    · by_cases huI : u ∈ I
      · simpa [extendPrefix, huI, hvI, hvJ] using (hf.2.1 u huI).1.le
      · simp [extendPrefix, huI, huJ, hvI, hvJ]

omit [Fintype α] in
theorem previousState_extend {S : WeakSystem α K} {k : Fin K} {I J : Finset α}
    {f : PrefixMap α K} (hf : PrefixValid S k.val I f)
    (hIJ : I ⊆ J) : previousState k.val J (extendPrefix k I J f) = I := by
  ext x
  by_cases hxI : x ∈ I
  · simp [hxI, hIJ hxI, extendPrefix, (hf.2.1 x hxI).1]
  · by_cases hxJ : x ∈ J <;> simp [hxI, hxJ, extendPrefix]

omit [Fintype α] in
theorem restrict_extend {S : WeakSystem α K} {k : Fin K} {I J : Finset α}
    {f : PrefixMap α K} (hf : PrefixValid S k.val I f) :
    restrictPrefix I (extendPrefix k I J f) = f := by
  funext x
  by_cases hxI : x ∈ I
  · simp [restrictPrefix, extendPrefix, hxI]
  · simp [restrictPrefix, hxI, hf.2.2.1 x hxI]

omit [Fintype α] in
theorem prefixValid_previous {S : WeakSystem α K} {k : Fin K} {J : Finset α}
    {f : PrefixMap α K} (hf : PrefixValid S (k.val + 1) J f) :
    PrefixValid S k.val (previousState k.val J f)
      (restrictPrefix (previousState k.val J f) f) := by
  let I := previousState k.val J f
  have hI : ∀ x, x ∈ I ↔ x ∈ J ∧ (f x).val < k.val := by
    intro x
    exact mem_previousState _ _ _ _
  have hIJ : I ⊆ J := fun _ hx => (hI _).mp hx |>.1
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro u v huv hvI
    have hv := (hI v).mp hvI
    exact (hI u).mpr ⟨hf.1.1 u v huv hv.1,
      lt_of_le_of_lt (hf.2.2.2 u v huv hv.1) hv.2⟩
  · intro x hxI
    exact lt_of_le_of_lt (hf.2.1 x (hIJ hxI)).2.1 ((hI x).mp hxI).2
  · intro x hxI
    by_cases hxJ : x ∈ J
    · have hfx : k.val ≤ (f x).val := by
        by_contra h
        exact hxI ((hI x).mpr ⟨hxJ, Nat.lt_of_not_ge h⟩)
      exact hfx.trans (hf.2.1 x hxJ).2.2
    · exact (Nat.le_succ k.val).trans (hf.1.2.2 x hxJ)
  · intro x hxI
    simpa [restrictPrefix, hxI] using
      ⟨((hI x).mp hxI).2, (hf.2.1 x (hIJ hxI)).2⟩
  · intro x hxI
    simp [restrictPrefix, hxI]
  · intro u v huv hvI
    have hv := (hI v).mp hvI
    have huI : u ∈ I := (hI u).mpr ⟨hf.1.1 u v huv hv.1,
      lt_of_le_of_lt (hf.2.2.2 u v huv hv.1) hv.2⟩
    have hvI' : v ∈ I := hvI
    change (restrictPrefix I f u).val ≤ (restrictPrefix I f v).val
    simpa only [restrictPrefix, if_pos huI, if_pos hvI'] using hf.2.2.2 u v huv hv.1

omit [Fintype α] [DecidableEq α] in
theorem allowedStep_previous {S : WeakSystem α K} {k : Fin K} {J : Finset α}
    {f : PrefixMap α K} (hf : PrefixValid S (k.val + 1) J f) :
    AllowedStep S k.val (previousState k.val J f) J := by
  refine ⟨filter_subset _ _, hf.1, ?_⟩
  intro x hxJ hxI
  have hfx : (f x).val = k.val := by
    have hlt := (hf.2.1 x hxJ).1
    have hnot : ¬ (f x).val < k.val := fun h => hxI ((mem_previousState _ _ _ _).mpr ⟨hxJ, h⟩)
    omega
  simpa [hfx] using (hf.2.1 x hxJ).2

omit [Fintype α] in
theorem extend_previous {S : WeakSystem α K} {k : Fin K} {J : Finset α}
    {f : PrefixMap α K} (hf : PrefixValid S (k.val + 1) J f) :
    extendPrefix k (previousState k.val J f) J
      (restrictPrefix (previousState k.val J f) f) = f := by
  funext x
  by_cases hxI : x ∈ previousState k.val J f
  · simp [extendPrefix, restrictPrefix, hxI]
  · by_cases hxJ : x ∈ J
    · have hfx : (f x).val = k.val := by
        have hlt := (hf.2.1 x hxJ).1
        have hnot : ¬ (f x).val < k.val :=
          fun h => hxI ((mem_previousState _ _ _ _).mpr ⟨hxJ, h⟩)
        omega
      apply Fin.ext
      simp [extendPrefix, hxI, hxJ, hfx]
    · simp [extendPrefix, hxI, hxJ, hf.2.2.1 x hxJ]

/-- Disjoint predecessor fibres used in the correctness proof. -/
def predecessorPairs (S : WeakSystem α K) (k : ℕ) (J : Finset α) :
    Finset (Σ _ : Finset α, PrefixMap α K) :=
  J.powerset.sigma (fun I => if AllowedStep S k I J then prefixMaps S k I else ∅)

@[simp] theorem mem_predecessorPairs (S : WeakSystem α K) (k : ℕ) (J I : Finset α)
    (f : PrefixMap α K) :
    (⟨I, f⟩ : Σ _ : Finset α, PrefixMap α K) ∈ predecessorPairs S k J ↔
      AllowedStep S k I J ∧ PrefixValid S k I f := by
  simp only [predecessorPairs, mem_sigma, mem_powerset]
  by_cases hs : AllowedStep S k I J
  · simp [hs, hs.1]
  · simp [hs]

/-- Exact semantic recurrence.  The predecessor is recovered from the values
strictly below `k`, so each partial map is counted exactly once. -/
theorem prefix_count_succ (S : WeakSystem α K) (k : Fin K) (J : Finset α) :
    (prefixMaps S (k.val + 1) J).card =
      ∑ I ∈ J.powerset, if AllowedStep S k.val I J then (prefixMaps S k.val I).card else 0 := by
  have hcard : (predecessorPairs S k.val J).card = (prefixMaps S (k.val + 1) J).card := by
    apply Finset.card_bij (fun p _ => extendPrefix k p.1 J p.2)
    · rintro ⟨I, f⟩ hp
      obtain ⟨hs, hf⟩ := (mem_predecessorPairs S k.val J I f).mp hp
      exact (mem_prefixMaps _ _ _ _).mpr (prefixValid_extend hf hs)
    · rintro ⟨I, f⟩ hp ⟨I', g⟩ hq heq
      obtain ⟨hs, hf⟩ := (mem_predecessorPairs S k.val J I f).mp hp
      obtain ⟨hs', hg⟩ := (mem_predecessorPairs S k.val J I' g).mp hq
      have hI : I = I' := by
        have h := congrArg (previousState k.val J) heq
        simpa only [previousState_extend hf hs.1, previousState_extend hg hs'.1] using h
      subst I'
      have hfg : f = g := by
        have h := congrArg (restrictPrefix I) heq
        simpa only [restrict_extend hf, restrict_extend hg] using h
      subst g
      rfl
    · intro f hf
      have hv := (mem_prefixMaps _ _ _ _).mp hf
      refine ⟨⟨previousState k.val J f, restrictPrefix (previousState k.val J f) f⟩, ?_, ?_⟩
      · exact (mem_predecessorPairs _ _ _ _ _).mpr
          ⟨allowedStep_previous hv, prefixValid_previous hv⟩
      · exact extend_previous hv
  rw [← hcard]
  simp only [predecessorPairs, card_sigma]
  apply sum_congr rfl
  intro I _
  split_ifs <;> simp

omit [Fintype α] [DecidableEq α] in
theorem prefixValid_zero_iff (S : WeakSystem α K) (I : Finset α) (f : PrefixMap α K) :
    PrefixValid S 0 I f ↔ I = ∅ ∧ f = fun _ => Fin.last K := by
  constructor
  · intro hf
    have hI : I = ∅ := eq_empty_iff_forall_notMem.mpr
      (fun x hx => Nat.not_lt_zero _ (hf.2.1 x hx).1)
    refine ⟨hI, ?_⟩
    funext x
    exact hf.2.2.1 x (by simp [hI])
  · rintro ⟨rfl, rfl⟩
    simp [PrefixValid, Admissible, IsIdeal]

theorem prefix_count_zero (S : WeakSystem α K) (I : Finset α) :
    (prefixMaps S 0 I).card = if I = ∅ then 1 else 0 := by
  have hmaps : prefixMaps S 0 I = if I = ∅ then {fun _ => Fin.last K} else ∅ := by
    ext f
    by_cases hI : I = ∅ <;> simp [prefixValid_zero_iff, hI]
  rw [hmaps]
  split_ifs <;> simp

omit [DecidableEq α] in
theorem prefixValid_full_iff (S : WeakSystem α K) (f : ColorMap α K) :
    PrefixValid S K univ (fun x => (f x).castSucc) ↔ S.Valid f := by
  constructor
  · intro hf
    exact ⟨fun x => (hf.2.1 x (mem_univ x)).2,
      fun u v huv => hf.2.2.2 u v huv (mem_univ v)⟩
  · intro hf
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro u _ _ _
      exact mem_univ u
    · intro x _
      exact (S.lower x).isLt
    · intro x hx
      exact False.elim (hx (mem_univ x))
    · intro x _
      exact ⟨(f x).isLt, hf.1 x⟩
    · intro x hx
      exact False.elim (hx (mem_univ x))
    · intro u v huv _
      exact hf.2 u v huv

/-- At the end, prefix witnesses are exactly the original weak colour maps. -/
theorem prefix_count_full (S : WeakSystem α K) :
    (prefixMaps S K univ).card = S.count := by
  symm
  unfold WeakSystem.count
  apply Finset.card_bij (fun f _ x => (f x).castSucc)
  · intro f hf
    exact (mem_prefixMaps _ _ _ _).mpr
      ((prefixValid_full_iff S f).mpr ((WeakSystem.mem_maps S f).mp hf))
  · intro f _ g _ hfg
    funext x
    apply Fin.ext
    have h := congrArg (fun c : Fin (K + 1) => c.val) (congrFun hfg x)
    exact h
  · intro g hg
    have hv := (mem_prefixMaps _ _ _ _).mp hg
    let f : ColorMap α K := fun x => ⟨(g x).val, (hv.2.1 x (mem_univ x)).1⟩
    have hfg : (fun x => (f x).castSucc) = g := by
      funext x
      apply Fin.ext
      rfl
    refine ⟨f, ?_, hfg⟩
    apply (WeakSystem.mem_maps S f).mpr
    apply (prefixValid_full_iff S f).mp
    rwa [hfg]

/-- A materialized table.  Scanning lookup has an explicit linear bound below. -/
abbrev Table (α : Type*) := Finset (Finset α × ℕ)

/-- Read an already computed count by scanning the stored rows.  Tables built
by `tabulate` have exactly one row for each state. -/
def lookup (T : Table α) (I : Finset α) : ℕ :=
  ∑ p ∈ T, if p.1 = I then p.2 else 0

/-- Evaluate each subset's value and store the resulting integer. -/
def tabulate (value : Finset α → ℕ) : Table α :=
  (univ : Finset α).powerset.map
    ⟨fun I => (I, value I), fun _ _ h => congrArg Prod.fst h⟩

@[simp] theorem lookup_tabulate (value : Finset α → ℕ) (I : Finset α) :
    lookup (tabulate value) I = value I := by
  simp only [lookup, tabulate, Finset.sum_map]
  change (∑ J ∈ (univ : Finset α).powerset, if J = I then value J else 0) = value I
  simp

/-- The dynamic program scans palette levels, materializing a fresh table at
each step.  It enumerates subsets and nested subset pairs, never colour maps. -/
def table (S : WeakSystem α K) : ℕ → Table α
  | 0 => tabulate (fun I => if I = ∅ then 1 else 0)
  | k + 1 =>
    let old := table S k
    tabulate (fun J => ∑ I ∈ J.powerset, if AllowedStep S k I J then lookup old I else 0)

/-- The executable output is the all-assigned entry after `K` palette levels. -/
def count (S : WeakSystem α K) : ℕ := lookup (table S K) univ

theorem lookup_table (S : WeakSystem α K) (k : ℕ) (hk : k ≤ K) (I : Finset α) :
    lookup (table S k) I = (prefixMaps S k I).card := by
  induction k generalizing I with
  | zero => simp [table, prefix_count_zero]
  | succ k ih =>
    rw [table, lookup_tabulate]
    rw [prefix_count_succ S ⟨k, Nat.lt_of_succ_le hk⟩ I]
    apply sum_congr rfl
    intro J _
    split_ifs
    · exact ih ((Nat.le_succ k).trans hk) J
    · rfl

/-- Exact correctness for arbitrary raw weak rows and inclusive unary lists.
No preorder hypothesis or assumption of nonempty support is needed. -/
theorem count_eq (S : WeakSystem α K) : count S = S.count := by
  rw [count, lookup_table S K le_rfl, prefix_count_full]

theorem lookup_table_eq_zero_of_not_admissible (S : WeakSystem α K) (k : ℕ)
    (hk : k ≤ K) (I : Finset α) (hI : ¬ Admissible S k I) :
    lookup (table S k) I = 0 := by
  rw [lookup_table S k hk I]
  apply card_eq_zero.mpr
  apply eq_empty_of_forall_notMem
  intro f hf
  exact hI ((mem_prefixMaps S k I f).mp hf).1

/-- A label cannot already be assigned before its interval has begun. -/
theorem lookup_table_eq_zero_of_future (S : WeakSystem α K) (k : ℕ)
    (hk : k ≤ K) (I : Finset α) (x : α) (hx : x ∈ I)
    (hfuture : k ≤ (S.lower x).val) : lookup (table S k) I = 0 := by
  apply lookup_table_eq_zero_of_not_admissible S k hk I
  intro hI
  exact (Nat.not_lt_of_ge hfuture) (hI.2.1 x hx)

/-- A label cannot remain unassigned after its last accepted colour. -/
theorem lookup_table_eq_zero_of_expired (S : WeakSystem α K) (k : ℕ)
    (hk : k ≤ K) (I : Finset α) (x : α) (hx : x ∉ I)
    (hexpired : (S.upper x).val < k) : lookup (table S k) I = 0 := by
  apply lookup_table_eq_zero_of_not_admissible S k hk I
  intro hI
  exact (Nat.not_lt_of_ge (hI.2.2 x hx)) hexpired

/-! ## Table size, transition visits, and binary storage

The counters in this section measure visits to candidate transitions and
stored table rows.  They do not charge an arbitrary implementation of the
input functions `edge`, `lower`, and `upper` as constant-time machine code.
The binary-size bounds apply to the actual natural numbers stored in the
table.  Together these give the quantitative counting core; a machine-cost
theorem additionally needs a concrete representation of the input relation.
-/

omit [DecidableEq α] in
@[simp] theorem tabulate_card (value : Finset α → ℕ) :
    (tabulate value).card = 2 ^ Fintype.card α := by
  simp [tabulate]

/-- The algorithm stores exactly one count for each of the `2^b` subsets.
Entries for inadmissible states are zero by correctness. -/
@[simp] theorem table_card (S : WeakSystem α K) (k : ℕ) :
    (table S k).card = 2 ^ Fintype.card α := by
  cases k <;> simp [table]

omit [DecidableEq α] in
/-- Across all target states there are exactly `3^b` nested subset pairs.
Each label is old, newly assigned, or still unassigned. -/
theorem candidate_transitions :
    (∑ J ∈ (univ : Finset α).powerset, J.powerset.card) = 3 ^ Fintype.card α := by
  simpa using
    (Finset.prod_add_one (f := fun _ : α => (2 : ℕ)) (univ : Finset α)).symm

/-- One outer-state visit, one predicate test per candidate transition, and
one row visit per scanned old table entry on accepted transitions. -/
def stepWork (S : WeakSystem α K) (k : ℕ) (old : Table α) : ℕ :=
  (univ : Finset α).powerset.card +
    ∑ J ∈ (univ : Finset α).powerset,
      ∑ I ∈ J.powerset, (1 + if AllowedStep S k I J then old.card else 0)

theorem stepWork_le (S : WeakSystem α K) (k : ℕ) (old : Table α) :
    stepWork S k old ≤ 2 ^ Fintype.card α + 3 ^ Fintype.card α * (1 + old.card) := by
  unfold stepWork
  rw [card_powerset, card_univ]
  apply Nat.add_le_add_left
  calc
    (∑ J ∈ (univ : Finset α).powerset,
        ∑ I ∈ J.powerset, (1 + if AllowedStep S k I J then old.card else 0)) ≤
        ∑ J ∈ (univ : Finset α).powerset, ∑ _I ∈ J.powerset, (1 + old.card) := by
      apply sum_le_sum
      intro J _
      apply sum_le_sum
      intro I _
      split_ifs <;> omega
    _ = 3 ^ Fintype.card α * (1 + old.card) := by
      simp only [sum_const, nsmul_eq_mul, Nat.cast_id]
      rw [← sum_mul, candidate_transitions]

/-- Instrumented execution of the same materialized dynamic program.
The second component counts the visits described by `stepWork`. -/
def tableWithWork (S : WeakSystem α K) : ℕ → Table α × ℕ
  | 0 =>
    let T := tabulate (fun I => if I = ∅ then 1 else 0)
    (T, T.card)
  | k + 1 =>
    let old := tableWithWork S k
    let T := tabulate
      (fun J => ∑ I ∈ J.powerset, if AllowedStep S k I J then lookup old.1 I else 0)
    (T, old.2 + stepWork S k old.1)

@[simp] theorem tableWithWork_fst (S : WeakSystem α K) (k : ℕ) :
    (tableWithWork S k).1 = table S k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [tableWithWork, table, ih]

theorem tableWithWork_le (S : WeakSystem α K) (k : ℕ) :
    (tableWithWork S k).2 ≤ 2 ^ Fintype.card α +
      k * (2 ^ Fintype.card α + 3 ^ Fintype.card α * (1 + 2 ^ Fintype.card α)) := by
  induction k with
  | zero => simp [tableWithWork]
  | succ k ih =>
    have hs := stepWork_le S k (table S k)
    rw [table_card] at hs
    change (tableWithWork S k).2 + stepWork S k (tableWithWork S k).1 ≤
      2 ^ Fintype.card α +
        (k + 1) * (2 ^ Fintype.card α + 3 ^ Fintype.card α * (1 + 2 ^ Fintype.card α))
    rw [tableWithWork_fst, Nat.add_mul, one_mul]
    omega

/-- The final read is included in this execution counter. -/
def countWithWork (S : WeakSystem α K) : ℕ × ℕ :=
  let result := tableWithWork S K
  (lookup result.1 univ, result.2 + result.1.card)

@[simp] theorem countWithWork_fst (S : WeakSystem α K) :
    (countWithWork S).1 = S.count := by
  simp only [countWithWork, tableWithWork_fst]
  exact count_eq S

theorem countWithWork_le (S : WeakSystem α K) :
    (countWithWork S).2 ≤ 2 * 2 ^ Fintype.card α +
      K * (2 ^ Fintype.card α + 3 ^ Fintype.card α * (1 + 2 ^ Fintype.card α)) := by
  have h := tableWithWork_le S K
  simp only [countWithWork, tableWithWork_fst, table_card]
  omega

/-- Under the logarithmic ball cap and a linear palette bound, the measured
visits satisfy an explicit polynomial bound of degree four in `n`. -/
theorem countWithWork_polynomial (S : WeakSystem α K) (n c : ℕ) (hn : n ≠ 0)
    (hb : Fintype.card α ≤ Nat.log 2 n) (hK : K ≤ c * n) :
    (countWithWork S).2 ≤ 2 * n + c * n * (n + n ^ 2 * (1 + n)) := by
  have htwo : 2 ^ Fintype.card α ≤ n := Nat.pow_le_of_le_log hn hb
  have hthree : 3 ^ Fintype.card α ≤ n ^ 2 := by
    calc
      3 ^ Fintype.card α ≤ 4 ^ Fintype.card α := Nat.pow_le_pow_left (by decide) _
      _ = (2 ^ Fintype.card α) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by rfl, mul_pow, pow_two]
      _ ≤ n ^ 2 := Nat.pow_le_pow_left htwo _
  apply (countWithWork_le S).trans
  apply Nat.add_le_add (Nat.mul_le_mul_left 2 htwo)
  apply Nat.mul_le_mul hK
  exact Nat.add_le_add htwo (Nat.mul_le_mul hthree (Nat.add_le_add_left htwo 1))

/-- Every stored value is bounded by the number of maps into the ambient
palette with its one extra unassigned sentinel. -/
theorem lookup_table_le (S : WeakSystem α K) (k : ℕ) (hk : k ≤ K) (I : Finset α) :
    lookup (table S k) I ≤ (K + 1) ^ Fintype.card α := by
  rw [lookup_table S k hk I]
  calc
    (prefixMaps S k I).card ≤ (univ : Finset (PrefixMap α K)).card :=
      card_le_card (filter_subset _ _)
    _ = (K + 1) ^ Fintype.card α := by simp [PrefixMap]

/-- A precise binary storage bound for every table count. -/
theorem lookup_table_size_le (S : WeakSystem α K) (k : ℕ) (hk : k ≤ K) (I : Finset α) :
    Nat.size (lookup (table S k) I) ≤
      Fintype.card α * (Nat.log 2 (K + 1) + 1) + 1 := by
  have hbase : K + 1 ≤ 2 ^ (Nat.log 2 (K + 1) + 1) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (K + 1)).le
  have hcount : lookup (table S k) I ≤
      2 ^ (Fintype.card α * (Nat.log 2 (K + 1) + 1)) := by
    calc
      _ ≤ (K + 1) ^ Fintype.card α := lookup_table_le S k hk I
      _ ≤ (2 ^ (Nat.log 2 (K + 1) + 1)) ^ Fintype.card α := Nat.pow_le_pow_left hbase _
      _ = _ := by rw [← pow_mul, Nat.mul_comm]
  apply Nat.size_le.mpr
  exact lt_of_le_of_lt hcount
    (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self _))

theorem mem_tabulate_value (value : Finset α → ℕ) {p : Finset α × ℕ}
    (hp : p ∈ tabulate value) : p.2 = lookup (tabulate value) p.1 := by
  obtain ⟨I, _, rfl⟩ := mem_map.mp hp
  exact (lookup_tabulate value I).symm

/-- The storage bound applies to each actual row, not just values obtained
through the lookup interface. -/
theorem stored_size_le (S : WeakSystem α K) (k : ℕ) (hk : k ≤ K)
    {p : Finset α × ℕ} (hp : p ∈ table S k) :
    Nat.size p.2 ≤ Fintype.card α * (Nat.log 2 (K + 1) + 1) + 1 := by
  have hval : p.2 = lookup (table S k) p.1 := by
    cases k <;> exact mem_tabulate_value _ hp
  rw [hval]
  exact lookup_table_size_le S k hk p.1

/-- Scanning a stored table uses sums of nonnegative terms, so its partial
sums obey the same bit bound as the completed lookup. -/
theorem lookup_partial_sum_size_le (S : WeakSystem α K) (k : ℕ) (hk : k ≤ K)
    (I : Finset α) (T : Table α) (hT : T ⊆ table S k) :
    Nat.size (∑ p ∈ T, if p.1 = I then p.2 else 0) ≤
      Fintype.card α * (Nat.log 2 (K + 1) + 1) + 1 := by
  have hs : (∑ p ∈ T, if p.1 = I then p.2 else 0) ≤ lookup (table S k) I :=
    sum_le_sum_of_subset hT
  exact (Nat.size_le_size hs).trans (lookup_table_size_le S k hk I)

/-- The sums which produce new entries also stay within the proved binary
capacity throughout, including on infeasible target states. -/
theorem transition_partial_sum_size_le (S : WeakSystem α K) (k : ℕ) (hk : k + 1 ≤ K)
    (J : Finset α) (T : Finset (Finset α)) (hT : T ⊆ J.powerset) :
    Nat.size (∑ I ∈ T, if AllowedStep S k I J then lookup (table S k) I else 0) ≤
      Fintype.card α * (Nat.log 2 (K + 1) + 1) + 1 := by
  have hs : (∑ I ∈ T, if AllowedStep S k I J then lookup (table S k) I else 0) ≤
      lookup (table S (k + 1)) J := by
    rw [table, lookup_tabulate]
    exact sum_le_sum_of_subset hT
  exact (Nat.size_le_size hs).trans (lookup_table_size_le S (k + 1) hk J)

/-- With the logarithmic ball cap the actual table integers need only a
product of logarithmic bounds on their binary lengths. -/
theorem lookup_table_size_logCap (S : WeakSystem α K) (k : ℕ) (hk : k ≤ K)
    (I : Finset α) (n c : ℕ) (hb : Fintype.card α ≤ Nat.log 2 n) (hK : K ≤ c * n) :
    Nat.size (lookup (table S k) I) ≤
      Nat.log 2 n * (Nat.log 2 (c * n + 1) + 1) + 1 := by
  apply (lookup_table_size_le S k hk I).trans
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul hb
  exact Nat.add_le_add_right (Nat.log_mono_right (Nat.add_le_add_right hK 1)) 1

end SortingAdversary.Optimal.IdealCounting
