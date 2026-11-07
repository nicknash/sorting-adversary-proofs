import SortingAdversary.Optimal.LocalDPWork

/-!
# Counted original-label indexing for induced local systems

The actual ball is a duplicate-free list of original labels. The executable
adapter uses a counted list traversal for every index lookup. A bijection
with the induced carrier is used only in the correctness proof.
-/

namespace SortingAdversary.Optimal.LocalListDPWork

open PrimitiveWork WeakMaps LocalChoice

def get {α : Type*} : (xs : List α) → Fin xs.length → Result α
  | [], i => Fin.elim0 i
  | x :: xs, i => Fin.cases ⟨x, 1⟩
      (fun j => let tail := get xs j; ⟨tail.value, tail.work + 2⟩) i

@[simp] theorem get_value {α : Type*} (xs : List α) (i : Fin xs.length) :
    (get xs i).value = xs[i] := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simpa only [get, Fin.cases_succ, Fin.getElem_fin, Fin.val_succ, List.getElem_cons_succ] using ih j

theorem get_work {α : Type*} (xs : List α) (i : Fin xs.length) :
    (get xs i).work = 2 * i.val + 1 := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [get, Fin.cases_succ, Fin.val_succ, ih]
      omega

def input {α : Type*} {K : ℕ} (xs : List α)
    (edge : α → α → Result Bool) (lower upper : α → Result (Fin K)) : LocalDPWork.Input xs.length K where
  edge i j :=
    let x := get xs i
    let y := get xs j
    let row := edge x.value y.value
    ⟨row.value, x.work + y.work + row.work + 2⟩
  lower i :=
    let x := get xs i
    let wall := lower x.value
    ⟨wall.value, x.work + wall.work + 1⟩
  upper i :=
    let x := get xs i
    let wall := upper x.value
    ⟨wall.value, x.work + wall.work + 1⟩

theorem input_cost {α : Type*} {K : ℕ} (xs : List α)
    (edge : α → α → Result Bool) (lower upper : α → Result (Fin K)) (C : ℕ)
    (he : ∀ x y, (edge x y).work ≤ C) (hl : ∀ x, (lower x).work ≤ C) (hu : ∀ x, (upper x).work ≤ C) :
    (input xs edge lower upper).Cost (4 * xs.length + C + 4) := by
  constructor
  · intro i j
    have hi := i.isLt
    have hj := j.isLt
    have hh := he (get xs i).value (get xs j).value
    change (get xs i).work + (get xs j).work + (edge (get xs i).value (get xs j).value).work + 2 ≤ _
    rw [get_work, get_work]
    omega
  · constructor
    · intro i
      have hi := i.isLt
      have hh := hl (get xs i).value
      change (get xs i).work + _ + 1 ≤ _
      rw [get_work]
      omega
    · intro i
      have hi := i.isLt
      have hh := hu (get xs i).value
      change (get xs i).work + _ + 1 ≤ _
      rw [get_work]
      omega

def count {α : Type*} {K : ℕ} (xs : List α)
    (edge : α → α → Result Bool) (lower upper : α → Result (Fin K)) : Result ℕ :=
  let size := FiniteLoopWork.length xs
  let answer := LocalDPWork.count (input xs edge lower upper)
  ⟨answer.value, size.work + answer.work + 1⟩

theorem count_value {α : Type*} [Fintype α] [DecidableEq α] {K : ℕ}
    (S : WeakSystem α K) (B : Finset α) (xs : List α) (hn : xs.Nodup) (hs : xs.toFinset = B)
    (edge : α → α → Result Bool) (lower upper : α → Result (Fin K))
    (he : ∀ x y, (edge x y).value = S.edge x y)
    (hl : ∀ x, (lower x).value = S.lower x) (hu : ∀ x, (upper x).value = S.upper x) :
    (count xs edge lower upper).value = IdealCounting.count (induced S B) := by
  let f : Fin xs.length → B := fun i => ⟨xs[i], by
    rw [← hs]
    exact List.mem_toFinset.mpr (List.getElem_mem i.isLt)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      have hget : xs.get i = xs.get j := congrArg Subtype.val hij
      exact (List.nodup_iff_injective_get.mp hn) hget
    · intro x
      have hx : x.val ∈ xs := List.mem_toFinset.mp (by rw [hs]; exact x.property)
      obtain ⟨i, hi⟩ := List.get_of_mem hx
      exact ⟨i, Subtype.ext hi⟩
  let e : Fin xs.length ≃ B := Equiv.ofBijective f hf
  have hsystem : (input xs edge lower upper).system = Reindexing.relabel (induced S B) e.symm := by
    apply Reindexing.system_ext
    · funext i j
      simpa only [input, LocalDPWork.Input.system, get_value, Reindexing.relabel, Equiv.symm_symm,
        induced, e, Equiv.ofBijective_apply, f] using he xs[i] xs[j]
    · funext i
      simpa only [input, LocalDPWork.Input.system, get_value, Reindexing.relabel, Equiv.symm_symm,
        induced, e, Equiv.ofBijective_apply, f] using hl xs[i]
    · funext i
      simpa only [input, LocalDPWork.Input.system, get_value, Reindexing.relabel, Equiv.symm_symm,
        induced, e, Equiv.ofBijective_apply, f] using hu xs[i]
  change (LocalDPWork.count (input xs edge lower upper)).value = _
  rw [LocalDPWork.count_eq, hsystem, Reindexing.count_relabel, IdealCounting.count_eq]

theorem count_work {α : Type*} {K : ℕ} (xs : List α)
    (edge : α → α → Result Bool) (lower upper : α → Result (Fin K)) (C : ℕ)
    (he : ∀ x y, (edge x y).work ≤ C) (hl : ∀ x, (lower x).work ≤ C) (hu : ∀ x, (upper x).work ≤ C) :
    (count xs edge lower upper).work ≤ 2 * xs.length +
      LocalDPWork.countBound xs.length K (4 * xs.length + C + 4) + 2 := by
  have hh := LocalDPWork.count_work _ _ (input_cost xs edge lower upper C he hl hu)
  change (FiniteLoopWork.length xs).work + (LocalDPWork.count (input xs edge lower upper)).work + 1 ≤ _
  rw [FiniteLoopWork.length_work]
  omega

theorem count_polynomial {α : Type*} {K : ℕ} (xs : List α)
    (edge : α → α → Result Bool) (lower upper : α → Result (Fin K)) (n c C : ℕ)
    (hn : n ≠ 0) (hb : xs.length ≤ Nat.log 2 n) (hK : K ≤ c * n)
    (he : ∀ x y, (edge x y).work ≤ C) (hl : ∀ x, (lower x).work ≤ C) (hu : ∀ x, (upper x).work ≤ C) :
    (count xs edge lower upper).work ≤ 2 * n + LocalDPWork.polynomialBound n c (4 * n + C + 4) + 2 := by
  have hlen : xs.length ≤ n := hb.trans (Nat.log_le_self 2 n)
  have hc := input_cost xs edge lower upper C he hl hu
  have hc' : (input xs edge lower upper).Cost (4 * n + C + 4) := by
    have hh : 4 * xs.length + C + 4 ≤ 4 * n + C + 4 := by omega
    exact ⟨fun i j => (hc.1 i j).trans hh, fun i => (hc.2.1 i).trans hh, fun i => (hc.2.2 i).trans hh⟩
  have hh := LocalDPWork.count_polynomial _ n c (4 * n + C + 4) hn hb hK hc'
  change (FiniteLoopWork.length xs).work + (LocalDPWork.count (input xs edge lower upper)).work + 1 ≤ _
  rw [FiniteLoopWork.length_work]
  omega

end SortingAdversary.Optimal.LocalListDPWork
