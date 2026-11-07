import SortingAdversary.Optimal.IdealCounting
import SortingAdversary.Optimal.FiniteLoopWork
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Explicit Boolean subset generation and scans

Subsets are materialized Boolean vectors. Enumeration recursively appends
one false or true coordinate, paying for vector copying, list mapping and
concatenation. The finite-set interpretation is used only in proofs.
-/

namespace SortingAdversary.Optimal.SubsetWork

open scoped BigOperators
open PrimitiveWork

abbrev Mask (b : ℕ) := Vector Bool b

def enumerate : (b : ℕ) → Result (List (Mask b))
  | 0 => ⟨[#v[]], 2⟩
  | b + 1 =>
    let small := enumerate b
    let off := PrimitiveWork.map (fun v => ⟨v.push false, b + 2⟩) small.value
    let on := PrimitiveWork.map (fun v => ⟨v.push true, b + 2⟩) small.value
    let joined := FiniteLoopWork.append off.value on.value
    ⟨joined.value, small.work + off.work + on.work + joined.work + 3⟩

@[simp] theorem enumerate_zero : (enumerate 0).value = [#v[]] := rfl

@[simp] theorem enumerate_succ (b : ℕ) :
    (enumerate (b + 1)).value = ((enumerate b).value.map (fun v => v.push false)) ++
      ((enumerate b).value.map (fun v => v.push true)) := by
  simp only [enumerate, FiniteLoopWork.append_value, PrimitiveWork.map_value]

@[simp] theorem enumerate_length (b : ℕ) : (enumerate b).value.length = 2 ^ b := by
  induction b with
  | zero => rfl
  | succ b ih => simp [enumerate_succ, ih, pow_succ, Nat.mul_two]

theorem enumerate_complete (b : ℕ) (v : Mask b) : v ∈ (enumerate b).value := by
  induction b with
  | zero =>
    have hv : v = #v[] := by ext i hi; omega
    simp [hv]
  | succ b ih =>
    rw [enumerate_succ, List.mem_append]
    have hm := ih v.pop
    cases hb : v.back
    · left
      exact List.mem_map.mpr ⟨v.pop, hm, by simpa only [hb] using Vector.push_pop_back v⟩
    · right
      exact List.mem_map.mpr ⟨v.pop, hm, by simpa only [hb] using Vector.push_pop_back v⟩

theorem enumerate_nodup (b : ℕ) : (enumerate b).value.Nodup := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [enumerate_succ, List.nodup_append]
    refine ⟨ih.map (fun _ _ h => Vector.pop_eq_of_push_eq h),
      ih.map (fun _ _ h => Vector.pop_eq_of_push_eq h), ?_⟩
    intro v hv w hw heq
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a', _, rfl⟩ := List.mem_map.mp hw
    have hbad := Vector.back_eq_of_push_eq heq
    cases hbad

def enumerationBound (b : ℕ) : ℕ := 8 * (b + 1) * 2 ^ b

theorem enumerate_work (b : ℕ) : (enumerate b).work ≤ enumerationBound b := by
  induction b with
  | zero => norm_num [enumerate, enumerationBound]
  | succ b ih =>
    have hoff := PrimitiveWork.map_work_le (fun v : Mask b => (⟨v.push false, b + 2⟩ : Result (Mask (b + 1))))
      (enumerate b).value (b + 2) (fun _ _ => le_rfl)
    have hon := PrimitiveWork.map_work_le (fun v : Mask b => (⟨v.push true, b + 2⟩ : Result (Mask (b + 1))))
      (enumerate b).value (b + 2) (fun _ _ => le_rfl)
    simp only [enumerate_length] at hoff hon
    have hjoin := FiniteLoopWork.append_work
      ((PrimitiveWork.map (fun v : Mask b => (⟨v.push false, b + 2⟩ : Result (Mask (b + 1))))) (enumerate b).value).value
      ((PrimitiveWork.map (fun v : Mask b => (⟨v.push true, b + 2⟩ : Result (Mask (b + 1))))) (enumerate b).value).value
    simp only [PrimitiveWork.map_value, List.length_map, enumerate_length] at hjoin
    have hp : 0 < 2 ^ b := Nat.pow_pos (by decide)
    change (enumerate b).work + _ + _ + _ + 3 ≤ _
    simp only [PrimitiveWork.map_value]
    unfold enumerationBound at ih ⊢
    rw [pow_succ]
    nlinarith

def asSet {b : ℕ} (v : Mask b) : Finset (Fin b) := Finset.univ.filter (fun x => v[x] = true)

@[simp] theorem mem_asSet {b : ℕ} (v : Mask b) (x : Fin b) : x ∈ asSet v ↔ v[x] = true := by
  simp [asSet]

def encode {b : ℕ} (s : Finset (Fin b)) : Mask b := Vector.ofFn (fun x => decide (x ∈ s))

@[simp] theorem asSet_encode {b : ℕ} (s : Finset (Fin b)) : asSet (encode s) = s := by
  ext x
  simp [encode]

theorem asSet_injective {b : ℕ} : Function.Injective (@asSet b) := by
  intro v w heq
  ext i hi
  apply Bool.eq_iff_iff.mpr
  have hm : (⟨i, hi⟩ : Fin b) ∈ asSet v ↔ (⟨i, hi⟩ : Fin b) ∈ asSet w := by rw [heq]
  simpa only [mem_asSet, Fin.getElem_fin] using hm

theorem asSets_nodup (b : ℕ) : ((enumerate b).value.map asSet).Nodup :=
  (enumerate_nodup b).map asSet_injective

theorem asSets_toFinset (b : ℕ) : ((enumerate b).value.map asSet).toFinset = Finset.univ := by
  ext s
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_univ, iff_true]
  exact ⟨encode s, enumerate_complete b (encode s), asSet_encode s⟩

theorem sum_enumerate (b : ℕ) (f : Finset (Fin b) → ℕ) :
    ((enumerate b).value.map (fun v => f (asSet v))).sum = ∑ s : Finset (Fin b), f s := by
  change ((enumerate b).value.map (f ∘ asSet)).sum = _
  rw [← List.map_map]
  rw [← List.sum_toFinset f (asSets_nodup b), asSets_toFinset]

def allFin {b : ℕ} (f : Fin b → Result Bool) : Result Bool :=
  let domain := FiniteLoopWork.indices b
  let result := PrimitiveWork.all f domain.value
  ⟨result.value, domain.work + result.work⟩

@[simp] theorem allFin_true {b : ℕ} (f : Fin b → Result Bool) :
    (allFin f).value = true ↔ ∀ x, (f x).value = true := by
  simp [allFin, FiniteLoopWork.indices, List.all_eq_true]

theorem allFin_work {b : ℕ} (f : Fin b → Result Bool) (C : ℕ) (cost : ∀ x, (f x).work ≤ C) :
    (allFin f).work ≤ b * (C + 6) + 4 := by
  have hh := PrimitiveWork.all_work_le f (List.finRange b) C (fun x _ => cost x)
  simp only [List.length_finRange] at hh
  change (3 * b + 1) + (PrimitiveWork.all f (List.finRange b)).work ≤ _
  simp only [Nat.mul_add] at hh ⊢
  omega

def equal {b : ℕ} (v w : Mask b) : Result Bool :=
  allFin (fun x => ⟨decide (v[x] = w[x]), 3⟩)

@[simp] theorem equal_true {b : ℕ} (v w : Mask b) : (equal v w).value = true ↔ v = w := by
  simp only [equal, allFin_true, decide_eq_true_eq]
  constructor
  · intro h
    ext i hi
    exact h ⟨i, hi⟩
  · intro h x
    rw [h]

theorem equal_work {b : ℕ} (v w : Mask b) : (equal v w).work ≤ 9 * b + 4 := by
  simpa [equal, Nat.mul_comm] using allFin_work (fun x : Fin b => (⟨decide (v[x] = w[x]), 3⟩ : Result Bool)) 3 (fun _ => le_rfl)

def empty {b : ℕ} (v : Mask b) : Result Bool := allFin (fun x => ⟨!v[x], 2⟩)

@[simp] theorem empty_true {b : ℕ} (v : Mask b) : (empty v).value = true ↔ asSet v = ∅ := by
  simp [empty, Finset.eq_empty_iff_forall_notMem]

theorem empty_work {b : ℕ} (v : Mask b) : (empty v).work ≤ 8 * b + 4 := by
  simpa [empty, Nat.mul_comm] using allFin_work (fun x : Fin b => (⟨!v[x], 2⟩ : Result Bool)) 2 (fun _ => le_rfl)

end SortingAdversary.Optimal.SubsetWork
