import SortingAdversary.Continuous.OperandBounds

/-!
# Endpoint scans with charged rational comparisons

Scan the rows of the retained system and select the largest incoming
coordinate or smallest outgoing coordinate. Each comparison charges the
signed cross products of the two actual rationals.
-/

namespace SortingAdversary.Continuous.PolylogSweepProfile

open Optimal EnclosureWork OperandBounds
open Optimal.PrimitiveWork (Result)

private def pick (lower : Bool) (a b : ℚ) : Result ℚ :=
  let c := RationalBitWork.lessEqual a b
  ⟨if lower then (if c.result.value then b else a) else (if c.result.value then a else b),
    c.bitWork+2⟩

private theorem pick_max (a b : ℚ) : (pick true a b).value = max a b := by
  by_cases h : a ≤ b <;> simp [pick,h,max_def]

private theorem pick_min (a b : ℚ) : (pick false a b).value = min a b := by
  by_cases h : a ≤ b <;> simp [pick,h,min_def]

private theorem pick_fits {B : ℕ} (lower : Bool) {a b : ℚ} (ha : Fits B a) (hb : Fits B b) :
    Fits B (pick lower a b).value := by
  cases lower <;> simp only [pick, if_true, Bool.false_eq_true, if_false] <;>
    split <;> assumption

private def rows {m : ℕ} (lower : Bool) (edge : Fin m → Bool) (Y : Vector ℚ m) (base : ℚ) :
    List (Fin m) → Result ℚ
  | [] => ⟨base,1⟩
  | x::xs =>
    let tail := rows lower edge Y base xs
    if edge x then
      let q := pick lower Y[x] tail.value
      ⟨q.value,tail.work+q.work+4⟩
    else ⟨tail.value,tail.work+3⟩

private theorem lower_le (edge : Fin m → Bool) (Y : Vector ℚ m) (base t : ℚ) (xs : List (Fin m)) :
    (rows true edge Y base xs).value ≤ t ↔
      base ≤ t ∧ ∀ y ∈ xs, edge y = true → Y[y] ≤ t := by
  induction xs with
  | nil => simp [rows]
  | cons x xs ih =>
    cases h : edge x <;> simp [rows,h,pick_max,ih]
    tauto

private theorem le_upper (edge : Fin m → Bool) (Y : Vector ℚ m) (base t : ℚ) (xs : List (Fin m)) :
    t ≤ (rows false edge Y base xs).value ↔
      t ≤ base ∧ ∀ y ∈ xs, edge y = true → t ≤ Y[y] := by
  induction xs with
  | nil => simp [rows]
  | cons x xs ih =>
    cases h : edge x <;> simp [rows,h,pick_min,ih]
    tauto

private theorem rows_cost (lower : Bool) (edge : Fin m → Bool) (Y : Vector ℚ m) (base : ℚ)
    (xs : List (Fin m)) {B : ℕ} (hY : ∀ y : Fin m, Fits B Y[y]) (hb : Fits B base) :
    Fits B (rows lower edge Y base xs).value ∧
      (rows lower edge Y base xs).work ≤ 1+xs.length*(128*(B+1)^3+6) := by
  induction xs with
  | nil => simpa [rows]
  | cons x xs ih =>
    obtain ⟨ht,hw⟩ := ih
    cases e : edge x with
    | false =>
      simp only [rows,e,Bool.false_eq_true,if_false,List.length_cons]
      rw [Nat.succ_mul xs.length]
      exact ⟨ht,by omega⟩
    | true =>
      simp only [rows,e,if_true,List.length_cons]
      rw [Nat.succ_mul xs.length]
      refine ⟨pick_fits lower (hY x) ht,?_⟩
      have h := comparison_bit_charge (hY x) ht
      simp only [pick]; omega

def scan (lower : Bool) (D : StoredSystem m) (i : Fin m) (Y : Vector ℚ m) : Result ℚ :=
  let edge := fun y : Fin m => if lower then D.edge[y][i] else D.edge[i][y]
  let base := if lower then D.lower[i] else D.upper[i]
  let r := rows lower edge Y base (List.finRange m)
  ⟨r.value,r.work+4*m+3⟩

theorem scan_lower_value (D : StoredSystem m) (i : Fin m) (Y : Vector ℚ m) :
    (scan true D i Y).value = (EnclosureWork.conditionalLower D i Y).value := by
  apply le_antisymm_iff.mpr
  have h (t : ℚ) : (scan true D i Y).value ≤ t ↔ (EnclosureWork.conditionalLower D i Y).value ≤ t := by
    simp only [scan,if_true,lower_le,List.mem_finRange,forall_const,conditionalLower_value,
      FiniteAveraging.conditionalLower,Finset.fold_max_le,
      StoredSystem.system,values,SparseClosure.lookup]
    apply and_congr_right
    intro _
    exact ⟨fun h x hx => h x (Finset.mem_filter.mp hx).2,
      fun h x hx => h x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)⟩
  exact ⟨(h _).2 le_rfl,(h _).1 le_rfl⟩

theorem scan_upper_value (D : StoredSystem m) (i : Fin m) (Y : Vector ℚ m) :
    (scan false D i Y).value = (EnclosureWork.conditionalUpper D i Y).value := by
  apply le_antisymm_iff.mpr
  have h (t : ℚ) : t ≤ (scan false D i Y).value ↔ t ≤ (EnclosureWork.conditionalUpper D i Y).value := by
    simp only [scan,Bool.false_eq_true,if_false,le_upper,List.mem_finRange,forall_const,conditionalUpper_value,
      FiniteAveraging.conditionalUpper,Finset.le_fold_min,
      StoredSystem.system,values,SparseClosure.lookup]
    apply and_congr_right
    intro _
    exact ⟨fun h x hx => h x (Finset.mem_filter.mp hx).2,
      fun h x hx => h x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)⟩
  exact ⟨(h _).1 le_rfl,(h _).2 le_rfl⟩

theorem scan_fits (lower : Bool) (D : StoredSystem m) (i : Fin m) (Y : Vector ℚ m) {B : ℕ}
    (hY : ∀ x : Fin m, Fits B Y[x]) (hl : Fits B D.lower[i]) (hu : Fits B D.upper[i]) :
    Fits B (scan lower D i Y).value :=
  (rows_cost lower _ _ _ _ hY (by cases lower <;> assumption)).1

theorem scan_work (lower : Bool) (D : StoredSystem m) (i : Fin m) (Y : Vector ℚ m) {B : ℕ}
    (hY : ∀ x : Fin m, Fits B Y[x]) (hl : Fits B D.lower[i]) (hu : Fits B D.upper[i]) :
    (scan lower D i Y).work ≤ (m+1)*(128*(B+1)^3+15) := by
  have hb : Fits B (if lower then D.lower[i] else D.upper[i]) := by cases lower <;> assumption
  have h := (rows_cost lower (fun y : Fin m => if lower then D.edge[y][i] else D.edge[i][y]) Y
    _ (List.finRange m) hY hb).2
  simp only [List.length_finRange] at h
  let C := 128*(B+1)^3
  change _ ≤ 1 + m*(C+6) at h
  change _ + 4*m + 3 ≤ (m+1)*(C+15)
  rw [Nat.mul_add m] at h
  rw [Nat.add_mul,Nat.mul_add m,Nat.one_mul]
  omega

end SortingAdversary.Continuous.PolylogSweepProfile
