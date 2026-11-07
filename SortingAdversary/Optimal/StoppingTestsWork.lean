import SortingAdversary.Optimal.WindowWork
import SortingAdversary.Optimal.ControllerRouting

/-!
# Measured finite safety tests at a stopping node

Every branch window is evaluated into a finite table. Feasibility and free
singleton tests scan those tables, and inner-order witnesses scan pairs of
labels and compare their actual optional pins. No colour assignments are
enumerated. The returned action has the reference controller's exact priority.
-/

namespace SortingAdversary.Optimal.StoppingTestsWork

open PrimitiveWork WindowWork ControllerRouting

variable {n K : ℕ}

def closedRow (rows : Fin n → Fin n → Result Bool) (a b u v : Fin n) : Result Bool :=
  let old := rows u v
  let into := rows u a
  let out := rows b v
  ⟨old.value || (into.value && out.value), old.work + into.work + out.work + 2⟩

def adjoined (input : Input n K) (a b : Fin n) : Input n K :=
  ⟨closedRow input.edge a b, input.lower, input.upper⟩

@[simp] theorem adjoined_system (input : Input n K) (a b : Fin n) :
    (adjoined input a b).system = Safety.closedAdd input.system a b := rfl

def windows (input : Input n K) (a b : Fin n) : Result (Vector (Fin (K + 1) × Fin (K + 1)) n) :=
  PrimitiveWork.vector fun v =>
    let lower := effectiveLower (adjoined input a b) v
    let upper := effectiveUpper (adjoined input a b) v
    ⟨(lower.value, upper.value), lower.work + upper.work + 1⟩

@[simp] theorem windows_get (input : Input n K) (a b v : Fin n) :
    (windows input a b).value[v] =
      ((Safety.closedAdd input.system a b).effectiveLower v,
        (Safety.closedAdd input.system a b).effectiveUpper v) := by
  simp only [windows, PrimitiveWork.vector_value, Fin.getElem_fin, Vector.getElem_ofFn,
    effectiveLower_value, effectiveUpper_value, adjoined_system]

def windowsBound (n A : ℕ) : ℕ := n * (2 * endpointWorkBound n (3 * A + 2) A + 3)

theorem windows_work_le (input : Input n K) (a b : Fin n) (A : ℕ)
    (he : ∀ u v, (input.edge u v).work ≤ A)
    (hl : ∀ v, (input.lower v).work ≤ A) (hu : ∀ v, (input.upper v).work ≤ A) :
    (windows input a b).work ≤ windowsBound n A := by
  have hed : ∀ u v, ((adjoined input a b).edge u v).work ≤ 3 * A + 2 := by
    intro u v
    have h1 := he u v
    have h2 := he u a
    have h3 := he b v
    change _ + _ + _ + 2 ≤ _
    omega
  exact PrimitiveWork.vector_work_le _ (2 * endpointWorkBound n (3 * A + 2) A + 1) (fun v => by
    have h1 := effectiveLower_work_le (adjoined input a b) v (3 * A + 2) A (fun u => hed u v) hl
    have h2 := effectiveUpper_work_le (adjoined input a b) v (3 * A + 2) A (hed v) hu
    change _ + _ + 1 ≤ _
    omega)

def feasible (table : Vector (Fin (K + 1) × Fin (K + 1)) n) : Result Bool :=
  let domain := FiniteLoopWork.indices n
  let answer := PrimitiveWork.all (fun v => let row := table[v]; ⟨decide (row.1 ≤ row.2), 4⟩) domain.value
  ⟨answer.value, domain.work + answer.work + 1⟩

@[simp] theorem feasible_value (table : Vector (Fin (K + 1) × Fin (K + 1)) n) :
    (feasible table).value = decide (∀ v : Fin n, table[v].1 ≤ table[v].2) := by
  apply Bool.eq_iff_iff.mpr
  simp [feasible, PrimitiveWork.all_value, FiniteLoopWork.indices, List.all_eq_true]

theorem feasible_work_le (table : Vector (Fin (K + 1) × Fin (K + 1)) n) :
    (feasible table).work ≤ 10 * n + 5 := by
  have h := PrimitiveWork.all_work_le (fun v => (⟨decide (table[v].1 ≤ table[v].2), 4⟩ : Result Bool))
    (List.finRange n) 4 (fun _ _ => le_rfl)
  simp only [List.length_finRange, Nat.reduceAdd] at h
  dsimp only [feasible, FiniteLoopWork.indices]
  omega

def singleton (pins : Fin n → Result (Option (Fin (K + 1))))
    (table : Vector (Fin (K + 1) × Fin (K + 1)) n) : Result Bool :=
  let domain := FiniteLoopWork.indices n
  let answer := PrimitiveWork.any (fun v =>
    let pin := pins v
    ⟨decide (pin.value = none ∧ table[v].1 = table[v].2), pin.work + 7⟩) domain.value
  ⟨answer.value, domain.work + answer.work + 1⟩

@[simp] theorem singleton_value (pins : Fin n → Result (Option (Fin (K + 1))))
    (table : Vector (Fin (K + 1) × Fin (K + 1)) n) :
    (singleton pins table).value = decide (∃ v : Fin n, (pins v).value = none ∧ table[v].1 = table[v].2) := by
  apply Bool.eq_iff_iff.mpr
  simp [singleton, PrimitiveWork.any_value, FiniteLoopWork.indices, List.any_eq_true]

theorem singleton_work_le (pins : Fin n → Result (Option (Fin (K + 1))))
    (table : Vector (Fin (K + 1) × Fin (K + 1)) n) (A : ℕ) (hA : ∀ v, (pins v).work ≤ A) :
    (singleton pins table).work ≤ 3 * n + n * (A + 9) + 4 := by
  have h := PrimitiveWork.any_work_le (fun v =>
    (⟨decide ((pins v).value = none ∧ table[v].1 = table[v].2), (pins v).work + 7⟩ : Result Bool))
    (List.finRange n) (A + 7) (fun v _ => Nat.add_le_add_right (hA v) 7)
  simp only [List.length_finRange, Nat.add_assoc, Nat.reduceAdd] at h
  dsimp only [singleton, FiniteLoopWork.indices]
  omega

def samePin (pins : Fin n → Result (Option (Fin (K + 1)))) (u v : Fin n) : Result Bool :=
  let first := pins u
  let second := pins v
  ⟨match first.value with
   | none => false
   | some c => decide (second.value = some c), first.work + second.work + 3⟩

@[simp] theorem samePin_value (pins : Fin n → Result (Option (Fin (K + 1)))) (u v : Fin n) :
    (samePin pins u v).value = decide (∃ c, (pins u).value = some c ∧ (pins v).value = some c) := by
  cases h : (pins u).value <;> simp [samePin, h]

def innerCell (rows : Fin n → Fin n → Result Bool)
    (pins : Fin n → Result (Option (Fin (K + 1)))) (a b u v : Fin n) : Result Bool :=
  let same := samePin pins u v
  let into := rows u a
  let out := rows b v
  let old := rows u v
  ⟨same.value && into.value && out.value && !old.value,
    same.work + into.work + out.work + old.work + 4⟩

def inner (rows : Fin n → Fin n → Result Bool)
    (pins : Fin n → Result (Option (Fin (K + 1)))) (a b : Fin n) : Result Bool :=
  let pairs := FiniteLoopWork.pairs n
  let answer := PrimitiveWork.any (fun uv => innerCell rows pins a b uv.1 uv.2) pairs.value
  ⟨answer.value, pairs.work + answer.work + 1⟩

@[simp] theorem inner_value (input : Input n K)
    (pins : Fin n → Result (Option (Fin (K + 1)))) (a b : Fin n) :
    (inner input.edge pins a b).value =
      decide (Inner input.system (fun v => (pins v).value) a b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [inner, PrimitiveWork.any_value, FiniteLoopWork.pairs_value, List.any_eq_true,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map, exists_and_left,
    innerCell, Bool.and_eq_true, Bool.not_eq_true, samePin_value, decide_eq_true_eq,
    Inner, Routing.InnerWitness, Input.system]
  constructor
  · rintro ⟨uv, ⟨u, v, rfl⟩, ⟨⟨⟨c, hc, hd⟩, hua⟩, hbv⟩, huv⟩
    exact ⟨u, v, c, hc, hd, hua, hbv, by simpa using huv⟩
  · rintro ⟨u, v, c, hc, hd, hua, hbv, huv⟩
    exact ⟨(u, v), ⟨u, v, rfl⟩,
      ⟨⟨⟨c, hc, hd⟩, hua⟩, hbv⟩, by simpa using huv⟩

def innerBound (n A : ℕ) : ℕ :=
  3 * n + n * (5 * n + 3) + n * n * (5 * A + 9) + 5

theorem inner_work_le (rows : Fin n → Fin n → Result Bool)
    (pins : Fin n → Result (Option (Fin (K + 1)))) (a b : Fin n) (A : ℕ)
    (he : ∀ u v, (rows u v).work ≤ A) (hp : ∀ v, (pins v).work ≤ A) :
    (inner rows pins a b).work ≤ innerBound n A := by
  have hc : ∀ uv : Fin n × Fin n, (innerCell rows pins a b uv.1 uv.2).work ≤ 5 * A + 7 := by
    rintro ⟨u, v⟩
    have h1 := hp u
    have h2 := hp v
    have h3 := he u a
    have h4 := he b v
    have h5 := he u v
    dsimp only [innerCell, samePin]
    omega
  have hs := PrimitiveWork.any_work_le (fun uv : Fin n × Fin n => innerCell rows pins a b uv.1 uv.2)
    (FiniteLoopWork.pairs n).value (5 * A + 7) (fun uv _ => hc uv)
  rw [FiniteLoopWork.pairs_length] at hs
  simp only [Nat.add_assoc, Nat.reduceAdd] at hs
  have hpairs := FiniteLoopWork.pairs_work_le n
  change _ + _ + 1 ≤ _
  unfold innerBound
  omega


@[simp] theorem singleton_windows (input : Input n K)
    (pins : Fin n → Result (Option (Fin (K + 1)))) (a b : Fin n) :
    (singleton pins (windows input a b).value).value =
      decide (SingletonTest input.system (fun v => (pins v).value) a b) := by
  rw [singleton_value]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold SingletonTest
  simp only [windows_get]

def fromTests (ff rf fi ri fs rs : Bool) : Action :=
  if !ff then .reverse
  else if !rf then .forward
  else if fi then if ri then .delegate else .reverse
  else if ri then .forward
  else if fs then .reverse
  else if rs then .forward
  else .compareMasses

def route (input : Input n K) (pins : Fin n → Result (Option (Fin (K + 1))))
    (a b : Fin n) : Result Action :=
  let forward := windows input a b
  let reverse := windows input b a
  let ff := feasible forward.value
  let rf := feasible reverse.value
  let fi := inner input.edge pins a b
  let ri := inner input.edge pins b a
  let fs := singleton pins forward.value
  let rs := singleton pins reverse.value
  ⟨fromTests ff.value rf.value fi.value ri.value fs.value rs.value,
    forward.work + reverse.work + ff.work + rf.work + fi.work + ri.work + fs.work + rs.work + 8⟩

theorem route_value (input : Input n K) (pins : Fin n → Result (Option (Fin (K + 1))))
    (h : Invariant input.system (fun v => (pins v).value)) (a b : Fin n)
    (hab : input.system.edge a b ≠ true) (hba : input.system.edge b a ≠ true) :
    (route input pins a b).value =
      (chooseRoute input.system (fun v => (pins v).value) h a b hab hba).val := by
  simp only [route, feasible_value, singleton_windows, inner_value, windows_get]
  unfold fromTests chooseRoute
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  split_ifs <;> rfl

def workBound (n A : ℕ) : ℕ :=
  2 * windowsBound n A + 2 * (10 * n + 5) + 2 * innerBound n A +
    2 * (3 * n + n * (A + 9) + 4) + 8

theorem route_work_le (input : Input n K) (pins : Fin n → Result (Option (Fin (K + 1))))
    (a b : Fin n) (A : ℕ) (he : ∀ u v, (input.edge u v).work ≤ A)
    (hl : ∀ v, (input.lower v).work ≤ A) (hu : ∀ v, (input.upper v).work ≤ A)
    (hp : ∀ v, (pins v).work ≤ A) :
    (route input pins a b).work ≤ workBound n A := by
  have hfw := windows_work_le input a b A he hl hu
  have hrw := windows_work_le input b a A he hl hu
  have hff := feasible_work_le (windows input a b).value
  have hrf := feasible_work_le (windows input b a).value
  have hfi := inner_work_le input.edge pins a b A he hp
  have hri := inner_work_le input.edge pins b a A he hp
  have hfs := singleton_work_le pins (windows input a b).value A hp
  have hrs := singleton_work_le pins (windows input b a).value A hp
  change _ + _ + _ + _ + _ + _ + _ + _ + 8 ≤ _
  unfold workBound
  omega

end SortingAdversary.Optimal.StoppingTestsWork
