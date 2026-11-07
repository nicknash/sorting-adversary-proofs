import SortingAdversary.Optimal.RepresentationWork
import SortingAdversary.Optimal.WindowWork

/-!
# Measured scalar cell transformations

The fixed scalar charges pay for branches, finite-index comparisons,
successor/predecessor arithmetic, and constructors. Calls to old functional
fields retain their measured work. None of these transformations scans an
assignment space or reconstructs a function by choice.
-/

namespace SortingAdversary.Optimal.RepresentationWork

open PrimitiveWork WidthRepair FiniteRefinement

variable {n K L : ℕ}

def eraseVertex (rows : Fin n → Fin n → Result Bool) (v x y : Fin n) : Result Bool :=
  let old := rows x y
  ⟨if x = v ∨ y = v then false else old.value, old.work + 4⟩

def eraseRow (rows : Fin n → Fin n → Result Bool) (u v x y : Fin n) : Result Bool :=
  let old := rows x y
  ⟨if x = u ∧ y = v then false else old.value, old.work + 4⟩

@[simp] theorem eraseVertex_value {s : State n} (a : LocalAccess s) (v x y : Fin n) :
    (eraseVertex a.active v x y).value = SparseRepairGraph.eraseVertex s.rows.active v x y := by
  by_cases hx : x = v <;> by_cases hy : y = v <;>
    simp [eraseVertex, a.active_value, SparseRepairGraph.eraseVertex, hx, hy]

@[simp] theorem eraseRow_value {s : State n} (a : LocalAccess s) (u v x y : Fin n) :
    (eraseRow a.active u v x y).value = SparseRepairGraph.eraseRow s.rows.active u v x y := by
  simp only [eraseRow, a.active_value, SparseRepairGraph.eraseRow]

def pinLower (lower : Fin n → Result (Fin K)) (v : Fin n) (c : Fin K) (x : Fin n) :
    Result (Fin K) :=
  let old := lower x
  ⟨if x = v then max old.value c else old.value, old.work + 3⟩

def pinUpper (upper : Fin n → Result (Fin K)) (v : Fin n) (c : Fin K) (x : Fin n) :
    Result (Fin K) :=
  let old := upper x
  ⟨if x = v then min old.value c else old.value, old.work + 3⟩

def embedAfter (c x : Fin K) : Result (Fin (K + 1)) := ⟨embedColor c x, 3⟩
def embedBefore (c x : Fin K) : Result (Fin (K + 1)) := ⟨embedColorBefore c x, 3⟩
def embedUpper (c x : Fin K) : Result (Fin (K + 1)) := ⟨upperColor c x, 3⟩

def splitWall (pins : Fin n → Result (Option (Fin K))) (wall : Fin n → Result (Fin K))
    (fixedMap freeMap : Fin K → Result (Fin L)) (x : Fin n) : Result (Fin L) :=
  let pinned := pins x
  match pinned.value with
  | some c =>
    let mapped := fixedMap c
    ⟨mapped.value, pinned.work + mapped.work + 2⟩
  | none =>
    let old := wall x
    let mapped := freeMap old.value
    ⟨mapped.value, pinned.work + old.work + mapped.work + 2⟩

theorem splitWall_work_le (pins : Fin n → Result (Option (Fin K)))
    (wall : Fin n → Result (Fin K)) (fixedMap freeMap : Fin K → Result (Fin L))
    (x : Fin n) (A B : ℕ) (hp : (pins x).work ≤ A) (hw : (wall x).work ≤ A)
    (hf : ∀ c, (fixedMap c).work ≤ B) (hg : ∀ c, (freeMap c).work ≤ B) :
    (splitWall pins wall fixedMap freeMap x).work ≤ 2 * A + B + 2 := by
  simp only [splitWall]
  split
  · rename_i c hc
    have hh := hf c
    dsimp only
    omega
  · have hh := hg (wall x).value
    dsimp only
    omega

def pinMap (pins : Fin n → Result (Option (Fin K))) (embed : Fin K → Result (Fin L))
    (v : Fin n) (destination : Fin L) (x : Fin n) : Result (Option (Fin L)) :=
  if x = v then ⟨some destination, 2⟩
  else
    let old := pins x
    match old.value with
    | none => ⟨none, old.work + 2⟩
    | some c =>
      let mapped := embed c
      ⟨some mapped.value, old.work + mapped.work + 3⟩

theorem pinMap_work_le (pins : Fin n → Result (Option (Fin K)))
    (embed : Fin K → Result (Fin L)) (v : Fin n) (destination : Fin L) (x : Fin n)
    (A B : ℕ) (hp : (pins x).work ≤ A) (he : ∀ c, (embed c).work ≤ B) :
    (pinMap pins embed v destination x).work ≤ A + B + 3 := by
  simp only [pinMap]
  split
  · dsimp only; omega
  · split
    · dsimp only; omega
    · rename_i c hc
      have hh := he c
      dsimp only
      omega

/-- Explicit option decomposition executes at most one old permutation
lookup. Twelve covers all fixed finite-index arithmetic and case operations. -/
def extendForward (order : Fin K → Result (Fin K)) (fresh x : Fin (K + 1)) :
    Result (Fin (K + 1)) :=
  match finSuccEquiv' (Fin.last K) x with
  | none => ⟨fresh, 12⟩
  | some i =>
    let old := order i
    ⟨fresh.succAbove old.value, old.work + 12⟩

def extendInverse (inverse : Fin K → Result (Fin K)) (fresh x : Fin (K + 1)) :
    Result (Fin (K + 1)) :=
  match finSuccEquiv' fresh x with
  | none => ⟨Fin.last K, 12⟩
  | some i =>
    let old := inverse i
    ⟨old.value.castSucc, old.work + 12⟩

theorem extendForward_value (order : Equiv.Perm (Fin K)) (get : Fin K → Result (Fin K))
    (h : ∀ x, (get x).value = order x) (fresh x : Fin (K + 1)) :
    (extendForward get fresh x).value = PaletteBirthOrder.extend order fresh x := by
  cases he : finSuccEquiv' (Fin.last K) x with
  | none => simp [extendForward, PaletteBirthOrder.extend, he]
  | some i => simp [extendForward, PaletteBirthOrder.extend, he, h]

theorem extendInverse_value (order : Equiv.Perm (Fin K)) (get : Fin K → Result (Fin K))
    (h : ∀ x, (get x).value = order.symm x) (fresh x : Fin (K + 1)) :
    (extendInverse get fresh x).value = (PaletteBirthOrder.extend order fresh).symm x := by
  cases he : finSuccEquiv' fresh x with
  | none => simp [extendInverse, PaletteBirthOrder.extend, Equiv.optionCongr, he]
  | some i => simp [extendInverse, PaletteBirthOrder.extend, Equiv.optionCongr, he, h]

theorem extendForward_work_le (get : Fin K → Result (Fin K)) (fresh x : Fin (K + 1))
    (A : ℕ) (h : ∀ i, (get i).work ≤ A) : (extendForward get fresh x).work ≤ A + 12 := by
  simp only [extendForward]
  split
  · dsimp only; omega
  · exact Nat.add_le_add_right (h _) 12

theorem extendInverse_work_le (get : Fin K → Result (Fin K)) (fresh x : Fin (K + 1))
    (A : ℕ) (h : ∀ i, (get i).work ≤ A) : (extendInverse get fresh x).work ≤ A + 12 := by
  simp only [extendInverse]
  split
  · dsimp only; omega
  · exact Nat.add_le_add_right (h _) 12

namespace LocalAccess

def windows {s : State n} (a : LocalAccess s) : WindowWork.Input n s.pool.palette :=
  ⟨a.publicRow, a.lower, a.upper⟩

@[simp] theorem windows_system {s : State n} (a : LocalAccess s) :
    a.windows.system = s.pool.system := by
  cases hs : s.pool.system with
  | mk edge lower upper =>
    have he : (fun x y => (a.publicRow x y).value) = edge := by funext x y; simpa [hs] using a.publicRow_value x y
    have hl : (fun x => (a.lower x).value) = lower := by funext x; simpa [hs] using a.lower_value x
    have hu : (fun x => (a.upper x).value) = upper := by funext x; simpa [hs] using a.upper_value x
    simp only [windows, WindowWork.Input.system, he, hl, hu]

end LocalAccess

end SortingAdversary.Optimal.RepresentationWork
