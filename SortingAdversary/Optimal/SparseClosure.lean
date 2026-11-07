import SortingAdversary.Optimal.WeakMaps
import Mathlib.Data.List.FinRange
import Init.Data.Vector.OfFn

/-!
# Sparse rows and their computable public closure

Floyd--Warshall closure preserves exactly the weak colour maps. The executable
version stores every intermediate Boolean matrix in vectors, so looking up an
old entry does not recursively recompute earlier stages. The instrumented
routine counts the matrix cells written by its explicit stages.
-/

namespace SortingAdversary.Optimal.SparseClosure

open WeakMaps WeakMaps.WeakSystem

abbrev Rows (α : Type*) := α → α → Bool

variable {α : Type*}

def via (R : Rows α) (k : α) : Rows α :=
  fun u v => R u v || (R u k && R k v)

@[simp] theorem via_true (R : Rows α) (k u v : α) :
    via R k u v = true ↔ R u v = true ∨ (R u k = true ∧ R k v = true) := by
  simp [via]

def ClosedAt (R : Rows α) (k : α) : Prop :=
  ∀ u v, R u k = true → R k v = true → R u v = true

theorem via_closed (R : Rows α) (k : α) : ClosedAt (via R k) k := by
  intro u v huk hkv
  have huk' : R u k = true := ((via_true R k u k).mp huk).elim id And.left
  have hkv' : R k v = true := ((via_true R k k v).mp hkv).elim id And.right
  exact (via_true R k u v).mpr (Or.inr ⟨huk', hkv'⟩)

theorem via_preserves {R : Rows α} {j : α} (hj : ClosedAt R j) (k : α) :
    ClosedAt (via R k) j := by
  intro u v huj hjv
  apply (via_true R k u v).mpr
  rcases (via_true R k u j).mp huj with huj | ⟨huk, hkj⟩
  · rcases (via_true R k j v).mp hjv with hjv | ⟨hjk, hkv⟩
    · exact Or.inl (hj u v huj hjv)
    · exact Or.inr ⟨hj u k huj hjk, hkv⟩
  · rcases (via_true R k j v).mp hjv with hjv | ⟨_, hkv⟩
    · exact Or.inr ⟨huk, hj k v hkj hjv⟩
    · exact Or.inr ⟨huk, hkv⟩

def along (R : Rows α) : List α → Rows α
  | [] => R
  | k :: ks => along (via R k) ks

theorem along_old (ks : List α) (R : Rows α) {u v : α} (huv : R u v = true) :
    along R ks u v = true := by
  induction ks generalizing R with
  | nil => exact huv
  | cons k ks ih => exact ih (via R k) ((via_true R k u v).mpr (Or.inl huv))

theorem along_preserves (ks : List α) (R : Rows α) {j : α} (hj : ClosedAt R j) :
    ClosedAt (along R ks) j := by
  induction ks generalizing R with
  | nil => exact hj
  | cons k ks ih => exact ih _ (via_preserves hj k)

theorem along_closed (ks : List α) (R : Rows α) {j : α} (hj : j ∈ ks) :
    ClosedAt (along R ks) j := by
  induction ks generalizing R with
  | nil => simp at hj
  | cons k ks ih =>
      rcases List.mem_cons.mp hj with rfl | hj
      · exact along_preserves ks _ (via_closed R j)
      · exact ih _ hj

def Respects {β : Type*} [Preorder β] (R : Rows α) (f : α → β) : Prop :=
  ∀ u v, R u v = true → f u ≤ f v

theorem respects_via {β : Type*} [Preorder β] (R : Rows α) (k : α) (f : α → β) :
    Respects (via R k) f ↔ Respects R f := by
  constructor
  · intro h u v huv
    exact h u v ((via_true R k u v).mpr (Or.inl huv))
  · intro h u v huv
    rcases (via_true R k u v).mp huv with huv | ⟨huk, hkv⟩
    · exact h u v huv
    · exact (h u k huk).trans (h k v hkv)

theorem respects_along {β : Type*} [Preorder β] (ks : List α) (R : Rows α) (f : α → β) :
    Respects (along R ks) f ↔ Respects R f := by
  induction ks generalizing R with
  | nil => rfl
  | cons k ks ih => exact (ih _).trans (respects_via R k f)

def reflexive [DecidableEq α] (R : Rows α) : Rows α :=
  fun u v => R u v || decide (u = v)

@[simp] theorem respects_reflexive {β : Type*} [Preorder β] [DecidableEq α]
    (R : Rows α) (f : α → β) : Respects (reflexive R) f ↔ Respects R f := by
  constructor
  · intro h u v huv
    apply h u v
    simp [reflexive, huv]
  · intro h u v huv
    have hh : R u v = true ∨ u = v := by simpa [reflexive] using huv
    rcases hh with huv | rfl
    · exact h u v huv
    · exact le_rfl

def closure {n : ℕ} (R : Rows (Fin n)) : Rows (Fin n) :=
  along (reflexive R) (List.finRange n)

theorem closure_refl {n : ℕ} (R : Rows (Fin n)) (v : Fin n) : closure R v v = true := by
  apply along_old
  simp [reflexive]

theorem closure_trans {n : ℕ} (R : Rows (Fin n)) (u v w : Fin n)
    (huv : closure R u v = true) (hvw : closure R v w = true) : closure R u w = true := by
  exact along_closed (List.finRange n) (reflexive R) (by simp) u w huv hvw

theorem closure_old {n : ℕ} (R : Rows (Fin n)) {u v : Fin n} (huv : R u v = true) :
    closure R u v = true := by
  apply along_old
  simp [reflexive, huv]

@[simp] theorem respects_closure {n : ℕ} {β : Type*} [Preorder β]
    (R : Rows (Fin n)) (f : Fin n → β) : Respects (closure R) f ↔ Respects R f := by
  exact (respects_along _ _ _).trans (respects_reflexive R f)

/-- An explicitly stored square Boolean table. -/
abbrev Table (n : ℕ) := Vector (Vector Bool n) n

def lookup {n : ℕ} (T : Table n) : Rows (Fin n) := fun u v => T[u][v]

def tabulate {n : ℕ} (R : Rows (Fin n)) : Table n :=
  Vector.ofFn (fun u => Vector.ofFn (fun v => R u v))

@[simp] theorem lookup_tabulate {n : ℕ} (R : Rows (Fin n)) : lookup (tabulate R) = R := by
  funext u v
  simp [lookup, tabulate]

def tableVia {n : ℕ} (T : Table n) (k : Fin n) : Table n := tabulate (via (lookup T) k)

@[simp] theorem lookup_tableVia {n : ℕ} (T : Table n) (k : Fin n) :
    lookup (tableVia T k) = via (lookup T) k := lookup_tabulate _

/-- Every stage materializes all entries of the next matrix once. -/
def tableAlong {n : ℕ} (T : Table n) : List (Fin n) → Table n
  | [] => T
  | k :: ks => tableAlong (tableVia T k) ks

theorem lookup_tableAlong {n : ℕ} (ks : List (Fin n)) (T : Table n) :
    lookup (tableAlong T ks) = along (lookup T) ks := by
  induction ks generalizing T with
  | nil => rfl
  | cons k ks ih => simpa [tableAlong, along] using ih (tableVia T k)

def tableClosure {n : ℕ} (R : Rows (Fin n)) : Table n :=
  tableAlong (tabulate (reflexive R)) (List.finRange n)

@[simp] theorem lookup_tableClosure {n : ℕ} (R : Rows (Fin n)) :
    lookup (tableClosure R) = closure R := by
  simp [tableClosure, lookup_tableAlong, closure]

/-- Close the sparse rows without changing any primitive colour list. -/
def closeSystem {n K : ℕ} (S : WeakSystem (Fin n) K) : WeakSystem (Fin n) K :=
  let T := tableClosure S.edge
  { S with edge := lookup T }

@[simp] theorem closeSystem_valid {n K : ℕ} (S : WeakSystem (Fin n) K)
    (f : ColorMap (Fin n) K) : (closeSystem S).Valid f ↔ S.Valid f := by
  change ((∀ v, S.lower v ≤ f v ∧ f v ≤ S.upper v) ∧
      Respects (lookup (tableClosure S.edge)) f) ↔
    ((∀ v, S.lower v ≤ f v ∧ f v ≤ S.upper v) ∧ Respects S.edge f)
  rw [lookup_tableClosure, respects_closure]

theorem closeSystem_closed {n K : ℕ} (S : WeakSystem (Fin n) K) : (closeSystem S).Closed := by
  constructor
  · intro v
    change lookup (tableClosure S.edge) v v = true
    rw [lookup_tableClosure]
    exact closure_refl S.edge v
  · intro u v w huv hvw
    change lookup (tableClosure S.edge) u v = true at huv
    change lookup (tableClosure S.edge) v w = true at hvw
    change lookup (tableClosure S.edge) u w = true
    rw [lookup_tableClosure] at *
    exact closure_trans S.edge u v w huv hvw

@[simp] theorem closeSystem_maps {n K : ℕ} (S : WeakSystem (Fin n) K) :
    (closeSystem S).maps = S.maps := by
  ext f
  simp

@[simp] theorem closeSystem_count {n K : ℕ} (S : WeakSystem (Fin n) K) :
    (closeSystem S).count = S.count := by simp [count]

/-- Propagate unary bounds through the public closure, while retaining the
original sparse generating rows for local computations. -/
def propagateSystem {n K : ℕ} (S : WeakSystem (Fin n) (K + 1)) :
    WeakSystem (Fin n) (K + 1) where
  edge := S.edge
  lower := (closeSystem S).effectiveLower
  upper := (closeSystem S).effectiveUpper

@[simp] theorem propagateSystem_valid {n K : ℕ} (S : WeakSystem (Fin n) (K + 1))
    (f : ColorMap (Fin n) (K + 1)) : (propagateSystem S).Valid f ↔ S.Valid f := by
  constructor
  · intro hf
    refine ⟨?_, hf.2⟩
    intro v
    have hc := closeSystem_closed S
    exact ⟨((closeSystem S).lower_le_effectiveLower (hc.refl v)).trans (hf.1 v).1,
      (hf.1 v).2.trans ((closeSystem S).effectiveUpper_le_upper (hc.refl v))⟩
  · intro hf
    refine ⟨?_, hf.2⟩
    have hc : (closeSystem S).Valid f := (closeSystem_valid S f).mpr hf
    exact fun v => (closeSystem S).valid_between_windows f hc v

@[simp] theorem propagateSystem_maps {n K : ℕ} (S : WeakSystem (Fin n) (K + 1)) :
    (propagateSystem S).maps = S.maps := by
  ext f
  simp

@[simp] theorem propagateSystem_count {n K : ℕ} (S : WeakSystem (Fin n) (K + 1)) :
    (propagateSystem S).count = S.count := by simp [count]

/-- The instrumented stored-table routine: its second component counts one
write for each cell of every materialized stage. -/
def tableAlongCounted {n : ℕ} (T : Table n) : List (Fin n) → Table n × ℕ
  | [] => (T, 0)
  | k :: ks =>
      let next := tableAlongCounted (tableVia T k) ks
      (next.1, n * n + next.2)

theorem tableAlongCounted_value {n : ℕ} (ks : List (Fin n)) (T : Table n) :
    (tableAlongCounted T ks).1 = tableAlong T ks := by
  induction ks generalizing T with
  | nil => rfl
  | cons k ks ih => exact ih (tableVia T k)

theorem tableAlongCounted_writes {n : ℕ} (ks : List (Fin n)) (T : Table n) :
    (tableAlongCounted T ks).2 = ks.length * (n * n) := by
  induction ks generalizing T with
  | nil => simp [tableAlongCounted]
  | cons k ks ih => simp [tableAlongCounted, ih, Nat.succ_mul, Nat.add_comm]

/-- Including the initial reflexive table, closure writes exactly this many
Boolean cells. This is a cell-write count, not a complete machine cost model. -/
theorem closure_cell_writes (n : ℕ) (R : Rows (Fin n)) :
    n * n + (tableAlongCounted (tabulate (reflexive R)) (List.finRange n)).2 =
      (n + 1) * n ^ 2 := by
  rw [tableAlongCounted_writes]
  simp [pow_two, Nat.add_mul, Nat.add_comm]

end SortingAdversary.Optimal.SparseClosure
