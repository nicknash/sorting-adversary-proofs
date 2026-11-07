import SortingAdversary.Optimal.StoppingTestsWork
import SortingAdversary.Optimal.LongestPathWork
import SortingAdversary.Optimal.RepresentationShape
import SortingAdversary.Optimal.RecursiveController

/-!
# A measured physical-comparison update

The explicit single-new-edge closure formula updates the public matrix.
Source rows record the physical comparison, and active rows add it only
when both endpoints are free. Every resulting getter is then materialized;
the resulting State is built from those arrays and the supplied persistent
shape. The reference comparison state is an erased proof index.
-/

namespace SortingAdversary.Optimal.ComparedWork

open PrimitiveWork RepresentationWork WidthRepair ControllerRouting

variable {n : ℕ} {s : State n}

def sourceRow (rows : Fin n → Fin n → Result Bool) (a b x y : Fin n) : Result Bool :=
  let old := rows x y
  ⟨old.value || decide (x = a ∧ y = b), old.work + 4⟩

def activeRow {K : ℕ} (rows : Fin n → Fin n → Result Bool)
    (pins : Fin n → Result (Option (Fin K))) (a b x y : Fin n) : Result Bool :=
  let old := rows x y
  let first := pins a
  let second := pins b
  ⟨old.value || decide (x = a ∧ y = b ∧ first.value = none ∧ second.value = none),
    old.work + first.work + second.work + 8⟩

def access (a : LocalAccess s) (first second : Fin n)
    (hf : first ∈ s.pool.members) (hs : second ∈ s.pool.members) (hne : first ≠ second)
    (hi : Invariant (Safety.closedAdd s.pool.system first second) s.pool.pins) :
    LocalAccess (RecursiveController.compared s first second hf hs hne hi) where
  publicRow := StoppingTestsWork.closedRow a.publicRow first second
  source := sourceRow a.source first second
  active := activeRow a.active a.pin first second
  lower := a.lower
  upper := a.upper
  pin := a.pin
  member := a.member
  order := a.order
  inverse := a.inverse
  publicRow_value := by
    intro x y
    change (StoppingTestsWork.closedRow a.publicRow first second x y).value =
      (s.pool.system.edge x y || (s.pool.system.edge x first && s.pool.system.edge second y))
    simp only [StoppingTestsWork.closedRow, a.publicRow_value]
  source_value := by
    intro x y
    change (sourceRow a.source first second x y).value = SparseRepairGraph.addRow s.rows.source first second x y
    simp only [sourceRow, a.source_value, SparseRepairGraph.addRow]
  active_value := by
    intro x y
    change (activeRow a.active a.pin first second x y).value =
      (s.rows.active x y || decide (x = first ∧ y = second ∧ s.pool.pins first = none ∧ s.pool.pins second = none))
    simp only [activeRow, a.active_value, a.pin_value]
  lower_value := a.lower_value
  upper_value := a.upper_value
  pin_value := a.pin_value
  member_value := a.member_value
  order_value := a.order_value
  inverse_value := a.inverse_value

theorem access_bound (a : LocalAccess s) {A : ℕ} (hA : AccessBound a A)
    (first second : Fin n) (hf : first ∈ s.pool.members) (hs : second ∈ s.pool.members)
    (hne : first ≠ second) (hi : Invariant (Safety.closedAdd s.pool.system first second) s.pool.pins) :
    AccessBound (access a first second hf hs hne hi) (3 * A + 10) := by
  constructor
  · intro x y
    have h1 := hA.publicRow x y
    have h2 := hA.publicRow x first
    have h3 := hA.publicRow second y
    change _ + _ + _ + 2 ≤ _
    omega
  · intro x y
    have h := hA.source x y
    change _ + 4 ≤ _
    omega
  · intro x y
    have h1 := hA.active x y
    have h2 := hA.pin first
    have h3 := hA.pin second
    change _ + _ + _ + 8 ≤ _
    omega
  · intro x; exact (hA.lower x).trans (by omega)
  · intro x; exact (hA.upper x).trans (by omega)
  · intro x; exact (hA.pin x).trans (by omega)
  · intro x; exact (hA.member x).trans (by omega)
  · intro x; exact (hA.order x).trans (by omega)
  · intro x; exact (hA.inverse x).trans (by omega)

structure Output (expected : State n) where
  state : State n
  access : LocalAccess state
  actual : state = expected
  cached : AccessBound access 2

def compare (a : LocalAccess s) (first second : Fin n)
    (hf : first ∈ s.pool.members) (hs : second ∈ s.pool.members) (hne : first ≠ second)
    (hi : Invariant (Safety.closedAdd s.pool.system first second) s.pool.pins)
    (palette : ℕ) (members : Finset (Fin n)) (hp : palette = s.pool.palette) (hm : members = s.pool.members) :
    Result (Output (RecursiveController.compared s first second hf hs hne hi)) :=
  let next := access a first second hf hs hne hi
  let cached := next.cacheWith palette hp
  let state := cached.value.realizeWith palette members hp hm
  ⟨⟨state, cached.value.rebasedWith palette members hp hm,
    cached.value.realizeWith_eq palette members hp hm,
    cached.value.rebasedWith_bound palette members hp hm (LocalAccess.cacheWith_access next palette hp)⟩,
    cached.work + 24⟩

theorem compare_work_le (a : LocalAccess s) {A : ℕ} (hA : AccessBound a A)
    (first second : Fin n) (hf : first ∈ s.pool.members) (hs : second ∈ s.pool.members)
    (hne : first ≠ second) (hi : Invariant (Safety.closedAdd s.pool.system first second) s.pool.pins)
    (palette : ℕ) (members : Finset (Fin n)) (hp : palette = s.pool.palette) (hm : members = s.pool.members) :
    (compare a first second hf hs hne hi palette members hp hm).work ≤
      LocalAccess.cacheBound n palette (3 * A + 10) + 24 := by
  exact Nat.add_le_add_right (LocalAccess.cacheWith_work_le
    (access a first second hf hs hne hi) palette hp (access_bound a hA first second hf hs hne hi)) 24

/-- Compute the compressed old public rank, then the exact cached shifted
rank used by `NormalizedBounds.afterComparisonBounds`. -/
def afterRank (a : LocalAccess s) (height : ℕ) (head : Fin n) : Result (Vector ℕ n) :=
  let old := LongestPathWork.normalizedRank a.publicRow a.active
  let shifted := LongestPathWork.ranksAfterAdd a.active (fun x => ⟨old.value[x], 1⟩) height head
  ⟨shifted.value, old.work + shifted.work + 2⟩

theorem afterRank_value (a : LocalAccess s) (height : ℕ) (head : Fin n) :
    (afterRank a height head).value =
      Vector.ofFn (SparseRepairGraph.rankAfterAdd s.rows.active (NormalizedBounds.rank s) height head) := by
  have hpublic : RankWork.values a.publicRow = s.pool.system.edge := funext fun x => funext (a.publicRow_value x)
  have hactive : LongestPathWork.rowValues a.active = s.rows.active := funext fun x => funext (a.active_value x)
  have hnormalized := LongestPathWork.normalizedRank_value s a.publicRow a.active hpublic hactive
  simp only [afterRank, LongestPathWork.ranksAfterAdd_value, hactive, hnormalized,
    LongestPathWork.rankValues, Fin.getElem_fin, Vector.getElem_ofFn]
  rfl

def rankBound (n A : ℕ) : ℕ :=
  RankWork.workBound n A + LongestPathWork.tableBound n n A 1 + n * (2 * n + 5) +
    ClosureWork.workBound n A + 7 * n + 2

theorem afterRank_work_le (a : LocalAccess s) {A : ℕ} (hA : AccessBound a A)
    (height : ℕ) (head : Fin n) : (afterRank a height head).work ≤ rankBound n A := by
  have hpublic : RankWork.values a.publicRow = s.pool.system.edge := funext fun x => funext (a.publicRow_value x)
  have hactive : LongestPathWork.rowValues a.active = s.rows.active := funext fun x => funext (a.active_value x)
  have hnormalized := LongestPathWork.normalizedRank_work_le s a.publicRow a.active hpublic hactive
    A A hA.publicRow hA.active
  have hshifted := LongestPathWork.ranksAfterAdd_work_le a.active
    (fun x => ⟨(LongestPathWork.normalizedRank a.publicRow a.active).value[x], 1⟩) height head
    A 1 hA.active (fun _ => le_rfl)
  change _ + _ + 2 ≤ _
  unfold rankBound
  omega

end SortingAdversary.Optimal.ComparedWork
