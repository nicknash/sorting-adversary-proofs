import SortingAdversary.Optimal.MeasuredMachine
import SortingAdversary.Optimal.FiniteLoopWork

/-! The initial member list is generated explicitly and reused by the initial tree. -/

namespace SortingAdversary.Optimal.UniformInitialWork

open PrimitiveWork PoolState RepresentationWork

def members (n : ℕ) : Result (Finset (Fin n)) :=
  let labels := FiniteLoopWork.indices n
  ⟨⟨labels.value, List.nodup_finRange n⟩, labels.work + 1⟩

@[simp] theorem members_value (n : ℕ) : (members n).value = Finset.univ := by
  ext v
  simp [members, FiniteLoopWork.indices]

theorem members_work (n : ℕ) : (members n).work = 3 * n + 2 := by
  simp only [members, FiniteLoopWork.indices]

def pool (N : ℕ) (labels : Finset (Fin (N + 2))) (hl : labels = Finset.univ) : Pool (N + 2) where
  palette := N + 1
  positive := Nat.succ_pos _
  members := labels
  system := rootSystem N
  pins _ := none
  invariant := (initialRoot N).invariant
  pin_bounds := (initialRoot N).pin_bounds
  capacity := by rw [hl]; exact (initialRoot N).capacity
  outside := by rw [hl]; exact (initialRoot N).outside

theorem pool_eq (N : ℕ) (labels : Finset (Fin (N + 2))) (hl : labels = Finset.univ) :
    pool N labels hl = initialRoot N := by subst labels; rfl

def data (N : ℕ) (labels : Finset (Fin (N + 2))) (hl : labels = Finset.univ) :
    LocalData (pool N labels hl) := (pool_eq N labels hl).symm ▸ initialData N

theorem state_eq (N : ℕ) (labels : Finset (Fin (N + 2))) (hl : labels = Finset.univ) :
    PassiveLocalState.state (pool N labels hl) (data N labels hl) =
      PassiveLocalState.state (initialRoot N) (initialData N) := by subst labels; rfl

def tree (N : ℕ) (labels : Finset (Fin (N + 2))) (hl : labels = Finset.univ) : StoredTree (N + 2) :=
  .node 0 (pool N labels hl) (data N labels hl) []

theorem tree_eq (N : ℕ) (labels : Finset (Fin (N + 2))) (hl : labels = Finset.univ) :
    tree N labels hl = StoredTree.initial N := by subst labels; rfl

/-- All finite shapes are explicit. In particular, constructing the zero
and upper getter closures does not evaluate `initialRoot` to recover its
palette and thereby enumerate the member set a second time. -/
def initialAccess (N : ℕ) : LocalAccess
    (PassiveLocalState.state (initialRoot N) (initialData N)) :=
  let top : Fin (N + 1 + 1) := ⟨N + 1, Nat.lt_succ_self _⟩
  {
    publicRow := fun x y => ⟨decide (x = y), 1⟩
    source := fun _ _ => ⟨false, 0⟩
    active := fun _ _ => ⟨false, 0⟩
    lower := fun _ => ⟨(⟨0, Nat.succ_pos _⟩ : Fin (N + 1 + 1)), 0⟩
    upper := fun _ => ⟨top, 0⟩
    pin := fun _ => ⟨(none : Option (Fin (N + 1 + 1))), 0⟩
    member := fun _ => ⟨true, 0⟩
    order := fun x => ⟨x, 0⟩
    inverse := fun x => ⟨x, 0⟩
    publicRow_value := by intros; rfl
    source_value := by intros; rfl
    active_value := by intros; rfl
    lower_value := by intros; rfl
    upper_value := by intros; rfl
    pin_value := by intros; rfl
    member_value := by intro x; simp [PassiveLocalState.state, initialRoot]
    order_value := by intros; rfl
    inverse_value := by intros; rfl }

theorem initialAccess_eq (N : ℕ) : initialAccess N = RepresentationWork.initial N := by rfl

def access (N : ℕ) (labels : Finset (Fin (N + 2))) (hl : labels = Finset.univ) :
    TreeAccess (tree N labels hl) :=
  .node 0 (pool N labels hl) (data N labels hl)
    ((initialAccess N).transport (state_eq N labels hl).symm) .nil

theorem access_bound (N : ℕ) (labels : Finset (Fin (N + 2))) (hl : labels = Finset.univ) :
    (access N labels hl).Bound 2 := by
  subst labels
  exact TreeAccess.initial_bound N

def activeState (p : RecursiveController.Parameters) (N : ℕ)
    (labels : Finset (Fin (N + 2))) (hl : labels = Finset.univ) : ControllerMachine.Active p (N + 2) where
  tree := tree N labels hl
  counter := 1
  wellFormed := by rw [tree_eq]; exact (ControllerMachine.initialActive p N).wellFormed
  coherent := by rw [tree_eq]; exact (ControllerMachine.initialActive p N).coherent
  bounded := by rw [tree_eq]; exact (ControllerMachine.initialActive p N).bounded
  normal := by rw [tree_eq]; exact (ControllerMachine.initialActive p N).normal
  full := hl

theorem activeState_eq (p : RecursiveController.Parameters) (N : ℕ)
    (labels : Finset (Fin (N + 2))) (hl : labels = Finset.univ) :
    activeState p N labels hl = ControllerMachine.initialActive p N := by subst labels; rfl

def active (p : RecursiveController.Parameters) (N : ℕ) : Result (MeasuredController.Active p (N + 2)) :=
  let labels := members (N + 2)
  ⟨⟨activeState p N labels.value (members_value _), access N labels.value (members_value _),
    access_bound N labels.value (members_value _)⟩, labels.work + 30⟩

theorem active_actual (p : RecursiveController.Parameters) (N : ℕ) :
    (active p N).value.state = ControllerMachine.initialActive p N := activeState_eq ..

theorem active_eq (p : RecursiveController.Parameters) (N : ℕ) :
    (active p N).value = MeasuredController.Active.initial p N := by
  simp only [active, members_value]
  rfl

theorem active_work (p : RecursiveController.Parameters) (N : ℕ) :
    (active p N).work = 3 * (N + 2) + 32 := by
  change (members (N + 2)).work + 30 = _
  rw [members_work]

end SortingAdversary.Optimal.UniformInitialWork
