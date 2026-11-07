import SortingAdversary.Optimal.RepresentationWork

/-! Explicit palette input keeps the semantic target state erased during caching. -/

namespace SortingAdversary.Optimal.RepresentationWork.LocalAccess

open PrimitiveWork WidthRepair PoolState WeakMaps

variable {n : ℕ} {s : State n}

def cacheWith (a : LocalAccess s) (palette : ℕ) (hp : palette = s.pool.palette) :
    Result (LocalAccess s) :=
  let publicRows := ClosureWork.tabulate a.publicRow
  let sources := ClosureWork.tabulate a.source
  let activeRows := ClosureWork.tabulate a.active
  let lowers := PrimitiveWork.vector a.lower
  let uppers := PrimitiveWork.vector a.upper
  let pins := PrimitiveWork.vector a.pin
  let members := PrimitiveWork.vector a.member
  let orders := PrimitiveWork.vector (fun x : Fin (palette + 1) =>
    a.order (Fin.cast (congrArg (· + 1) hp) x))
  let inverses := PrimitiveWork.vector (fun x : Fin (palette + 1) =>
    a.inverse (Fin.cast (congrArg (· + 1) hp) x))
  ⟨{
    publicRow := fun x y => ⟨publicRows.value[x][y], 2⟩
    source := fun x y => ⟨sources.value[x][y], 2⟩
    active := fun x y => ⟨activeRows.value[x][y], 2⟩
    lower := fun x => ⟨lowers.value[x], 1⟩
    upper := fun x => ⟨uppers.value[x], 1⟩
    pin := fun x => ⟨pins.value[x], 1⟩
    member := fun x => ⟨members.value[x], 1⟩
    order := fun x => ⟨orders.value[Fin.cast (congrArg (· + 1) hp.symm) x], 1⟩
    inverse := fun x => ⟨inverses.value[Fin.cast (congrArg (· + 1) hp.symm) x], 1⟩
    publicRow_value := by intro x y; simp [publicRows, ClosureWork.tabulate_value, SparseClosure.tabulate]
    source_value := by intro x y; simp [sources, ClosureWork.tabulate_value, SparseClosure.tabulate]
    active_value := by intro x y; simp [activeRows, ClosureWork.tabulate_value, SparseClosure.tabulate]
    lower_value := by intro x; simp [lowers, a.lower_value]
    upper_value := by intro x; simp [uppers, a.upper_value]
    pin_value := by intro x; simp [pins, a.pin_value]
    member_value := by intro x; simp [members, a.member_value]
    order_value := by intro x; simp [orders, a.order_value]
    inverse_value := by intro x; simp [inverses, a.inverse_value] },
    publicRows.work + sources.work + activeRows.work + lowers.work + uppers.work +
      pins.work + members.work + orders.work + inverses.work + 9⟩

theorem cacheWith_eq (a : LocalAccess s) (palette : ℕ) (hp : palette = s.pool.palette) :
    a.cacheWith palette hp = a.cache := by
  subst palette
  rfl

theorem cacheWith_access (a : LocalAccess s) (palette : ℕ) (hp : palette = s.pool.palette) :
    AccessBound (a.cacheWith palette hp).value 2 := by
  rw [cacheWith_eq]
  exact cache_access a

theorem cacheWith_work_le (a : LocalAccess s) (palette : ℕ) (hp : palette = s.pool.palette)
    {A : ℕ} (hA : AccessBound a A) :
    (a.cacheWith palette hp).work ≤ cacheBound n palette A := by
  rw [cacheWith_eq, hp]
  exact cache_work_le a hA

end SortingAdversary.Optimal.RepresentationWork.LocalAccess
