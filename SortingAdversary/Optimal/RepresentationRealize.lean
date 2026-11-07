import SortingAdversary.Optimal.RepresentationPromoteWork

/-!
# Reconstructing runtime states from measured getters

`realize` places the measured getters in the actual State fields. A cache
therefore changes the executable representation, rather than merely attaching
a cost bound to an unrelated state. Equality with the reference state is
proved extensionally, while every invariant certificate is erased at runtime.
-/

namespace SortingAdversary.Optimal.RepresentationWork

open PrimitiveWork WidthRepair WeakMaps PoolState

variable {n : ℕ} {s : State n}

theorem state_ext {s t : State n} (hp : s.pool = t.pool)
    (hs : s.rows.source = t.rows.source) (ha : s.rows.active = t.rows.active)
    (ho : HEq s.order t.order) : s = t := by
  cases s
  cases t
  dsimp only at hp hs ha ho
  cases hp
  have hr := sourcePartition_ext hs ha
  cases hr
  cases eq_of_heq ho
  rfl

namespace LocalAccess

def system (a : LocalAccess s) : WeakSystem (Fin n) (s.pool.palette + 1) where
  edge x y := (a.publicRow x y).value
  lower x := (a.lower x).value
  upper x := (a.upper x).value

@[simp] theorem system_eq (a : LocalAccess s) : a.system = s.pool.system :=
  windows_system a

def pins (a : LocalAccess s) : Fin n → Option (Fin (s.pool.palette + 1)) := fun x => (a.pin x).value

@[simp] theorem pins_eq (a : LocalAccess s) : a.pins = s.pool.pins := funext a.pin_value

def pool (a : LocalAccess s) : Pool n where
  palette := s.pool.palette
  positive := s.pool.positive
  members := s.pool.members
  system := a.system
  pins := a.pins
  invariant := by simpa only [system_eq, pins_eq] using s.pool.invariant
  pin_bounds := by simpa only [system_eq, pins_eq] using s.pool.pin_bounds
  capacity := s.pool.capacity
  outside := by simpa only [system_eq, pins_eq] using s.pool.outside

@[simp] theorem pool_eq (a : LocalAccess s) : a.pool = s.pool := by
  unfold pool
  simp only [system_eq, pins_eq]

def permutation (a : LocalAccess s) : Equiv.Perm (Fin (s.pool.palette + 1)) where
  toFun x := (a.order x).value
  invFun x := (a.inverse x).value
  left_inv x := by simp only [a.order_value, a.inverse_value, Equiv.symm_apply_apply]
  right_inv x := by simp only [a.order_value, a.inverse_value, Equiv.apply_symm_apply]

@[simp] theorem permutation_eq (a : LocalAccess s) : a.permutation = s.order :=
  Equiv.ext a.order_value

/-- All executable functional fields come from measured getters. The
existing finite member set is persistent data and is shared by reference. -/
def realize (a : LocalAccess s) : State n where
  pool := a.pool
  rows := {
    source := ClosureWork.values a.source
    active := ClosureWork.values a.active
    proper := by simpa only [source_values] using s.rows.proper
    public_eq := by simpa only [pool, source_values, system_eq] using s.rows.public_eq
    active_source := by simpa only [active_values, source_values] using s.rows.active_source
    active_free := by simpa only [active_values, pool, pins_eq] using s.rows.active_free
    covered := by
      intro u v huv
      have hold := s.rows.covered u v (by simpa only [ClosureWork.values, a.source_value] using huv)
      rcases hold with ha | hu | hv | hw
      · left
        simpa only [ClosureWork.values, a.active_value] using ha
      · right; left
        simpa only [pool, pins, a.pin_value] using hu
      · right; right; left
        simpa only [pool, pins, a.pin_value] using hv
      · right; right; right
        change (a.upper u).value.val < (a.lower v).value.val
        rw [a.upper_value, a.lower_value]
        exact hw }
  order := a.permutation

@[simp] theorem realize_eq (a : LocalAccess s) : a.realize = s := by
  apply state_ext (pool_eq a) (source_values a) (active_values a)
  exact heq_of_eq (permutation_eq a)

def rebased (a : LocalAccess s) : LocalAccess a.realize := a.transport a.realize_eq.symm

theorem rebased_bound (a : LocalAccess s) {A : ℕ} (h : AccessBound a A) :
    AccessBound a.rebased A := a.transport_bound _ h

end LocalAccess

end SortingAdversary.Optimal.RepresentationWork
