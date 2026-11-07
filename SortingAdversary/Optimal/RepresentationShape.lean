import SortingAdversary.Optimal.RepresentationRealize
import SortingAdversary.Optimal.RepresentationCacheShape

/-!
# Explicit runtime shapes for cached representations

The semantic target of a dependent getter record must remain a proof index:
reading its palette or members can accidentally evaluate a reference update.
These variants receive the already computed palette and persistent member
set explicitly. Their semantic State argument is used only by erased proofs.
-/

namespace SortingAdversary.Optimal.RepresentationWork.LocalAccess

open PrimitiveWork WidthRepair PoolState WeakMaps

variable {n : ℕ} {s : State n}

def systemWith (a : LocalAccess s) (palette : ℕ) (hp : palette = s.pool.palette) :
    WeakSystem (Fin n) (palette + 1) where
  edge x y := (a.publicRow x y).value
  lower x := Fin.cast (congrArg (· + 1) hp.symm) (a.lower x).value
  upper x := Fin.cast (congrArg (· + 1) hp.symm) (a.upper x).value

def pinsWith (a : LocalAccess s) (palette : ℕ) (hp : palette = s.pool.palette) :
    Fin n → Option (Fin (palette + 1)) :=
  fun x => (a.pin x).value.map (Fin.cast (congrArg (· + 1) hp.symm))

@[simp] theorem systemWith_self (a : LocalAccess s) :
    a.systemWith s.pool.palette rfl = a.system := rfl

@[simp] theorem pinsWith_self (a : LocalAccess s) :
    a.pinsWith s.pool.palette rfl = a.pins := by
  funext x
  simp only [pinsWith, pins, Fin.cast_refl, Option.map_id, id_eq]

def poolWith (a : LocalAccess s) (palette : ℕ) (members : Finset (Fin n))
    (hp : palette = s.pool.palette) (hm : members = s.pool.members) : Pool n where
  palette := palette
  positive := by rw [hp]; exact s.pool.positive
  members := members
  system := a.systemWith palette hp
  pins := fun x => (a.pin x).value.map (Fin.cast (congrArg (· + 1) hp.symm))
  invariant := by subst palette; simpa only [systemWith_self, pinsWith_self, system_eq, pins_eq, Fin.cast_refl, Option.map_id, id_eq, a.pin_value] using s.pool.invariant
  pin_bounds := by subst palette; simpa only [systemWith_self, pinsWith_self, system_eq, pins_eq, Fin.cast_refl, Option.map_id, id_eq, a.pin_value] using s.pool.pin_bounds
  capacity := by rw [hp, hm]; exact s.pool.capacity
  outside := by
    subst palette
    simpa only [hm, systemWith_self, pinsWith_self, system_eq, pins_eq, Fin.cast_refl, Option.map_id, id_eq, a.pin_value] using s.pool.outside

@[simp] theorem poolWith_eq (a : LocalAccess s) (palette : ℕ) (members : Finset (Fin n))
    (hp : palette = s.pool.palette) (hm : members = s.pool.members) :
    a.poolWith palette members hp hm = s.pool := by
  subst palette
  subst members
  unfold poolWith
  simp only [systemWith_self, pinsWith_self, system_eq, pins_eq, Fin.cast_refl, Option.map_id, id_eq, a.pin_value]

def permutationWith (a : LocalAccess s) (palette : ℕ) (hp : palette = s.pool.palette) :
    Equiv.Perm (Fin (palette + 1)) where
  toFun x := Fin.cast (congrArg (· + 1) hp.symm)
    (a.order (Fin.cast (congrArg (· + 1) hp) x)).value
  invFun x := Fin.cast (congrArg (· + 1) hp.symm)
    (a.inverse (Fin.cast (congrArg (· + 1) hp) x)).value
  left_inv x := by subst palette; simpa only [Fin.cast_refl, id_eq, permutation] using a.permutation.left_inv x
  right_inv x := by subst palette; simpa only [Fin.cast_refl, id_eq, permutation] using a.permutation.right_inv x

def realizeWith (a : LocalAccess s) (palette : ℕ) (members : Finset (Fin n))
    (hp : palette = s.pool.palette) (hm : members = s.pool.members) : State n where
  pool := a.poolWith palette members hp hm
  rows := {
    source := ClosureWork.values a.source
    active := ClosureWork.values a.active
    proper := by simpa only [source_values] using s.rows.proper
    public_eq := by
      change ClosureWork.values a.publicRow = SparseClosure.closure (ClosureWork.values a.source)
      rw [public_values, source_values]
      exact s.rows.public_eq
    active_source := by simpa only [active_values, source_values] using s.rows.active_source
    active_free := by
      subst palette
      simpa only [active_values, poolWith, pinsWith_self, pins_eq, Fin.cast_refl, Option.map_id, id_eq, a.pin_value] using s.rows.active_free
    covered := by
      subst palette
      subst members
      intro u v huv
      have hold := s.rows.covered u v (by simpa only [ClosureWork.values, a.source_value] using huv)
      rcases hold with ha | hu | hv | hw
      · left; simpa only [ClosureWork.values, a.active_value] using ha
      · right; left; simpa only [poolWith, pinsWith_self, pins_eq, Fin.cast_refl, Option.map_id, id_eq, a.pin_value] using hu
      · right; right; left; simpa only [poolWith, pinsWith_self, pins_eq, Fin.cast_refl, Option.map_id, id_eq, a.pin_value] using hv
      · right; right; right
        change (a.upper u).value.val < (a.lower v).value.val
        rw [a.upper_value, a.lower_value]
        exact hw }
  order := a.permutationWith palette hp

@[simp] theorem realizeWith_eq (a : LocalAccess s) (palette : ℕ) (members : Finset (Fin n))
    (hp : palette = s.pool.palette) (hm : members = s.pool.members) :
    a.realizeWith palette members hp hm = s := by
  subst palette
  subst members
  apply state_ext (poolWith_eq a _ _ rfl rfl) (source_values a) (active_values a)
  apply heq_of_eq
  exact Equiv.ext a.order_value

def rebasedWith (a : LocalAccess s) (palette : ℕ) (members : Finset (Fin n))
    (hp : palette = s.pool.palette) (hm : members = s.pool.members) :
    LocalAccess (a.realizeWith palette members hp hm) :=
  a.transport (a.realizeWith_eq palette members hp hm).symm

theorem rebasedWith_bound (a : LocalAccess s) (palette : ℕ) (members : Finset (Fin n))
    (hp : palette = s.pool.palette) (hm : members = s.pool.members) {A : ℕ}
    (hA : AccessBound a A) : AccessBound (a.rebasedWith palette members hp hm) A :=
  a.transport_bound _ hA

end SortingAdversary.Optimal.RepresentationWork.LocalAccess
