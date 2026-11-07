import SortingAdversary.Optimal.RepresentationPromoteWork
import SortingAdversary.Optimal.PassiveLocalState
import SortingAdversary.Optimal.FiniteLoopWork

/-!
# Measured child admission and eager caching

The population test counts actual measured membership getters. The two
branches implement precisely `Pool.admission` and `LocalData.admission`:
an available slot admits the new isolated label; a full palette first adds
one top position and then performs the same admission. Retained functional
fields keep their lookup charges, and the final eager cache resets them.
-/

namespace SortingAdversary.Optimal.RepresentationWork

open PrimitiveWork WidthRepair PoolState FreshAdmission RefinementTransitions

variable {n K : ℕ}

def admissionState (p : Pool n) (d : LocalData p) (v : Fin n) (hv : v ∉ p.members) : State n :=
  PassiveLocalState.state (p.admission v hv).next (d.admission p v hv)

def sizedData (p : Pool n) (d : LocalData p) (v : Fin n) (hv : v ∉ p.members)
    (hcap : p.members.card + 1 ≤ p.palette + 1) : LocalData (p.admitSized v hv hcap) :=
  ⟨d.rows.admit v (p.system.lower v) (p.outside v hv).2, d.order⟩

def sizedState (p : Pool n) (d : LocalData p) (v : Fin n) (hv : v ∉ p.members)
    (hcap : p.members.card + 1 ≤ p.palette + 1) : State n :=
  PassiveLocalState.state (p.admitSized v hv hcap) (sizedData p d v hv hcap)

def appendData (p : Pool n) (d : LocalData p) : LocalData p.append :=
  ⟨d.rows.append, PaletteBirthOrder.extendTop d.order⟩

def appendState (p : Pool n) (d : LocalData p) : State n :=
  PassiveLocalState.state p.append (appendData p d)

theorem append_active (p : Pool n) (d : LocalData p) : d.rows.append.active = d.rows.active := by
  funext x y
  change (d.rows.active x y && decide (mapPins Fin.castSucc p.pins x = none ∧
    mapPins Fin.castSucc p.pins y = none)) = d.rows.active x y
  by_cases he : d.rows.active x y = true
  · obtain ⟨hx, hy⟩ := d.rows.active_free x y he
    simp [he, mapPins, hx, hy]
  · simp [Bool.eq_false_iff.mpr he]

def admitLower (get : Fin n → Result (Fin (K + 1))) (v x : Fin n) : Result (Fin (K + 1)) :=
  let old := get x
  ⟨if x = v then 0 else old.value, old.work + 2⟩

def admitUpper (get : Fin n → Result (Fin (K + 1))) (v x : Fin n) : Result (Fin (K + 1)) :=
  let old := get x
  ⟨if x = v then Fin.last K else old.value, old.work + 2⟩

def admitPin (get : Fin n → Result (Option (Fin K))) (v x : Fin n) : Result (Option (Fin K)) :=
  let old := get x
  ⟨if x = v then none else old.value, old.work + 2⟩

def admitMember (get : Fin n → Result Bool) (v x : Fin n) : Result Bool :=
  let old := get x
  ⟨old.value || decide (x = v), old.work + 2⟩

def sizedAccess (p : Pool n) (d : LocalData p) (a : LocalAccess (PassiveLocalState.state p d))
    (v : Fin n) (hv : v ∉ p.members) (hcap : p.members.card + 1 ≤ p.palette + 1) :
    LocalAccess (sizedState p d v hv hcap) where
  publicRow := a.publicRow
  source := a.source
  active := a.active
  lower := admitLower a.lower v
  upper := admitUpper a.upper v
  pin := admitPin a.pin v
  member := admitMember a.member v
  order := a.order
  inverse := a.inverse
  publicRow_value := a.publicRow_value
  source_value := a.source_value
  active_value := a.active_value
  lower_value := by intro x; simp [admitLower, a.lower_value, sizedState, sizedData,
    PassiveLocalState.state, Pool.admitSized, FreshAdmission.admit]; rfl
  upper_value := by intro x; simp [admitUpper, a.upper_value, sizedState, sizedData,
    PassiveLocalState.state, Pool.admitSized, FreshAdmission.admit]
  pin_value := by intro x; simp [admitPin, a.pin_value, sizedState, sizedData,
    PassiveLocalState.state, Pool.admitSized, unpin, Function.update_apply]
  member_value := by
    intro x
    change ((a.member x).value || decide (x = v)) = decide (x ∈ insert v p.members)
    have hm : (a.member x).value = decide (x ∈ p.members) := a.member_value x
    rw [hm]
    simp [Finset.mem_insert, Bool.or_comm]
  order_value := a.order_value
  inverse_value := a.inverse_value

def appendAccess (p : Pool n) (d : LocalData p) (a : LocalAccess (PassiveLocalState.state p d)) :
    LocalAccess (appendState p d) where
  publicRow := a.publicRow
  source := a.source
  active := a.active
  lower x := let old := a.lower x; ⟨old.value.castSucc, old.work + 1⟩
  upper x := let old := a.upper x; ⟨old.value.castSucc, old.work + 1⟩
  pin x := let old := a.pin x; ⟨old.value.map Fin.castSucc, old.work + 2⟩
  member := a.member
  order := extendForward a.order (Fin.last (p.palette + 1))
  inverse := extendInverse a.inverse (Fin.last (p.palette + 1))
  publicRow_value := a.publicRow_value
  source_value := a.source_value
  active_value := by intro x y; rw [a.active_value]; exact congrFun (congrFun (append_active p d).symm x) y
  lower_value := by intro x; exact congrArg Fin.castSucc (a.lower_value x)
  upper_value := by intro x; exact congrArg Fin.castSucc (a.upper_value x)
  pin_value := by intro x; exact congrArg (Option.map Fin.castSucc) (a.pin_value x)
  member_value := a.member_value
  order_value := by
    intro x
    exact extendForward_value d.order a.order a.order_value (Fin.last (p.palette + 1)) x
  inverse_value := by
    intro x
    exact extendInverse_value d.order a.inverse a.inverse_value (Fin.last (p.palette + 1)) x

theorem sizedAccess_bound (p : Pool n) (d : LocalData p) (a : LocalAccess (PassiveLocalState.state p d))
    {A : ℕ} (cost : AccessBound a A) (v : Fin n) (hv : v ∉ p.members)
    (hcap : p.members.card + 1 ≤ p.palette + 1) : AccessBound (sizedAccess p d a v hv hcap) (A + 3) := by
  constructor
  · intro x y; exact (cost.publicRow x y).trans (Nat.le_add_right A 3)
  · intro x y; exact (cost.source x y).trans (Nat.le_add_right A 3)
  · intro x y; exact (cost.active x y).trans (Nat.le_add_right A 3)
  · intro x; exact (Nat.add_le_add_right (cost.lower x) 2).trans (by omega)
  · intro x; exact (Nat.add_le_add_right (cost.upper x) 2).trans (by omega)
  · intro x; exact (Nat.add_le_add_right (cost.pin x) 2).trans (by omega)
  · intro x; exact (Nat.add_le_add_right (cost.member x) 2).trans (by omega)
  · intro x; exact (cost.order x).trans (Nat.le_add_right A 3)
  · intro x; exact (cost.inverse x).trans (Nat.le_add_right A 3)

theorem appendAccess_bound (p : Pool n) (d : LocalData p) (a : LocalAccess (PassiveLocalState.state p d))
    {A : ℕ} (cost : AccessBound a A) : AccessBound (appendAccess p d a) (A + 12) := by
  constructor
  · intro x y; exact (cost.publicRow x y).trans (Nat.le_add_right A 12)
  · intro x y; exact (cost.source x y).trans (Nat.le_add_right A 12)
  · intro x y; exact (cost.active x y).trans (Nat.le_add_right A 12)
  · intro x; exact (Nat.add_le_add_right (cost.lower x) 1).trans (by omega)
  · intro x; exact (Nat.add_le_add_right (cost.upper x) 1).trans (by omega)
  · intro x; exact (Nat.add_le_add_right (cost.pin x) 2).trans (by omega)
  · intro x; exact (cost.member x).trans (Nat.le_add_right A 12)
  · intro x; exact extendForward_work_le a.order _ x A cost.order
  · intro x; exact extendInverse_work_le a.inverse _ x A cost.inverse

theorem stateData_mpr {p q : Pool n} (hp : p = q) (d : LocalData p) (he : LocalData q = LocalData p) :
    PassiveLocalState.state q (he.mpr d) = PassiveLocalState.state p d := by
  cases hp
  rfl

theorem sizedState_actual (p : Pool n) (d : LocalData p) (v : Fin n) (hv : v ∉ p.members)
    (hcap : p.members.card + 1 ≤ p.palette + 1) : sizedState p d v hv hcap = admissionState p d v hv := by
  unfold admissionState LocalData.admission
  have hd : ((p.members.card + 1).decLe (p.palette + 1)) = .isTrue hcap := Subsingleton.elim _ _
  simp only [hd]
  have hp : p.admitSized v hv hcap = (p.admission v hv).next := by
    simp only [Pool.admission, dif_pos hcap]
  change sizedState p d v hv hcap = PassiveLocalState.state _
    ((congrArg LocalData hp.symm).mpr (sizedData p d v hv hcap))
  rw [stateData_mpr hp]
  rfl

theorem appendSized_actual (p : Pool n) (d : LocalData p) (v : Fin n) (hv : v ∉ p.members)
    (hcap : ¬ p.members.card + 1 ≤ p.palette + 1) :
    sizedState p.append (appendData p d) v (by simpa using hv) (Nat.succ_le_succ p.capacity) =
      admissionState p d v hv := by
  unfold admissionState LocalData.admission
  have hd : ((p.members.card + 1).decLe (p.palette + 1)) = .isFalse hcap := Subsingleton.elim _ _
  simp only [hd]
  have hp : p.append.admitSized v (by simpa using hv) (Nat.succ_le_succ p.capacity) =
      (p.admission v hv).next := by simp only [Pool.admission, dif_neg hcap]
  change _ = PassiveLocalState.state _ ((congrArg LocalData hp.symm).mpr
    (sizedData p.append (appendData p d) v (by simpa using hv) (Nat.succ_le_succ p.capacity)))
  rw [stateData_mpr hp]
  rfl

private theorem weaken_access {s : State n} (a : LocalAccess s) {A B : ℕ}
    (h : AccessBound a A) (hle : A ≤ B) : AccessBound a B := by
  constructor
  · intro x y; exact (h.publicRow x y).trans hle
  · intro x y; exact (h.source x y).trans hle
  · intro x y; exact (h.active x y).trans hle
  · intro x; exact (h.lower x).trans hle
  · intro x; exact (h.upper x).trans hle
  · intro x; exact (h.pin x).trans hle
  · intro x; exact (h.member x).trans hle
  · intro x; exact (h.order x).trans hle
  · intro x; exact (h.inverse x).trans hle

namespace LocalAccess

def population {s : State n} (a : LocalAccess s) : Result ℕ :=
  let domain := FiniteLoopWork.indices n
  let size := PrimitiveWork.count a.member domain.value
  ⟨size.value, domain.work + size.work⟩

@[simp] theorem population_value {s : State n} (a : LocalAccess s) :
    a.population.value = s.pool.members.card := by
  simp only [population, FiniteLoopWork.indices, PrimitiveWork.count_value]
  have hn := (List.nodup_finRange n).filter (fun x => (a.member x).value)
  rw [← List.toFinset_card_of_nodup hn]
  congr 1
  ext x
  simp [a.member_value]

theorem population_work {s : State n} (a : LocalAccess s) {A : ℕ} (cost : AccessBound a A) :
    a.population.work ≤ n * (A + 6) + 2 := by
  have hh := PrimitiveWork.count_work_le a.member (List.finRange n) A (fun x _ => cost.member x)
  simp only [List.length_finRange] at hh
  change (3 * n + 1) + (PrimitiveWork.count a.member (List.finRange n)).work ≤ _
  simp only [Nat.mul_add] at hh ⊢
  omega

def admit (p : Pool n) (d : LocalData p) (a : LocalAccess (PassiveLocalState.state p d))
    (v : Fin n) (hv : v ∉ p.members) : Result (LocalAccess (admissionState p d v hv)) :=
  let size := a.population
  if hcap : size.value + 1 ≤ p.palette + 1 then
    have actual : p.members.card + 1 ≤ p.palette + 1 := by
      have hs : size.value = p.members.card := population_value a
      rwa [hs] at hcap
    ⟨(sizedAccess p d a v hv actual).transport (sizedState_actual p d v hv actual), size.work + 40⟩
  else
    have actual : ¬ p.members.card + 1 ≤ p.palette + 1 := by
      have hs : size.value = p.members.card := population_value a
      rwa [hs] at hcap
    let enlarged := appendAccess p d a
    let next := sizedAccess p.append (appendData p d) enlarged v (by simpa using hv)
      (Nat.succ_le_succ p.capacity)
    ⟨next.transport (appendSized_actual p d v hv actual), size.work + 40⟩

theorem admit_access (p : Pool n) (d : LocalData p) (a : LocalAccess (PassiveLocalState.state p d))
    {A : ℕ} (cost : AccessBound a A) (v : Fin n) (hv : v ∉ p.members) :
    AccessBound (a.admit p d v hv).value (A + 15) := by
  unfold admit
  dsimp only
  split
  · apply transport_bound
    exact weaken_access _ (sizedAccess_bound p d a cost v hv _) (by omega)
  · apply transport_bound
    exact sizedAccess_bound p.append (appendData p d) (appendAccess p d a)
      (appendAccess_bound p d a cost) v (by simpa using hv) (Nat.succ_le_succ p.capacity)

theorem admit_work (p : Pool n) (d : LocalData p) (a : LocalAccess (PassiveLocalState.state p d))
    {A : ℕ} (cost : AccessBound a A) (v : Fin n) (hv : v ∉ p.members) :
    (a.admit p d v hv).work ≤ n * (A + 6) + 42 := by
  have hh := population_work a cost
  unfold admit
  dsimp only
  split <;> dsimp only <;> omega

def admitCached (p : Pool n) (d : LocalData p) (a : LocalAccess (PassiveLocalState.state p d))
    (v : Fin n) (hv : v ∉ p.members) : Result (LocalAccess (admissionState p d v hv)) :=
  let updated := a.admit p d v hv
  let cached := updated.value.cache
  ⟨cached.value, updated.work + cached.work⟩

theorem admitCached_access (p : Pool n) (d : LocalData p) (a : LocalAccess (PassiveLocalState.state p d))
    (v : Fin n) (hv : v ∉ p.members) : AccessBound (a.admitCached p d v hv).value 2 :=
  cache_access _

theorem admitCached_work (p : Pool n) (d : LocalData p) (a : LocalAccess (PassiveLocalState.state p d))
    {A : ℕ} (cost : AccessBound a A) (v : Fin n) (hv : v ∉ p.members) :
    (a.admitCached p d v hv).work ≤ n * (A + 6) + 42 +
      cacheBound n (p.admission v hv).next.palette (A + 15) :=
  Nat.add_le_add (admit_work p d a cost v hv) (cache_work_le _ (admit_access p d a cost v hv))

end LocalAccess

/-- The newly allocated child has literal constant getters. -/
def emptyAccess (n : ℕ) : LocalAccess (PassiveLocalState.state (emptyPool n) (emptyData n)) where
  publicRow x y := ⟨decide (x = y), 1⟩
  source _ _ := ⟨false, 0⟩
  active _ _ := ⟨false, 0⟩
  lower _ := ⟨0, 0⟩
  upper _ := ⟨0, 0⟩
  pin _ := ⟨some 0, 0⟩
  member _ := ⟨false, 0⟩
  order x := ⟨x, 0⟩
  inverse x := ⟨x, 0⟩
  publicRow_value _ _ := rfl
  source_value _ _ := rfl
  active_value _ _ := rfl
  lower_value _ := rfl
  upper_value _ := rfl
  pin_value _ := rfl
  member_value _ := by simp [PassiveLocalState.state, emptyPool]
  order_value _ := rfl
  inverse_value _ := rfl

theorem emptyAccess_bound (n : ℕ) : AccessBound (emptyAccess n) 1 := by
  constructor <;> intros <;> norm_num only [emptyAccess]

end SortingAdversary.Optimal.RepresentationWork
