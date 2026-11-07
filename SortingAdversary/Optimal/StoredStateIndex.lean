import SortingAdversary.Optimal.StoredEvolution
import SortingAdversary.Optimal.PoolTreeTraversal

/-!
# Finite indices for actual stored metadata

This is the preorder traversal of the real stored states. Erasing its metadata
gives the existing pool traversal exactly. Finite indices are only summation
positions; the allocator proves their immutable node identities are distinct.
-/

namespace SortingAdversary.Optimal.StoredStateIndex

open scoped BigOperators
open PoolState WidthRepair StoredEvolution PoolTreeAccounting PoolTreeTraversal TreeChronology

variable {n : ℕ}

def storedStates : StoredTree n → List (ℕ × State n)
  | .node identity p d children =>
      (identity, ofData p d) :: children.flatMap (fun a => storedStates a.2)
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹a ∈ children›
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

theorem storedStates_pools (t : StoredTree n) :
    (storedStates t).map (fun a => (a.1, a.2.pool)) = storedPools t.erase := by
  cases t with
  | node identity p d children =>
    rw [storedStates, StoredTree.erase, storedPools]
    simp only [List.map_cons, List.map_flatMap, List.flatMap_map, Function.comp_def]
    congr 1
    apply List.flatMap_congr
    intro a ha
    exact storedStates_pools a.2
termination_by sizeOf t
decreasing_by
  subst t
  have h := List.sizeOf_lt_of_mem ha
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

theorem storedStates_length (t : StoredTree n) :
    (storedStates t).length = (storedPools t.erase).length := by
  simpa only [List.length_map] using congrArg List.length (storedStates_pools t)

theorem storedStates_nonempty (t : StoredTree n) : 0 < (storedStates t).length := by
  cases t
  rw [storedStates]
  simp

abbrev StateIndex (t : StoredTree n) := Fin (storedStates t).length

instance (t : StoredTree n) : Nonempty (StateIndex t) := ⟨⟨0, storedStates_nonempty t⟩⟩

def stateAt (t : StoredTree n) (i : StateIndex t) : State n := ((storedStates t).get i).2
def identityAt (t : StoredTree n) (i : StateIndex t) : ℕ := ((storedStates t).get i).1

theorem nodeAt_mem {t : StoredTree n} {identity : ℕ} {state : State n}
    (h : NodeAt t identity state) : (identity, state) ∈ storedStates t := by
  induction h with
  | here identity p d children => rw [storedStates]; exact List.mem_cons_self
  | descendant child member occurs ih =>
    rw [storedStates]
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨child, member, ih⟩)

theorem mem_nodeAt (t : StoredTree n) (identity : ℕ) (state : State n)
    (h : (identity, state) ∈ storedStates t) : NodeAt t identity state := by
  cases t with
  | node nodeId p d children =>
    rw [storedStates] at h
    rcases List.mem_cons.mp h with he | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact NodeAt.here _ _ _ _
    · obtain ⟨a, ha, hstate⟩ := List.mem_flatMap.mp h
      exact NodeAt.descendant a ha (mem_nodeAt a.2 identity state hstate)
termination_by sizeOf t
decreasing_by
  subst t
  have h := List.sizeOf_lt_of_mem ha
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

theorem nodeAt_iff_mem {t : StoredTree n} {identity : ℕ} {state : State n} :
    NodeAt t identity state ↔ (identity, state) ∈ storedStates t :=
  ⟨nodeAt_mem, mem_nodeAt t identity state⟩

theorem stateAt_occurs (t : StoredTree n) (i : StateIndex t) :
    NodeAt t (identityAt t i) (stateAt t i) := by
  apply mem_nodeAt
  exact List.get_mem _ _

theorem identities_eq (t : StoredTree n) :
    (storedStates t).map Prod.fst = identities t.erase := by
  rw [identities, ← storedStates_pools]
  simp only [List.map_map, Function.comp_def]

theorem identityAt_injective (t : StoredTree n) {counter : ℕ}
    (allocated : Allocated t.erase counter) : Function.Injective (identityAt t) := by
  have hnodup : ((storedStates t).map Prod.fst).Nodup := by
    rw [identities_eq]
    exact allocated.unique
  intro i j hij
  apply Fin.ext
  have hi : i.val < ((storedStates t).map Prod.fst).length := by simpa using i.isLt
  have hj : j.val < ((storedStates t).map Prod.fst).length := by simpa using j.isLt
  apply (hnodup.getElem_inj_iff (hi := hi) (hj := hj)).mp
  simpa only [identityAt, List.get_eq_getElem, List.getElem_map] using hij

theorem nodeAt_unique {t : StoredTree n} {counter identity : ℕ}
    (allocated : Allocated t.erase counter) {s u : State n}
    (hs : NodeAt t identity s) (hu : NodeAt t identity u) : s = u := by
  have hn : ((storedStates t).map Prod.fst).Nodup := by
    rw [identities_eq]
    exact allocated.unique
  exact congrArg Prod.snd (List.inj_on_of_nodup_map hn (nodeAt_mem hs) (nodeAt_mem hu) rfl)

/-- Proof-only lookup by a certified actual occurrence. -/
noncomputable def locate {t : StoredTree n} {identity : ℕ} {s : State n}
    (occurs : NodeAt t identity s) : StateIndex t :=
  Classical.choose (List.mem_iff_get.mp (nodeAt_mem occurs))

theorem locate_get {t : StoredTree n} {identity : ℕ} {s : State n}
    (occurs : NodeAt t identity s) : (storedStates t).get (locate occurs) = (identity, s) :=
  Classical.choose_spec (List.mem_iff_get.mp (nodeAt_mem occurs))

@[simp] theorem locate_identity {t : StoredTree n} {identity : ℕ} {s : State n}
    (occurs : NodeAt t identity s) : identityAt t (locate occurs) = identity :=
  congrArg Prod.fst (locate_get occurs)

@[simp] theorem locate_state {t : StoredTree n} {identity : ℕ} {s : State n}
    (occurs : NodeAt t identity s) : stateAt t (locate occurs) = s :=
  congrArg Prod.snd (locate_get occurs)

theorem stateAt_pool_mem (t : StoredTree n) (i : StateIndex t) :
    (identityAt t i, (stateAt t i).pool) ∈ storedPools t.erase := by
  rw [← storedStates_pools]
  exact List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩

theorem sum_stateAt {M : Type*} [AddCommMonoid M] (t : StoredTree n) (f : Pool n → M) :
    (∑ i : StateIndex t, f (stateAt t i).pool) =
      ((storedPools t.erase).map (fun a => f a.2)).sum := by
  rw [← storedStates_pools, List.map_map, sum_map_get]
  rfl

theorem sum_members (t : StoredTree n) (h : t.erase.WellFormed) :
    (∑ i : StateIndex t, (stateAt t i).pool.members.card) = t.erase.population := by
  rw [sum_stateAt t (fun p => p.members.card)]
  exact storedPools_population h

theorem sum_fixed (t : StoredTree n) (h : t.erase.WellFormed) :
    (∑ i : StateIndex t, (stateAt t i).pool.fixed.card) = PoolTreeAccounting.promotions t.erase := by
  rw [sum_stateAt t (fun p => p.fixed.card)]
  exact storedPools_promotions h

theorem sum_entropy (t : StoredTree n) (h : t.erase.WellFormed) :
    (∑ i : StateIndex t, PoolTreeGroups.localEntropy (stateAt t i).pool) =
      PoolTreeAccounting.entropy t.erase := by
  rw [sum_stateAt]
  exact storedPools_entropy h

end SortingAdversary.Optimal.StoredStateIndex
