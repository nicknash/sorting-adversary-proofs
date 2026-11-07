import SortingAdversary.Optimal.TreeChronology

/-!
# The chronological ledger counts the actual tree promotions

The two data equalities in `Represents` identify the ledger's entered/free
locations with the corresponding actual stored node/label pairs. Unique
immutable node identities make these finite sets disjoint between nodes.
Completeness of the promotion records is proved from the executable ledger
runner. Its count therefore agrees exactly with the actual tree's fixed
population, and the endpoint bound applies to that tree population.
-/

namespace SortingAdversary.Optimal.LedgerTreeBridge

open scoped BigOperators
open PoolState PoolTree PoolTree.Tree PoolTreeAccounting PoolTreeTraversal TreeChronology

variable {n : ℕ}

def movedLocations (s : IncidenceLedger.State n) : Finset (IncidenceLedger.Location n) :=
  s.moves.image IncidenceLedger.Move.location

def Complete (s : IncidenceLedger.State n) : Prop := movedLocations s = s.entered \ s.free

theorem initial_complete (free : Finset (IncidenceLedger.Location n)) :
    Complete (IncidenceLedger.initial free) := by
  simp [Complete, movedLocations, IncidenceLedger.initial]

theorem step_complete {threshold : ℕ} {s t : IncidenceLedger.State n}
    (hs : IncidenceLedger.Valid threshold s) (hcomplete : Complete s)
    (a : IncidenceLedger.Action n) (ht : IncidenceLedger.step threshold s a = some t) :
    Complete t := by
  cases a with
  | admit x =>
    simp only [IncidenceLedger.step] at ht
    split at ht
    next hx =>
      cases ht
      change movedLocations s = insert x s.entered \ insert x s.free
      rw [hcomplete]
      ext y
      by_cases hy : y = x
      · subst y
        simp [hx]
      · simp [hy]
    next => contradiction
  | physical row =>
    simp only [IncidenceLedger.step] at ht
    split at ht
    · cases ht
      exact hcomplete
    · contradiction
  | promote x kind =>
    simp only [IncidenceLedger.step] at ht
    split at ht
    next hx =>
      cases ht
      have hentered := hs.free_entered hx.1
      unfold Complete movedLocations
      simp only [Finset.image_insert]
      change insert x (movedLocations s) = s.entered \ s.free.erase x
      rw [hcomplete]
      ext y
      by_cases hy : y = x
      · subst y
        simp [hentered]
      · simp [hy]
    next => contradiction

theorem run_complete {threshold : ℕ} (actions : List (IncidenceLedger.Action n))
    {s t : IncidenceLedger.State n} (hs : IncidenceLedger.Valid threshold s)
    (hcomplete : Complete s) (ht : IncidenceLedger.run threshold s actions = some t) : Complete t := by
  induction actions generalizing s with
  | nil =>
    simp only [IncidenceLedger.run, Option.some.injEq] at ht
    exact ht ▸ hcomplete
  | cons a rest ih =>
    simp only [IncidenceLedger.run] at ht
    cases hstep : IncidenceLedger.step threshold s a with
    | none => simp [hstep] at ht
    | some u =>
      simp only [hstep, Option.bind_some] at ht
      exact ih (IncidenceLedger.step_valid hs a hstep) (step_complete hs hcomplete a hstep) ht

theorem movedLocations_card {threshold : ℕ} {s : IncidenceLedger.State n}
    (hs : IncidenceLedger.Valid threshold s) : (movedLocations s).card = s.moves.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  exact hs.unique a ha b hb hab

theorem moves_card_eq_entered_sub_free {threshold : ℕ} {s : IncidenceLedger.State n}
    (hs : IncidenceLedger.Valid threshold s) (hcomplete : Complete s) :
    s.moves.card = s.entered.card - s.free.card := by
  rw [← movedLocations_card hs, hcomplete, Finset.card_sdiff_of_subset hs.free_entered]

def nodeLocations (identity : ℕ) (labels : Finset (Fin n)) : Finset (IncidenceLedger.Location n) :=
  labels.image (fun x => (identity, x))

theorem nodeLocations_card (identity : ℕ) (labels : Finset (Fin n)) :
    (nodeLocations identity labels).card = labels.card := by
  apply Finset.card_image_of_injective
  intro x y h
  exact congrArg Prod.snd h

def treeLocations (t : Tree n) (select : Pool n → Finset (Fin n)) :
    Finset (IncidenceLedger.Location n) :=
  Finset.univ.biUnion (fun i : Fin (storedPools t).length =>
    nodeLocations (identityAt t i) (select (poolAt t i)))

theorem identityAt_injective {t : Tree n} {nextIdentity : ℕ} (h : Allocated t nextIdentity) :
    Function.Injective (identityAt t) := by
  intro i j hij
  apply Fin.ext
  have hleft : i.val < (identities t).length := by simp [identities]
  have hright : j.val < (identities t).length := by simp [identities]
  apply (h.unique.getElem_inj_iff (hi := hleft) (hj := hright)).mp
  simpa only [identities, List.getElem_map, identityAt, List.get_eq_getElem] using hij

theorem treeLocations_card {t : Tree n} {nextIdentity : ℕ} (h : Allocated t nextIdentity)
    (select : Pool n → Finset (Fin n)) :
    (treeLocations t select).card = ∑ i, (select (poolAt t i)).card := by
  have hdisjoint : Pairwise (fun i j : Fin (storedPools t).length =>
      Disjoint (nodeLocations (identityAt t i) (select (poolAt t i)))
        (nodeLocations (identityAt t j) (select (poolAt t j)))) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro location hi hj
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hi
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hj
    have heq : identityAt t i = identityAt t j :=
      congrArg (fun location : IncidenceLedger.Location n => location.1) (hx.trans hy.symm)
    exact hij (identityAt_injective h heq)
  rw [treeLocations, Finset.card_biUnion (fun i _ j _ hij => hdisjoint hij)]
  simp only [nodeLocations_card]

def enteredLocations (t : Tree n) : Finset (IncidenceLedger.Location n) := treeLocations t Pool.members
def freeLocations (t : Tree n) : Finset (IncidenceLedger.Location n) := treeLocations t Pool.free
def fixedLocations (t : Tree n) : Finset (IncidenceLedger.Location n) := treeLocations t Pool.fixed

theorem enteredLocations_card {t : Tree n} {nextIdentity : ℕ} (h : t.WellFormed)
    (ha : Allocated t nextIdentity) : (enteredLocations t).card = t.population := by
  rw [enteredLocations, treeLocations_card ha, sum_poolAt_members h]

theorem freeLocations_card {t : Tree n} {nextIdentity : ℕ} (h : t.WellFormed)
    (ha : Allocated t nextIdentity) : (freeLocations t).card = t.pool.members.card := by
  rw [freeLocations, treeLocations_card ha, sum_poolAt_free h]

theorem fixedLocations_card {t : Tree n} {nextIdentity : ℕ} (h : t.WellFormed)
    (ha : Allocated t nextIdentity) : (fixedLocations t).card = promotions t := by
  rw [fixedLocations, treeLocations_card ha]
  simpa only [sum_map_get, poolAt] using storedPools_promotions h

/-- Exact data correspondence; neither a charge budget nor a count equality
is a field of this relation. -/
structure Represents (s : IncidenceLedger.State n) (t : Tree n) : Prop where
  entered : s.entered = enteredLocations t
  free : s.free = freeLocations t

theorem mem_nodeLocations (identity : ℕ) (labels : Finset (Fin n))
    (location : IncidenceLedger.Location n) :
    location ∈ nodeLocations identity labels ↔ location.1 = identity ∧ location.2 ∈ labels := by
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
    exact ⟨rfl, hx⟩
  · rintro ⟨hid, hx⟩
    exact Finset.mem_image.mpr ⟨location.2, hx, Prod.ext hid.symm rfl⟩

theorem mem_treeLocations (t : Tree n) (select : Pool n → Finset (Fin n))
    (location : IncidenceLedger.Location n) :
    location ∈ treeLocations t select ↔
      ∃ a ∈ storedPools t, location.1 = a.1 ∧ location.2 ∈ select a.2 := by
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h
    exact ⟨(storedPools t).get i, List.get_mem _ _, (mem_nodeLocations _ _ _).mp hi⟩
  · rintro ⟨a, ha, hid, hx⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, (mem_nodeLocations _ _ _).mpr ?_⟩
    simpa only [identityAt, poolAt, hi] using And.intro hid hx

def initialFree (n : ℕ) : Finset (IncidenceLedger.Location n) := nodeLocations 0 Finset.univ

theorem initial_represents (N : ℕ) :
    Represents (IncidenceLedger.initial (initialFree (N + 2))) (PoolTree.Tree.initial N) := by
  constructor <;> ext location <;>
    simp only [IncidenceLedger.initial, enteredLocations, freeLocations, mem_treeLocations,
      PoolTree.Tree.initial, storedPools, List.flatMap_nil, List.mem_singleton, exists_eq_left,
      initialFree, mem_nodeLocations, initialRoot, Pool.free, Finset.mem_univ,
      Finset.mem_filter, and_true]

/-- The promotion count is derived from chronological completeness and the
actual node/label representation, not postulated in the correspondence. -/
theorem represented_moves_eq_promotions {threshold : ℕ} {s : IncidenceLedger.State n}
    {t : Tree n} {nextIdentity : ℕ} (hs : IncidenceLedger.Valid threshold s)
    (hcomplete : Complete s) (ht : t.WellFormed) (ha : Allocated t nextIdentity)
    (hrep : Represents s t) : s.moves.card = promotions t := by
  rw [moves_card_eq_entered_sub_free hs hcomplete, hrep.entered, hrep.free,
    enteredLocations_card ht ha, freeLocations_card ht ha, population_eq_members_add_promotions ht]
  omega

/-- The endpoint injection now bounds the actual represented recursive tree,
with physical calls counted from the input event sequence. -/
theorem actual_tree_incidence_bound (threshold : ℕ) (free : Finset (IncidenceLedger.Location n))
    (actions : List (IncidenceLedger.Action n)) (s : IncidenceLedger.State n)
    (hrun : IncidenceLedger.run threshold (IncidenceLedger.initial free) actions = some s)
    (t : Tree n) (ht : t.WellFormed) (nextIdentity : ℕ) (ha : Allocated t nextIdentity)
    (hrep : Represents s t) :
    promotions t ≤ 2 * (actions.map IncidenceLedger.Action.physicalCost).sum := by
  have hs := IncidenceLedger.run_valid actions (IncidenceLedger.initial_valid threshold free) hrun
  have hc := run_complete actions (IncidenceLedger.initial_valid threshold free) (initial_complete free) hrun
  have hmatch := represented_moves_eq_promotions hs hc ht ha hrep
  have hcounts := IncidenceLedger.run_counts actions (IncidenceLedger.initial_valid threshold free) hrun
  have hbound := IncidenceLedger.promotions_le_twice_calls hs
  rw [hmatch, hcounts.1] at hbound
  simpa only [IncidenceLedger.initial, List.length_nil, zero_add] using hbound

theorem actual_tree_promotion_count (threshold : ℕ) (free : Finset (IncidenceLedger.Location n))
    (actions : List (IncidenceLedger.Action n)) (s : IncidenceLedger.State n)
    (hrun : IncidenceLedger.run threshold (IncidenceLedger.initial free) actions = some s)
    (t : Tree n) (ht : t.WellFormed) (nextIdentity : ℕ) (ha : Allocated t nextIdentity)
    (hrep : Represents s t) :
    (actions.map IncidenceLedger.Action.promotionCost).sum = promotions t := by
  have hs := IncidenceLedger.run_valid actions (IncidenceLedger.initial_valid threshold free) hrun
  have hc := run_complete actions (IncidenceLedger.initial_valid threshold free) (initial_complete free) hrun
  have hmatch := represented_moves_eq_promotions hs hc ht ha hrep
  have hcounts := IncidenceLedger.run_counts actions (IncidenceLedger.initial_valid threshold free) hrun
  simpa only [IncidenceLedger.initial, Finset.card_empty, zero_add] using hcounts.2.1.symm.trans hmatch

end SortingAdversary.Optimal.LedgerTreeBridge
