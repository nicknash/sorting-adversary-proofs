import SortingAdversary.Optimal.ReservationFits
import SortingAdversary.Optimal.PoolTreeTraversal

/-!
# Actual completed reservation groups spend the finite-tree entropy

Each group is attached to an actual stored node, consists of its physical
pins, and has a bounded physical-destination multiplicity. Disjointness
allows the conditional-entropy inequality at each actual pool. Summing over
those pools uses the previously proved exact tree entropy telescope.
-/

namespace SortingAdversary.Optimal.TreeReservationEntropy

open scoped BigOperators
open PoolState PoolTree.Tree PoolTreeAccounting PoolTreeGroups PoolTreeTraversal
open LedgerTreeBridge StoredEvolution ReservationFits GroupReservations

variable {n : ℕ}

theorem nodeAt_storedPools {tree : StoredTree n} {identity : ℕ} {state : WidthRepair.State n}
    (h : NodeAt tree identity state) : (identity, state.pool) ∈ storedPools tree.erase := by
  induction h with
  | here identity p d children =>
    simp only [StoredTree.erase, storedPools, ofData, List.mem_cons, true_or]
  | descendant child member occurs ih =>
    rw [StoredTree.erase, storedPools]
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr
    exact ⟨(child.1, child.2.erase), List.mem_map.mpr ⟨child, member, rfl⟩, ih⟩

theorem fits_indexed {tree : StoredTree n} {group : Finset (IncidenceLedger.Location n)} {cap : ℕ}
    (h : Fits tree group cap) :
    ∃ i : Fin (storedPools tree.erase).length, ∃ members : Finset (Fin n),
      group = nodeLocations (identityAt tree.erase i) members ∧
      members ⊆ (poolAt tree.erase i).fixed ∧
      ∀ c, (members.filter (fun v => (poolAt tree.erase i).pins v = some c)).card ≤ cap := by
  obtain ⟨identity, state, members, hn, hg, hf, hc⟩ := h.physical
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (nodeAt_storedPools hn)
  have hid : identityAt tree.erase i = identity := congrArg Prod.fst hi
  have hp : poolAt tree.erase i = state.pool := congrArg Prod.snd hi
  refine ⟨i, members, ?_, ?_, ?_⟩
  · simpa only [hid] using hg
  · simpa only [hp] using hf
  · rw [hp]
    exact hc

def localGroup (p : Pool n) (identity : ℕ) (group : Finset (IncidenceLedger.Location n)) :
    Finset ↥p.fixed := Finset.univ.filter (fun x => (identity, x.val) ∈ group)

@[simp] theorem mem_localGroup (p : Pool n) (identity : ℕ)
    (group : Finset (IncidenceLedger.Location n)) (x : ↥p.fixed) :
    x ∈ localGroup p identity group ↔ (identity, x.val) ∈ group := by
  simp [localGroup]

@[simp] theorem mem_localGroup_nodeLocations (p : Pool n) (identity : ℕ)
    (members : Finset (Fin n)) (x : ↥p.fixed) :
    x ∈ localGroup p identity (nodeLocations identity members) ↔ x.val ∈ members := by
  simp only [mem_localGroup, LedgerTreeBridge.mem_nodeLocations, true_and]

theorem localGroup_card (p : Pool n) (identity : ℕ) (members : Finset (Fin n))
    (hm : members ⊆ p.fixed) :
    (localGroup p identity (nodeLocations identity members)).card = members.card := by
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    exact (mem_localGroup_nodeLocations p identity members x).mp hx
  · intro x _ y _ he
    exact Subtype.ext he
  · intro v hv
    exact ⟨⟨v, hm hv⟩, (mem_localGroup_nodeLocations p identity members _).mpr hv, rfl⟩

theorem localGroup_fiber_card (p : Pool n) (identity : ℕ) (members : Finset (Fin n))
    (hm : members ⊆ p.fixed) (c : Fin (p.palette + 1)) :
    ((localGroup p identity (nodeLocations identity members)).filter
      (fun x => fixedDestination p x = c)).card =
      (members.filter (fun v => p.pins v = some c)).card := by
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    obtain ⟨hx, hc⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(mem_localGroup_nodeLocations p identity members x).mp hx,
      (fixedDestination_eq_iff p x c).mp hc⟩
  · intro x _ y _ he
    exact Subtype.ext he
  · intro v hv
    obtain ⟨hvm, hpin⟩ := Finset.mem_filter.mp hv
    refine ⟨⟨v, hm hvm⟩, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · exact (mem_localGroup_nodeLocations p identity members _).mpr hvm
    · exact (fixedDestination_eq_iff p _ c).mpr hpin

theorem localGroups_disjoint {G : ℕ} (p : Pool n) (identity : ℕ)
    (groups : Fin G → Finset (IncidenceLedger.Location n))
    (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j))) :
    Pairwise (fun i j => Disjoint (localGroup p identity (groups i)) (localGroup p identity (groups j))) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hi hj
  exact Finset.disjoint_left.mp (hdisjoint hij)
    ((mem_localGroup p identity _ x).mp hi) ((mem_localGroup p identity _ x).mp hj)

/-- A selected family may omit the groups belonging to other nodes. -/
theorem selected_disjoint_budget {Event Child : Type*} [Fintype Event] [Fintype Child]
    [DecidableEq Event] [DecidableEq Child] {G : ℕ}
    (groups : Fin G → Finset Event)
    (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (selected : Finset (Fin G)) (destination : Event → Child) (h r : ℕ) (hr : 0 < r)
    (hsize : ∀ g ∈ selected, (groups g).card = h)
    (hcap : ∀ g ∈ selected, ∀ c, ((groups g).filter (fun e => destination e = c)).card ≤ r)
    (reservoir : ℝ) (hreservoir : (Fintype.card Event : ℝ) ≤ reservoir) :
    ((selected.card : ℝ) * h) * Real.log ((h : ℝ) / r) ≤ destinationEntropy destination reservoir := by
  have hb := selected_event_budget (groupOf groups) destination (selected.image some) h r hr
    (fun g hg => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
      rw [groupEvents_groupOf groups hdisjoint]
      exact hsize i hi)
    (fun g hg c => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
      rw [groupEvents_groupOf groups hdisjoint]
      exact hcap i hi c)
    reservoir hreservoir
  simpa only [Finset.card_image_of_injective _ (Option.some_injective _)] using hb

/-- The entropy cost of every actual group is charged at its actual node.
No per-node or global entropy budget is assumed. -/
theorem groups_budget {G H cap : ℕ} (tree : StoredTree n) (hw : tree.erase.WellFormed)
    (groups : Fin G → Finset (IncidenceLedger.Location n))
    (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (hsize : ∀ g, (groups g).card = H) (hcap : 0 < cap)
    (hfits : ∀ g, Fits tree (groups g) cap) :
    ((G : ℝ) * H) * Real.log ((H : ℝ) / cap) ≤ PoolTreeAccounting.entropy tree.erase := by
  classical
  choose index members hg hm hc using fun g => fits_indexed (hfits g)
  let selected (i : Fin (storedPools tree.erase).length) : Finset (Fin G) :=
    Finset.univ.filter (fun g => index g = i)
  have hlocal (i : Fin (storedPools tree.erase).length) :
      (((selected i).card : ℝ) * H) * Real.log ((H : ℝ) / cap) ≤ localEntropy (poolAt tree.erase i) := by
    apply selected_disjoint_budget (fun g => localGroup (poolAt tree.erase i) (identityAt tree.erase i) (groups g))
      (localGroups_disjoint _ _ groups hdisjoint) (selected i) (fixedDestination _) H cap hcap
    · intro g hsel
      have hi : index g = i := (Finset.mem_filter.mp hsel).2
      have hgroup := hg g
      have hmember := hm g
      rw [hi] at hgroup hmember
      rw [hgroup, localGroup_card _ _ _ hmember]
      have hs := hsize g
      rw [hgroup, nodeLocations_card] at hs
      exact hs
    · intro g hsel c
      have hi : index g = i := (Finset.mem_filter.mp hsel).2
      have hgroup := hg g
      have hmember := hm g
      have hbound := hc g
      rw [hi] at hgroup hmember hbound
      rw [hgroup, localGroup_fiber_card _ _ _ hmember]
      exact hbound c
    · exact_mod_cast (by simpa using fixed_card_le_members (poolAt tree.erase i))
  have hcount : (∑ i, (selected i).card) = G := by
    have he := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin G)))
      (t := Finset.univ) (f := index) (fun _ _ => Finset.mem_univ _)
    simpa only [selected, Finset.card_univ, Fintype.card_fin] using he.symm
  calc
    ((G : ℝ) * H) * Real.log ((H : ℝ) / cap) =
        ∑ i, (((selected i).card : ℝ) * H) * Real.log ((H : ℝ) / cap) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, hcount]
    _ ≤ ∑ i, localEntropy (poolAt tree.erase i) := Finset.sum_le_sum (fun i _ => hlocal i)
    _ = PoolTreeAccounting.entropy tree.erase := sum_poolAt_entropy hw

theorem list_groups_budget {H cap : ℕ} (tree : StoredTree n) (hw : tree.erase.WellFormed)
    (groups : List (Finset (IncidenceLedger.Location n)))
    (hdisjoint : groups.Pairwise Disjoint)
    (hsize : ∀ group ∈ groups, group.card = H) (hcap : 0 < cap)
    (hfits : ∀ group ∈ groups, Fits tree group cap) :
    ((groups.length : ℝ) * H) * Real.log ((H : ℝ) / cap) ≤ PoolTreeAccounting.entropy tree.erase := by
  apply groups_budget tree hw (fun i => groups.get i)
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hdisjoint.rel_get_of_lt hlt
    · exact (hdisjoint.rel_get_of_lt hgt).symm
  · intro i
    exact hsize (groups.get i) (List.get_mem _ _)
  · exact hcap
  · intro i
    exact hfits (groups.get i) (List.get_mem _ _)

theorem list_groups_root_budget {H cap : ℕ} (tree : StoredTree n) (hw : tree.erase.WellFormed)
    (hnonempty : tree.pool.members.Nonempty)
    (groups : List (Finset (IncidenceLedger.Location n)))
    (hdisjoint : groups.Pairwise Disjoint)
    (hsize : ∀ group ∈ groups, group.card = H) (hcap : 0 < cap)
    (hfits : ∀ group ∈ groups, Fits tree group cap) :
    ((groups.length : ℝ) * H) * Real.log ((H : ℝ) / cap) ≤
      (tree.pool.members.card : ℝ) * Real.log (tree.pool.members.card : ℝ) := by
  have hn : tree.erase.pool.members.Nonempty := by simpa only [StoredTree.erase_pool] using hnonempty
  simpa only [StoredTree.erase_pool] using
    (list_groups_budget tree hw groups hdisjoint hsize hcap hfits).trans (entropy_le_root hw hn)

end SortingAdversary.Optimal.TreeReservationEntropy
