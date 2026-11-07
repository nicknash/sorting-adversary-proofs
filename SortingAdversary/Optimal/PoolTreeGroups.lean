import SortingAdversary.Optimal.PoolTreeAccounting
import SortingAdversary.Optimal.GroupReservations

/-!
# Destination counts are the stored child populations

The destination of an actual fixed member is read from the pool's physical
pin. Its fibre is exactly the corresponding stored child's membership set.
Thus reservation entropy is the same quantity that telescopes on the actual
recursive tree, including unused palette positions with zero fibres.
-/

namespace SortingAdversary.Optimal.PoolTreeGroups

open scoped BigOperators
open PoolState PoolTree PoolTree.Tree PoolTreeAccounting GroupReservations

variable {n identity : ℕ} {p : Pool n} {children : List (ℕ × Tree n)}

/-- Read the stored physical destination; the impossible `none` branch is
eliminated by actual fixed membership. -/
def fixedDestination (p : Pool n) (x : ↥p.fixed) : Fin (p.palette + 1) :=
  match hp : p.pins x.val with
  | none => False.elim ((Finset.mem_filter.mp x.property).2 hp)
  | some c => c

theorem fixedDestination_pin (p : Pool n) (x : ↥p.fixed) :
    p.pins x.val = some (fixedDestination p x) := by
  unfold fixedDestination
  split
  next h => exact False.elim ((Finset.mem_filter.mp x.property).2 h)
  next c h => exact h

theorem fixedDestination_eq_iff (p : Pool n) (x : ↥p.fixed) (c : Fin (p.palette + 1)) :
    fixedDestination p x = c ↔ p.pins x.val = some c := by
  constructor
  · intro h
    simpa only [h] using fixedDestination_pin p x
  · intro h
    exact Option.some.inj ((fixedDestination_pin p x).symm.trans h)

def pinFiber (p : Pool n) (c : Fin (p.palette + 1)) : Finset (Fin n) :=
  p.members.filter (fun x => p.pins x = some c)

theorem fixedDestination_card (p : Pool n) (c : Fin (p.palette + 1)) :
    (destinationEvents (fixedDestination p) c).card = (pinFiber p c).card := by
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_filter.mp x.property).1, ?_⟩
    exact (fixedDestination_eq_iff p x c).mp (Finset.mem_filter.mp hx).2
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro x hx
    obtain ⟨hxm, hpin⟩ := Finset.mem_filter.mp hx
    have hfixed : x ∈ p.fixed := Finset.mem_filter.mpr ⟨hxm, by simp [hpin]⟩
    refine ⟨⟨x, hfixed⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (fixedDestination_eq_iff p _ c).mpr hpin⟩

theorem pinIndex_eq_some_iff (p : Pool n) (x : Fin n) (c : Fin (p.palette + 1)) :
    pinIndex p x = some c.val ↔ p.pins x = some c := by
  constructor
  · intro h
    exact Option.map_injective Fin.val_injective h
  · intro h
    simp [pinIndex, h]

def childColor (h : (PoolTree.Tree.node identity p children).WellFormed)
    (i : Fin children.length) : Fin (p.palette + 1) :=
  ⟨(children.get i).1, by
    cases h with
    | node _ _ _ _ hb _ _ _ _ _ => exact hb _ (List.get_mem _ _)⟩

theorem childColor_injective (h : (PoolTree.Tree.node identity p children).WellFormed) :
    Function.Injective (childColor h) := by
  intro i j hij
  exact child_key_injective h (congrArg Fin.val hij)

theorem pinFiber_childColor (h : (PoolTree.Tree.node identity p children).WellFormed)
    (i : Fin children.length) : pinFiber p (childColor h i) = childMembers children i := by
  cases h with
  | node _ _ _ _ _ _ _ _ hm _ =>
    ext x
    simp only [pinFiber, Finset.mem_filter, childMembers]
    rw [hm _ (List.get_mem _ _) x]
    constructor
    · rintro ⟨hxm, hpin⟩
      exact ⟨hxm, (pinIndex_eq_some_iff p x _).mpr hpin⟩
    · rintro ⟨hxm, hpin⟩
      exact ⟨hxm, (pinIndex_eq_some_iff p x _).mp hpin⟩

theorem pinFiber_empty_of_unoccupied (h : (PoolTree.Tree.node identity p children).WellFormed)
    (c : Fin (p.palette + 1)) (hc : c ∉ Set.range (childColor h)) : pinFiber p c = ∅ := by
  cases h with
  | node _ _ _ _ _ _ _ _ _ hcover =>
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hxm, hpin⟩ := Finset.mem_filter.mp hx
    obtain ⟨t, ht⟩ := hcover x hxm c.val ((pinIndex_eq_some_iff p x c).mpr hpin)
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ht
    apply hc
    refine ⟨i, ?_⟩
    apply Fin.ext
    exact congrArg Prod.fst hi

noncomputable def localEntropy (p : Pool n) : ℝ :=
  destinationEntropy (fixedDestination p) p.members.card

/-- Every destination term is counted exactly once at its actual child. -/
theorem localEntropy_eq_children (h : (PoolTree.Tree.node identity p children).WellFormed) :
    localEntropy p = (children.map (fun a =>
      (a.2.pool.members.card : ℝ) * Real.log ((p.members.card : ℝ) / a.2.pool.members.card))).sum := by
  unfold localEntropy destinationEntropy
  simp only [fixedDestination_card]
  rw [sum_map_get]
  apply (Fintype.sum_of_injective (childColor h) (childColor_injective h)
    (fun i => ((childMembers children i).card : ℝ) *
      Real.log ((p.members.card : ℝ) / (childMembers children i).card))
    (fun c => ((pinFiber p c).card : ℝ) * Real.log ((p.members.card : ℝ) / (pinFiber p c).card))
    ?_ ?_).symm
  · intro c hc
    simp [pinFiber_empty_of_unoccupied h c hc]
  · intro i
    rw [pinFiber_childColor h i]

/-- This identifies reservation entropy with the actual summand in the
global finite-tree telescope. -/
theorem entropy_eq_local_add_children (h : (PoolTree.Tree.node identity p children).WellFormed) :
    PoolTreeAccounting.entropy (PoolTree.Tree.node identity p children) =
      localEntropy p + (children.map (fun a => PoolTreeAccounting.entropy a.2)).sum := by
  rw [PoolTreeAccounting.entropy, localEntropy_eq_children h]
  simp only [sum_map_get, Finset.sum_add_distrib]

theorem fixed_card_le_members (p : Pool n) : p.fixed.card ≤ p.members.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- Actual path groups at one stored pool spend the same entropy as its
real children, including fixed members not selected by any path group. -/
theorem path_groups_le_local {G H : ℕ} (p : Pool n)
    (groups : Fin G → Finset ↥p.fixed)
    (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j))) (hH : 1 < H)
    (hsize : ∀ g, (groups g).card = H)
    (hinjective : ∀ g, Set.InjOn (fixedDestination p) (groups g)) :
    ((reservedEvents groups).card : ℝ) ≤ localEntropy p / Real.log H := by
  apply path_group_count_le groups hdisjoint (fixedDestination p) H hH hsize hinjective
  exact_mod_cast (by simpa using fixed_card_le_members p)

/-- The actual hub-record cap supplies the corresponding scale budget at a
stored pool; every destination is read from its real physical pin. -/
theorem scale_groups_le_local {G J : ℕ} (p : Pool n)
    (groups : Fin G → Finset ↥p.fixed)
    (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j))) (hJ : 2 < J)
    (hsize : ∀ g, (groups g).card = J)
    (births : Fin G → ℕ) (record : ↥p.fixed → HubSelector.Block)
    (rank : Fin G → ℕ → ℕ) (hinj : ∀ g, Function.Injective (rank g))
    (hvalid : ∀ g e, e ∈ groups g → record e ∈ HubSelector.allBlocks (births g))
    (hrecord : ∀ g, Set.InjOn record (groups g))
    (hdestination : ∀ g e, e ∈ groups g →
      (fixedDestination p e).val = HubSelector.hubColour (rank g) (hinj g) (record e)) :
    ((reservedEvents groups).card : ℝ) ≤ localEntropy p / Real.log ((J : ℝ) / 2) := by
  apply scale_group_count_le groups hdisjoint (fixedDestination p) J hJ hsize births record rank hinj
    hvalid hrecord hdestination
  exact_mod_cast (by simpa using fixed_card_le_members p)

end SortingAdversary.Optimal.PoolTreeGroups
