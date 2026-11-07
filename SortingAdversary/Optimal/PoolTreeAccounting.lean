import SortingAdversary.Optimal.PoolTree
import SortingAdversary.Optimal.Accounting
import Mathlib.Data.List.OfFn

/-!
# Accounting on the actual recursive pool tree

The stored child-membership invariant gives a disjoint partition of the
parent's fixed labels. Every original member consequently has exactly one
free stopping occurrence. The separated comparison mate forces every child
to be strictly smaller than its parent and every unary node to retain a
free label. These facts prove the node and entropy bounds on the concrete
tree, without a supplied abstract tree budget.
-/

namespace SortingAdversary.Optimal.PoolTreeAccounting

open scoped BigOperators
open PoolState PoolTree PoolTree.Tree

theorem sum_map_get {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → M) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  simpa only [List.get_eq_getElem, List.ofFn_getElem_eq_map] using
    (List.sum_ofFn (f := fun i : Fin l.length => f (l.get i)))

theorem short_list_members_eq {α : Type*} (l : List α) (hshort : l.length < 2)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hb
  have hij : i = j := by
    apply Fin.ext
    have hilt := i.isLt
    have hjlt := j.isLt
    omega
  exact hi.symm.trans (hij ▸ hj)

variable {n identity : ℕ} {p : Pool n} {children : List (ℕ × Tree n)}

def childMembers (children : List (ℕ × Tree n)) (i : Fin children.length) : Finset (Fin n) :=
  (children.get i).2.pool.members

theorem child_key_injective (h : (PoolTree.Tree.node identity p children).WellFormed) :
    Function.Injective (fun i : Fin children.length => (children.get i).1) := by
  cases h with
  | node _ _ _ hkeys _ _ _ _ _ _ =>
    intro i j hij
    apply Fin.ext
    have hleft : i.val < (children.map Prod.fst).length := by simp
    have hright : j.val < (children.map Prod.fst).length := by simp
    apply (hkeys.getElem_inj_iff (hi := hleft) (hj := hright)).mp
    simpa only [List.getElem_map, List.get_eq_getElem] using hij

theorem child_members_disjoint (h : (PoolTree.Tree.node identity p children).WellFormed) :
    Pairwise (fun i j => Disjoint (childMembers children i) (childMembers children j)) := by
  have hinj := child_key_injective h
  cases h with
  | node _ _ _ _ _ _ _ _ hm _ =>
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have hi := (hm _ (List.get_mem _ _) x).mp hxi
    have hj := (hm _ (List.get_mem _ _) x).mp hxj
    exact hij (hinj (Option.some.inj (hi.2.symm.trans hj.2)))

theorem child_members_union (h : (PoolTree.Tree.node identity p children).WellFormed) :
    Finset.univ.biUnion (childMembers children) = p.fixed := by
  cases h with
  | node _ _ _ _ _ _ _ _ hm hc =>
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨hxm, hpin⟩ := (hm _ (List.get_mem _ _) x).mp hxi
      apply Finset.mem_filter.mpr
      refine ⟨hxm, ?_⟩
      intro hnone
      simp [pinIndex, hnone] at hpin
    · intro hx
      obtain ⟨hxm, hfixed⟩ := Finset.mem_filter.mp hx
      cases hpx : p.pins x with
      | none => exact False.elim (hfixed hpx)
      | some c =>
        have hi : pinIndex p x = some c.val := by simp [pinIndex, hpx]
        obtain ⟨child, hchild⟩ := hc x hxm c.val hi
        obtain ⟨i, hi'⟩ := List.mem_iff_get.mp hchild
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_univ _, ?_⟩
        apply (hm _ (List.get_mem _ _) x).mpr
        exact ⟨hxm, by simpa only [hi'] using hi⟩

theorem free_add_fixed (p : Pool n) : p.free.card + p.fixed.card = p.members.card := by
  exact Finset.card_filter_add_card_filter_not (fun x => p.pins x = none)

/-- Exact local conservation, using the real stored child memberships. -/
theorem local_population (h : (PoolTree.Tree.node identity p children).WellFormed) :
    p.free.card + (children.map (fun a => a.2.pool.members.card)).sum = p.members.card := by
  have hsum := Finset.card_biUnion
    (fun i (_ : i ∈ Finset.univ) j (_ : j ∈ Finset.univ) hij => child_members_disjoint h hij)
  rw [child_members_union h] at hsum
  rw [sum_map_get]
  change p.free.card + (∑ i, (childMembers children i).card) = p.members.card
  rw [← hsum]
  exact free_add_fixed p

theorem child_indicator (h : (PoolTree.Tree.node identity p children).WellFormed) (x : Fin n) :
    (children.map (fun a => if x ∈ a.2.pool.members then 1 else 0)).sum =
      if x ∈ p.fixed then 1 else 0 := by
  rw [sum_map_get]
  change (∑ i : Fin children.length, if x ∈ childMembers children i then 1 else 0) = _
  by_cases hfixed : x ∈ p.fixed
  · have hu : x ∈ Finset.univ.biUnion (childMembers children) := by
      rw [child_members_union h]
      exact hfixed
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hu
    rw [if_pos hfixed]
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      have hxj : x ∉ childMembers children j :=
        fun hxj => Finset.disjoint_left.mp (child_members_disjoint h hji) hxj hi
      simp [hxj]
    · simp
  · have hnone (i : Fin children.length) : x ∉ childMembers children i := by
      intro hi
      apply hfixed
      rw [← child_members_union h]
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩
    simp [hnone, hfixed]

/-- A label stops free exactly once if it entered this subtree, and never
occurs free in it otherwise. -/
theorem freeOccurrences_eq {t : Tree n} (h : t.WellFormed) (x : Fin n) :
    t.freeOccurrences x = if x ∈ t.pool.members then 1 else 0 := by
  induction h with
  | node identity p children hkeys hb ho hs hchild hm hc ih =>
    have hnode := WellFormed.node identity p children hkeys hb ho hs hchild hm hc
    rw [freeOccurrences]
    rw [List.map_congr_left (fun a ha => ih a ha), child_indicator hnode x]
    change (if x ∈ p.free then 1 else 0) + (if x ∈ p.fixed then 1 else 0) =
      if x ∈ p.members then 1 else 0
    by_cases hx : x ∈ p.members
    · cases hp : p.pins x <;> simp [Pool.free, Pool.fixed, hx, hp]
    · simp [Pool.free, Pool.fixed, hx]

/-- Every occupied child is strictly smaller than its parent. The witness
outside that child is the parent's retained separated comparison mate. -/
theorem child_size_lt (h : (PoolTree.Tree.node identity p children).WellFormed)
    (a : ℕ × Tree n) (ha : a ∈ children) : a.2.pool.members.card < p.members.card := by
  cases h with
  | node _ _ _ _ _ ho hs _ hm _ =>
    have hsub : a.2.pool.members ⊆ p.members := fun x hx => ((hm a ha x).mp hx).1
    obtain ⟨x, hx⟩ := ho a ha
    obtain ⟨hxm, hxpin⟩ := (hm a ha x).mp hx
    cases hpx : p.pins x with
    | none => simp [pinIndex, hpx] at hxpin
    | some c =>
      obtain ⟨y, hym, _hycomp, hypin⟩ := hs x hxm c hpx
      have hynot : y ∉ a.2.pool.members := by
        intro hy
        have hyindex := ((hm a ha y).mp hy).2
        have heq : p.pins y = p.pins x :=
          Option.map_injective Fin.val_injective (hyindex.trans hxpin.symm)
        exact hypin (heq.trans hpx)
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hsub, ?_⟩
      intro heq
      exact hynot (heq ▸ hym)

theorem unary_free_nonempty (h : (PoolTree.Tree.node identity p children).WellFormed)
    (hnonempty : p.members.Nonempty) (hsmall : children.length < 2) : p.free.Nonempty := by
  cases h with
  | node _ _ _ _ _ _ hs _ _ hc =>
    obtain ⟨x, hxm⟩ := hnonempty
    cases hpx : p.pins x with
    | none => exact ⟨x, (p.free_iff x).mpr hpx⟩
    | some c =>
      obtain ⟨y, hym, _hycomp, hypin⟩ := hs x hxm c hpx
      cases hpy : p.pins y with
      | none => exact ⟨y, (p.free_iff y).mpr hpy⟩
      | some d =>
        have hcindex : pinIndex p x = some c.val := by simp [pinIndex, hpx]
        have hdindex : pinIndex p y = some d.val := by simp [pinIndex, hpy]
        obtain ⟨tc, htc⟩ := hc x hxm c.val hcindex
        obtain ⟨td, htd⟩ := hc y hym d.val hdindex
        have heq := short_list_members_eq children hsmall htc htd
        have hcd : c = d := Fin.ext (congrArg Prod.fst heq)
        exact False.elim (hypin (hpy.trans (congrArg some hcd.symm)))

/-- The actual stored finite tree has at most `2s-1` nodes when `s` labels
entered its nonempty root. Empty dummy pools are not counted as children. -/
theorem nodes_add_one_le_twice_members {t : Tree n} (h : t.WellFormed)
    (hnonempty : t.pool.members.Nonempty) : t.nodes + 1 ≤ 2 * t.pool.members.card := by
  induction h with
  | node identity p children hkeys hb ho hs hchild hm hc ih =>
    have hnode := WellFormed.node identity p children hkeys hb ho hs hchild hm hc
    have hlocal : 2 ≤ children.length + 2 * p.free.card := by
      by_cases hsmall : children.length < 2
      · have hfree := Finset.card_pos.mpr (unary_free_nonempty hnode hnonempty hsmall)
        change 0 < p.free.card at hfree
        omega
      · omega
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      ih (children.get i) (List.get_mem _ _) (ho _ (List.get_mem _ _)))
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one, ← Finset.mul_sum] at hsum
    have hpopulation := local_population hnode
    rw [sum_map_get] at hpopulation
    simp only [nodes, pool]
    rw [sum_map_get]
    omega

theorem local_fixed_population (h : (PoolTree.Tree.node identity p children).WellFormed) :
    (children.map (fun a => a.2.pool.members.card)).sum = p.fixed.card := by
  have hpop := local_population h
  have hpartition := free_add_fixed p
  omega

def stoppingPopulation : Tree n → ℕ
  | .node _ p children => p.free.card + (children.map (fun a => stoppingPopulation a.2)).sum
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹a ∈ children›
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

/-- The actual fixed-member counts sum to the number of parent-to-child
promotions represented by the current tree. -/
def promotions : Tree n → ℕ
  | .node _ p children => p.fixed.card + (children.map (fun a => promotions a.2)).sum
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹a ∈ children›
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

def allChildAdmissions : Tree n → ℕ
  | .node _ _ children =>
      (children.map (fun a => a.2.pool.members.card + allChildAdmissions a.2)).sum
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹a ∈ children›
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

theorem stoppingPopulation_eq_members {t : Tree n} (h : t.WellFormed) :
    stoppingPopulation t = t.pool.members.card := by
  induction h with
  | node identity p children hkeys hb ho hs hchild hm hc ih =>
    rw [stoppingPopulation, List.map_congr_left (fun a ha => ih a ha)]
    exact local_population (.node identity p children hkeys hb ho hs hchild hm hc)

theorem population_eq_members_add_childAdmissions {t : Tree n} (h : t.WellFormed) :
    t.population = t.pool.members.card + allChildAdmissions t := by
  induction h with
  | node _ _ _ _ _ _ _ _ _ _ ih =>
    rw [population, allChildAdmissions, List.map_congr_left (fun a ha => ih a ha)]
    rfl

theorem childAdmissions_eq_promotions {t : Tree n} (h : t.WellFormed) :
    allChildAdmissions t = promotions t := by
  induction h with
  | node identity p children hkeys hb ho hs hchild hm hc ih =>
    have hnode := WellFormed.node identity p children hkeys hb ho hs hchild hm hc
    rw [allChildAdmissions, promotions]
    have hmap := List.map_congr_left (fun a ha =>
      congrArg (fun z => a.2.pool.members.card + z) (ih a ha))
    rw [hmap, sum_map_get, Finset.sum_add_distrib]
    rw [← sum_map_get children (fun a => a.2.pool.members.card),
      ← sum_map_get children (fun a => promotions a.2), local_fixed_population hnode]

/-- Concrete finite-tree population identity, including every admission to
every descendant, even when one original label passes through several pools.
-/
theorem population_eq_members_add_promotions {t : Tree n} (h : t.WellFormed) :
    t.population = t.pool.members.card + promotions t := by
  rw [population_eq_members_add_childAdmissions h, childAdmissions_eq_promotions h]

theorem population_eq_stopping_add_promotions {t : Tree n} (h : t.WellFormed) :
    t.population = stoppingPopulation t + promotions t := by
  rw [stoppingPopulation_eq_members h, population_eq_members_add_promotions h]

/-- The actual separation entropy of every parent-to-child admission. -/
noncomputable def entropy : Tree n → ℝ
  | .node _ p children => (children.map (fun a =>
      (a.2.pool.members.card : ℝ) * Real.log ((p.members.card : ℝ) / a.2.pool.members.card) +
        entropy a.2)).sum
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹a ∈ children›
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

/-- The nonnegative remainder left by labels which stop at a pool. -/
noncomputable def stoppingLog : Tree n → ℝ
  | .node _ p children => (p.free.card : ℝ) * Real.log (p.members.card : ℝ) +
      (children.map (fun a => stoppingLog a.2)).sum
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹a ∈ children›
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

theorem stoppingLog_nonneg {t : Tree n} (h : t.WellFormed)
    (hnonempty : t.pool.members.Nonempty) : 0 ≤ stoppingLog t := by
  induction h with
  | node _ p children _ _ ho _ _ _ _ ih =>
    have hone : (1 : ℝ) ≤ p.members.card := by
      exact_mod_cast Finset.one_le_card.mpr hnonempty
    rw [stoppingLog]
    apply add_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hone)
    · apply List.sum_nonneg
      intro a ha
      obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp ha
      exact ih child hchild (ho child hchild)

/-- Exact telescoping of the actual tree entropy. The identity includes the
stopping remainder and uses no abstract parent map or population hypothesis.
-/
theorem entropy_add_stoppingLog {t : Tree n} (h : t.WellFormed)
    (hnonempty : t.pool.members.Nonempty) :
    entropy t + stoppingLog t = (t.pool.members.card : ℝ) * Real.log (t.pool.members.card : ℝ) := by
  induction h with
  | node identity p children hkeys hb ho hs hchild hm hc ih =>
    have hnode := WellFormed.node identity p children hkeys hb ho hs hchild hm hc
    have hpos : (0 : ℝ) < p.members.card := by exact_mod_cast Finset.card_pos.mpr hnonempty
    have hlocal (i : Fin children.length) :
        ((children.get i).2.pool.members.card : ℝ) *
          Real.log ((p.members.card : ℝ) / (children.get i).2.pool.members.card) +
          entropy (children.get i).2 + stoppingLog (children.get i).2 =
        ((children.get i).2.pool.members.card : ℝ) * Real.log (p.members.card : ℝ) := by
      have hchildpos : (0 : ℝ) < (children.get i).2.pool.members.card := by
        exact_mod_cast Finset.card_pos.mpr (ho _ (List.get_mem _ _))
      have hi := ih (children.get i) (List.get_mem _ _) (ho _ (List.get_mem _ _))
      rw [Real.log_div hpos.ne' hchildpos.ne']
      nlinarith
    have hsum := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hlocal i)
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
    have hpop := local_population hnode
    rw [sum_map_get] at hpop
    have hpopreal : (p.free.card : ℝ) +
        (∑ i : Fin children.length, ((children.get i).2.pool.members.card : ℝ)) = p.members.card := by
      exact_mod_cast hpop
    have hmul := congrArg (fun z : ℝ => z * Real.log (p.members.card : ℝ)) hpopreal
    rw [entropy, stoppingLog, sum_map_get, sum_map_get]
    change _ = (p.members.card : ℝ) * Real.log (p.members.card : ℝ)
    simp only [Finset.sum_add_distrib]
    nlinarith

/-- The manuscript's global entropy budget now holds for the stored tree. -/
theorem entropy_le_root {t : Tree n} (h : t.WellFormed)
    (hnonempty : t.pool.members.Nonempty) :
    entropy t ≤ (t.pool.members.card : ℝ) * Real.log (t.pool.members.card : ℝ) := by
  have heq := entropy_add_stoppingLog h hnonempty
  have hnonneg := stoppingLog_nonneg h hnonempty
  linarith

theorem entropy_nonneg {t : Tree n} (h : t.WellFormed) : 0 ≤ entropy t := by
  induction h with
  | node identity p children hkeys hb ho hs hchild hm hc ih =>
    have hnode := WellFormed.node identity p children hkeys hb ho hs hchild hm hc
    rw [entropy]
    apply List.sum_nonneg
    intro value hvalue
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hvalue
    apply add_nonneg _ (ih a ha)
    have hpos : (0 : ℝ) < a.2.pool.members.card := by exact_mod_cast Finset.card_pos.mpr (ho a ha)
    have hle : (a.2.pool.members.card : ℝ) ≤ p.members.card := by
      exact_mod_cast (child_size_lt hnode a ha).le
    exact mul_nonneg hpos.le (Real.log_nonneg ((one_le_div hpos).mpr hle))

end SortingAdversary.Optimal.PoolTreeAccounting
