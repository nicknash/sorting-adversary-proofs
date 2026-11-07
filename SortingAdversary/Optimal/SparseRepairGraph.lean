import SortingAdversary.Optimal.GraphBalls
import SortingAdversary.Optimal.SparseClosure
import Mathlib.Data.List.Chain
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Executable sparse-graph repair routines

Original label identities are retained. A supplied topological rank determines
when each entry of a materialized vector is filled. Each entry stores one
longest predecessor chain, selected by a deterministic scan of the labels.
The algorithm does not enumerate directed paths.
-/

namespace SortingAdversary.Optimal.SparseRepairGraph

open GraphBalls SparseClosure
open scoped BigOperators

variable {α : Type*} {n : ℕ}

/-- Deterministic maximum-length choice, taking the first longest candidate. -/
def longest : List (List α) → List α
  | [] => []
  | p :: ps => let q := longest ps; if q.length ≤ p.length then p else q

theorem longest_selected (ps : List (List α)) : longest ps = [] ∨ longest ps ∈ ps := by
  induction ps with
  | nil => exact Or.inl rfl
  | cons p ps ih =>
    simp only [longest]
    split_ifs with h
    · exact Or.inr List.mem_cons_self
    · exact ih.elim Or.inl (fun h => Or.inr (List.mem_cons_of_mem _ h))

theorem length_le_longest {ps : List (List α)} {p : List α} (hp : p ∈ ps) :
    p.length ≤ (longest ps).length := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [longest]
    rcases List.mem_cons.mp hp with rfl | hp
    · split_ifs with h <;> omega
    · have hh := ih hp
      split_ifs with h <;> omega

theorem longest_property (P : List α → Prop) (hnil : P [])
    (ps : List (List α)) (hps : ∀ p ∈ ps, P p) : P (longest ps) :=
  (longest_selected ps).elim (fun h => h ▸ hnil) (hps _)

/-- Chains are stored backwards, starting at their final vertex. -/
def EndsPath (E : α → α → Bool) (v : α) (p : List α) : Prop :=
  p.head? = some v ∧ p.IsChain (fun x y => Arc E y x)

theorem singleton_path (E : α → α → Bool) (v : α) : EndsPath E v [v] :=
  ⟨rfl, .singleton _⟩

theorem extend_path {E : α → α → Bool} {u v : α} {p : List α}
    (hp : EndsPath E u p) (huv : Arc E u v) : EndsPath E v (v :: p) := by
  refine ⟨rfl, hp.2.cons ?_⟩
  intro x hx
  have hx' : u = x := by simpa only [hp.1, Option.mem_some_iff] using hx
  simpa only [hx'] using huv

theorem path_mono {E F : α → α → Bool} (hEF : ∀ u v, E u v = true → F u v = true)
    {v : α} {p : List α} (hp : EndsPath E v p) : EndsPath F v p :=
  ⟨hp.1, hp.2.imp (fun _ _ h => ⟨h.1, hEF _ _ h.2⟩)⟩

abbrev PathTable (n : ℕ) := Vector (List (Fin n)) n

/-- One scan of the raw incoming rows, using already stored predecessor paths. -/
def candidates (E : Fin n → Fin n → Bool) (T : PathTable n) (v : Fin n) :
    List (List (Fin n)) :=
  ((List.finRange n).filter (fun u => decide (u ≠ v) && E u v)).map (fun u => T[u])

theorem mem_candidates (E : Fin n → Fin n → Bool) (T : PathTable n) (v : Fin n)
    (p : List (Fin n)) : p ∈ candidates E T v ↔ ∃ u, Arc E u v ∧ T[u] = p := by
  simp only [candidates, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    Bool.and_eq_true, decide_eq_true_eq, Arc]

/-- A complete materialized layer; old entries are copied, not recomputed. -/
def pathStep (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (k : ℕ)
    (T : PathTable n) : PathTable n :=
  Vector.ofFn (fun v => if rank v = k then v :: longest (candidates E T v) else T[v])

@[simp] theorem pathStep_get (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (k : ℕ)
    (T : PathTable n) (v : Fin n) :
    (pathStep E rank k T)[v] = if rank v = k then v :: longest (candidates E T v) else T[v] := by
  simp [pathStep]

/-- Process the first `k` topological ranks. -/
def pathTable (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) : ℕ → PathTable n
  | 0 => Vector.replicate n []
  | k + 1 => pathStep E rank k (pathTable E rank k)

@[simp] theorem pathTable_zero (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (v : Fin n) :
    (pathTable E rank 0)[v] = [] := by simp [pathTable]

theorem pathTable_unprocessed (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ)
    {k : ℕ} {v : Fin n} (h : k ≤ rank v) : (pathTable E rank k)[v] = [] := by
  induction k with
  | zero => exact pathTable_zero E rank v
  | succ k ih =>
    rw [pathTable, pathStep_get, if_neg (by omega)]
    exact ih (by omega)

/-- Once a vertex's rank is processed, its stored chain is a genuine maximum
among all directed paths ending there. -/
theorem pathTable_correct (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ)
    (hstrict : ∀ u v, Arc E u v → rank u < rank v) {k : ℕ} {v : Fin n}
    (hv : rank v < k) :
    EndsPath E v ((pathTable E rank k)[v]) ∧
      ∀ p, EndsPath E v p → p.length ≤ ((pathTable E rank k)[v]).length := by
  induction k generalizing v with
  | zero => omega
  | succ k ih =>
    by_cases hvk : rank v = k
    · rw [pathTable, pathStep_get, if_pos hvk]
      have hcand : ∀ p ∈ candidates E (pathTable E rank k) v,
          ∃ u, Arc E u v ∧ EndsPath E u p := by
        intro p hp
        obtain ⟨u, huv, rfl⟩ := (mem_candidates _ _ _ _).mp hp
        exact ⟨u, huv, (ih (by have := hstrict u v huv; omega)).1⟩
      constructor
      · rcases longest_selected (candidates E (pathTable E rank k) v) with hz | hm
        · rw [hz]
          exact singleton_path E v
        · obtain ⟨u, huv, hp⟩ := hcand _ hm
          exact extend_path hp huv
      · intro p hp
        cases p with
        | nil => simp
        | cons a tail =>
          have hav : a = v := Option.some.inj hp.1
          subst a
          cases tail with
          | nil => simp
          | cons u rest =>
            have hchain := List.isChain_cons_cons.mp hp.2
            have hr := hstrict u v hchain.1
            have hu : rank u < k := by omega
            have hmax := (ih hu).2 (u :: rest) ⟨rfl, hchain.2⟩
            have hmem : ((pathTable E rank k)[u]) ∈ candidates E (pathTable E rank k) v :=
              (mem_candidates _ _ _ _).mpr ⟨u, hchain.1, rfl⟩
            have hlen := length_le_longest hmem
            simpa only [List.length_cons] using Nat.add_le_add_right (hmax.trans hlen) 1
    · rw [pathTable, pathStep_get, if_neg hvk]
      exact ih (by omega)

/-- A deterministic longest chain in the entire graph after all ranks below
the supplied bound have been processed. -/
def longestChain (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (bound : ℕ) : List (Fin n) :=
  let T := pathTable E rank bound
  longest ((List.finRange n).map (fun v => T[v]))

theorem longestChain_chain (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (bound : ℕ)
    (hstrict : ∀ u v, Arc E u v → rank u < rank v) (hbound : ∀ v, rank v < bound) :
    (longestChain E rank bound).IsChain (fun x y => Arc E y x) := by
  apply longest_property _ .nil
  intro p hp
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hp
  exact (pathTable_correct E rank hstrict (hbound v)).1.2

theorem longestChain_maximal (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (bound : ℕ)
    (hstrict : ∀ u v, Arc E u v → rank u < rank v) (hbound : ∀ v, rank v < bound)
    {p : List (Fin n)} (hp : p.IsChain (fun x y => Arc E y x)) :
    p.length ≤ (longestChain E rank bound).length := by
  cases p with
  | nil => exact Nat.zero_le _
  | cons v tail =>
    have hm := (pathTable_correct E rank hstrict (hbound v)).2 (v :: tail) ⟨rfl, hp⟩
    exact hm.trans (length_le_longest (List.mem_map.mpr ⟨v, by simp, rfl⟩))

theorem chain_rank_pairwise (E : α → α → Bool) (rank : α → ℕ)
    (hstrict : ∀ u v, Arc E u v → rank u < rank v) {p : List α}
    (hp : p.IsChain (fun x y => Arc E y x)) :
    p.Pairwise (fun x y => rank y < rank x) := by
  let : Trans (fun x y : α => rank y < rank x)
      (fun x y => rank y < rank x) (fun x y => rank y < rank x) :=
    ⟨fun hxy hyz => hyz.trans hxy⟩
  exact List.isChain_iff_pairwise.mp (hp.imp (fun _ _ h => hstrict _ _ h))

theorem chain_nodup (E : α → α → Bool) (rank : α → ℕ)
    (hstrict : ∀ u v, Arc E u v → rank u < rank v) {p : List α}
    (hp : p.IsChain (fun x y => Arc E y x)) : p.Nodup := by
  apply (chain_rank_pairwise E rank hstrict hp).imp
  intro x y hxy heq
  subst y
  exact (lt_irrefl _ hxy)

theorem path_length_le_rank (E : α → α → Bool) (rank : α → ℕ)
    (hstrict : ∀ u v, Arc E u v → rank u < rank v) {v : α} {p : List α}
    (hp : EndsPath E v p) : p.length ≤ rank v + 1 := by
  induction p generalizing v with
  | nil => simp
  | cons x xs ih =>
    have hxv : x = v := Option.some.inj hp.1
    subst x
    cases xs with
    | nil => simp
    | cons u tail =>
      have hh := List.isChain_cons_cons.mp hp.2
      have hu := ih (v := u) ⟨rfl, hh.2⟩
      have hr := hstrict u v hh.1
      simp only [List.length_cons] at hu ⊢
      omega

theorem chain_length_le_rank_bound (E : α → α → Bool) (rank : α → ℕ) (bound : ℕ)
    (hstrict : ∀ u v, Arc E u v → rank u < rank v) (hbound : ∀ v, rank v < bound)
    {p : List α} (hp : p.IsChain (fun x y => Arc E y x)) : p.length ≤ bound := by
  cases p with
  | nil => exact Nat.zero_le _
  | cons v tail =>
    exact (path_length_le_rank E rank hstrict ⟨rfl, hp⟩).trans (hbound v)

theorem longestChain_length_le_card (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (bound : ℕ)
    (hstrict : ∀ u v, Arc E u v → rank u < rank v) (hbound : ∀ v, rank v < bound) :
    (longestChain E rank bound).length ≤ n := by
  simpa only [Fintype.card_fin] using (chain_nodup E rank hstrict
    (longestChain_chain E rank bound hstrict hbound)).length_le_card

/-- The height returned by the executable table. -/
def height (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (bound : ℕ) : ℕ :=
  (longestChain E rank bound).length

theorem height_lt_iff (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (bound H : ℕ)
    (hstrict : ∀ u v, Arc E u v → rank u < rank v) (hbound : ∀ v, rank v < bound) :
    height E rank bound < H ↔
      ∀ p : List (Fin n), p.IsChain (fun x y => Arc E y x) → p.length < H := by
  constructor
  · intro h p hp
    exact (longestChain_maximal E rank bound hstrict hbound hp).trans_lt h
  · intro h
    exact h _ (longestChain_chain E rank bound hstrict hbound)

theorem pathTable_length_pos (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ)
    (hstrict : ∀ u v, Arc E u v → rank u < rank v) {k : ℕ} {v : Fin n}
    (hv : rank v < k) : 0 < ((pathTable E rank k)[v]).length := by
  obtain ⟨tail, htail⟩ := List.head?_eq_some_iff.mp (pathTable_correct E rank hstrict hv).1.1
  rw [htail]
  exact Nat.succ_pos _

/-- Compress the supplied topological rank to the true longest-path height. -/
def heightRank (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (bound : ℕ) : Fin n → ℕ :=
  let T := pathTable E rank bound
  fun v => (T[v]).length - 1

theorem heightRank_strict (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (bound : ℕ)
    (hstrict : ∀ u v, Arc E u v → rank u < rank v) (hbound : ∀ v, rank v < bound)
    {u v : Fin n} (huv : Arc E u v) : heightRank E rank bound u < heightRank E rank bound v := by
  have hu := pathTable_correct E rank hstrict (hbound u)
  have hv := pathTable_correct E rank hstrict (hbound v)
  have hlen := hv.2 (v :: (pathTable E rank bound)[u]) (extend_path hu.1 huv)
  have hpos := pathTable_length_pos E rank hstrict (hbound u)
  simp only [List.length_cons] at hlen
  unfold heightRank
  omega

theorem heightRank_bound (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (bound : ℕ)
    (hstrict : ∀ u v, Arc E u v → rank u < rank v) (hbound : ∀ v, rank v < bound)
    (v : Fin n) : heightRank E rank bound v + 1 ≤ height E rank bound := by
  have hc := (pathTable_correct E rank hstrict (hbound v)).1.2
  have hlen := longestChain_maximal E rank bound hstrict hbound hc
  have hpos := pathTable_length_pos E rank hstrict (hbound v)
  unfold heightRank height
  omega

/-- Instrument one materialized layer. Each processed vertex inspects all
`n` raw incoming rows; unprocessed or already processed vertices inspect none. -/
def pathStepCounted (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (k : ℕ)
    (T : PathTable n) : PathTable n × ℕ :=
  let rows : Vector (List (Fin n) × ℕ) n := Vector.ofFn (fun v =>
    if rank v = k then (v :: longest (candidates E T v), n) else (T[v], 0))
  (rows.map Prod.fst, ∑ v : Fin n, (rows[v]).2)

theorem pathStepCounted_value (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (k : ℕ)
    (T : PathTable n) : (pathStepCounted E rank k T).1 = pathStep E rank k T := by
  apply Vector.ext
  intro i hi
  simp only [pathStepCounted, Vector.getElem_map, Vector.getElem_ofFn, pathStep]
  split_ifs <;> rfl

theorem pathStepCounted_tests (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (k : ℕ)
    (T : PathTable n) : (pathStepCounted E rank k T).2 =
      ∑ v : Fin n, if rank v = k then n else 0 := by
  unfold pathStepCounted
  dsimp only
  apply Finset.sum_congr rfl
  intro v _
  change ((Vector.ofFn (fun w : Fin n =>
      if rank w = k then (w :: longest (candidates E T w), n) else (T[w], 0)))[v.val]).2 = _
  rw [Vector.getElem_ofFn]
  split_ifs <;> rfl

def pathTableCounted (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) : ℕ → PathTable n × ℕ
  | 0 => (Vector.replicate n [], 0)
  | k + 1 =>
    let old := pathTableCounted E rank k
    let next := pathStepCounted E rank k old.1
    (next.1, old.2 + next.2)

theorem pathTableCounted_value (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (k : ℕ) :
    (pathTableCounted E rank k).1 = pathTable E rank k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pathTableCounted, pathTable, pathStepCounted_value, ih]

theorem pathTableCounted_tests (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (k : ℕ) :
    (pathTableCounted E rank k).2 =
      ∑ j ∈ Finset.range k, ∑ v : Fin n, if rank v = j then n else 0 := by
  induction k with
  | zero => simp [pathTableCounted]
  | succ k ih => simp only [pathTableCounted, pathStepCounted_tests, Finset.sum_range_succ, ih]

/-- Each vertex is processed once, hence exactly `n²` raw-row tests complete
the table. The layer copies and rank tests contribute another `n * bound`
each. Comparisons of stored chains inspect lists of at most `n` labels. -/
theorem pathTableCounted_tests_complete (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ)
    (bound : ℕ) (hbound : ∀ v, rank v < bound) :
    (pathTableCounted E rank bound).2 = n * n := by
  rw [pathTableCounted_tests, Finset.sum_comm]
  calc
    _ = ∑ _v : Fin n, n := by
      apply Finset.sum_congr rfl
      intro v _
      simp [hbound v]
    _ = n * n := by simp

theorem stored_path_length_le (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ)
    (hstrict : ∀ u v, Arc E u v → rank u < rank v) (k : ℕ) (v : Fin n) :
    ((pathTable E rank k)[v]).length ≤ n := by
  by_cases hv : rank v < k
  · simpa only [Fintype.card_fin] using
      (chain_nodup E rank hstrict (pathTable_correct E rank hstrict hv).1.2).length_le_card
  · rw [pathTable_unprocessed E rank (Nat.le_of_not_gt hv)]
    exact Nat.zero_le _

/-- Reserve a fixed prefix; later graph deletions never alter this list. -/
def reserve (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (bound H : ℕ) : List (Fin n) :=
  (longestChain E rank bound).take H

theorem reserve_spec (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (bound H : ℕ)
    (hstrict : ∀ u v, Arc E u v → rank u < rank v) (hbound : ∀ v, rank v < bound)
    (hheight : H ≤ (longestChain E rank bound).length) :
    (reserve E rank bound H).length = H ∧ (reserve E rank bound H).Nodup ∧
      (reserve E rank bound H).IsChain (fun x y => Arc E y x) := by
  have hc := longestChain_chain E rank bound hstrict hbound
  have hr := hc.take H
  exact ⟨by simp [reserve, List.length_take, min_eq_left hheight],
    chain_nodup E rank hstrict hr, hr⟩

/-- Every reserved chain stays publicly comparable even if its numerical
generating rows are retired later. -/
theorem chain_public_pairwise (E P : α → α → Bool)
    (htrans : ∀ x y z, P x y = true → P y z = true → P x z = true)
    (hEP : ∀ x y, E x y = true → P x y = true)
    {p : List α} (hp : p.IsChain (fun x y => Arc E y x)) :
    p.Pairwise (fun x y => P y x = true) := by
  let : Trans (fun x y : α => P y x = true)
      (fun x y => P y x = true) (fun x y => P y x = true) :=
    ⟨fun hxy hyz => htrans _ _ _ hyz hxy⟩
  exact List.isChain_iff_pairwise.mp (hp.imp (fun _ _ h => hEP _ _ h.2))

/-- Deleting raw rows cannot increase the longest directed path. -/
theorem longestChain_mono (E F : Fin n → Fin n → Bool)
    (hEF : ∀ u v, E u v = true → F u v = true)
    (rankE rankF : Fin n → ℕ) (bE bF : ℕ)
    (hE : ∀ u v, Arc E u v → rankE u < rankE v) (hBE : ∀ v, rankE v < bE)
    (hF : ∀ u v, Arc F u v → rankF u < rankF v) (hBF : ∀ v, rankF v < bF) :
    (longestChain E rankE bE).length ≤ (longestChain F rankF bF).length :=
  longestChain_maximal F rankF bF hF hBF
    ((longestChain_chain E rankE bE hE hBE).imp (fun _ _ h => ⟨h.1, hEF _ _ h.2⟩))

section Degree
variable [Fintype α] [DecidableEq α]

def addRow (E : α → α → Bool) (u v : α) : α → α → Bool :=
  fun x y => E x y || decide (x = u ∧ y = v)

omit [Fintype α] in
@[simp] theorem addRow_true (E : α → α → Bool) (u v x y : α) :
    addRow E u v x y = true ↔ E x y = true ∨ (x = u ∧ y = v) := by
  simp [addRow]

theorem neighbors_mono (E F : α → α → Bool)
    (hEF : ∀ u v, E u v = true → F u v = true) (x : α) :
    neighbors E x ⊆ neighbors F x := by
  intro y hy
  obtain ⟨hne, hxy | hyx⟩ := (mem_neighbors _ _ _).mp hy
  · exact (mem_neighbors _ _ _).mpr ⟨hne, Or.inl (hEF _ _ hxy)⟩
  · exact (mem_neighbors _ _ _).mpr ⟨hne, Or.inr (hEF _ _ hyx)⟩

/-- One new directed row adds at most one neighbor at any vertex. -/
theorem addRow_neighbors (E : α → α → Bool) (u v x : α) :
    neighbors (addRow E u v) x ⊆ insert (if x = u then v else u) (neighbors E x) := by
  intro y hy
  obtain ⟨hne, hxy | hyx⟩ := (mem_neighbors _ _ _).mp hy
  · rcases (addRow_true _ _ _ _ _).mp hxy with hxy | ⟨hxu, hyv⟩
    · exact Finset.mem_insert.mpr (Or.inr ((mem_neighbors _ _ _).mpr ⟨hne, Or.inl hxy⟩))
    · exact Finset.mem_insert.mpr (Or.inl (by simp only [hxu, ite_true]; exact hyv))
  · rcases (addRow_true _ _ _ _ _).mp hyx with hyx | ⟨hyu, hxv⟩
    · exact Finset.mem_insert.mpr (Or.inr ((mem_neighbors _ _ _).mpr ⟨hne, Or.inr hyx⟩))
    · have hxu : x ≠ u := by intro h; exact hne (hyu.trans h.symm)
      exact Finset.mem_insert.mpr (Or.inl (by simpa only [if_neg hxu] using hyu))

theorem addRow_degree_le (E : α → α → Bool) (u v : α) (D : ℕ)
    (hD : ∀ x, (neighbors E x).card ≤ D) (x : α) :
    (neighbors (addRow E u v) x).card ≤ D + 1 :=
  (Finset.card_le_card (addRow_neighbors E u v x)).trans
    ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right (hD x) 1))

theorem degree_mono (E F : α → α → Bool)
    (hEF : ∀ u v, E u v = true → F u v = true) (x : α) :
    (neighbors E x).card ≤ (neighbors F x).card := Finset.card_le_card (neighbors_mono E F hEF x)

end Degree

/-- Deterministic scan for a degree witness in the present free labels. -/
def degreeWitness (E : Fin n → Fin n → Bool) (free : Finset (Fin n)) (D : ℕ) : Option (Fin n) :=
  (List.finRange n).find? (fun v => decide (v ∈ free ∧ D ≤ (neighbors E v).card))

theorem degreeWitness_some (E : Fin n → Fin n → Bool) (free : Finset (Fin n)) (D : ℕ)
    {v : Fin n} (hv : degreeWitness E free D = some v) : v ∈ free ∧ D ≤ (neighbors E v).card := by
  have h := List.find?_some (p := fun w => decide (w ∈ free ∧ D ≤ (neighbors E w).card)) hv
  exact of_decide_eq_true h

theorem degreeWitness_none (E : Fin n → Fin n → Bool) (free : Finset (Fin n)) (D : ℕ) :
    degreeWitness E free D = none ↔ ∀ v ∈ free, (neighbors E v).card < D := by
  simp [degreeWitness, List.find?_eq_none]

/-- Shift the old descendants of the new head by one complete old height.
The reachability table is materialized once. -/
def rankAfterAdd (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (H : ℕ)
    (v : Fin n) : Fin n → ℕ :=
  let R := tableClosure E
  fun x => rank x + if lookup R v x = true then H else 0

theorem rankAfterAdd_bound (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (H : ℕ)
    (hbound : ∀ x, rank x < H) (v x : Fin n) : rankAfterAdd E rank H v x < 2 * H := by
  have hx := hbound x
  unfold rankAfterAdd
  split_ifs <;> omega

/-- Acyclic insertion admits an explicit rank below twice the old height,
even if the old ranks do not order the new endpoints. -/
theorem rankAfterAdd_strict (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (H : ℕ)
    (hstrict : ∀ x y, Arc E x y → rank x < rank y) (hbound : ∀ x, rank x < H)
    (u v : Fin n) (hback : closure E v u = false) :
    ∀ x y, Arc (addRow E u v) x y →
      rankAfterAdd E rank H v x < rankAfterAdd E rank H v y := by
  intro x y hxy
  rcases (addRow_true E u v x y).mp hxy.2 with hOld | ⟨hxu, hyv⟩
  · have hr := hstrict x y ⟨hxy.1, hOld⟩
    simp only [rankAfterAdd, lookup_tableClosure]
    by_cases hx : closure E v x = true
    · have hy := closure_trans E v x y hx (closure_old E hOld)
      simp only [if_pos hx, if_pos hy]
      omega
    · by_cases hy : closure E v y = true
      · simp only [if_neg hx, if_pos hy]
        omega
      · simp only [if_neg hx, if_neg hy]
        exact hr
  · subst x
    subst y
    have hu := hbound u
    simp only [rankAfterAdd, lookup_tableClosure, hback, Bool.false_eq_true,
      if_false, closure_refl, if_true, Nat.add_zero]
    omega

theorem addRow_height_le (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (H : ℕ)
    (hstrict : ∀ x y, Arc E x y → rank x < rank y) (hbound : ∀ x, rank x < H)
    (u v : Fin n) (hback : closure E v u = false) {p : List (Fin n)}
    (hp : p.IsChain (fun x y => Arc (addRow E u v) y x)) : p.length ≤ 2 * H :=
  chain_length_le_rank_bound _ (rankAfterAdd E rank H v) (2 * H)
    (rankAfterAdd_strict E rank H hstrict hbound u v hback)
    (rankAfterAdd_bound E rank H hbound v) hp

/-- The strict version used after a repair established height below `H`. -/
theorem addRow_height_lt (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (H : ℕ)
    (hstrict : ∀ x y, Arc E x y → rank x < rank y) (hbound : ∀ x, rank x + 1 < H)
    (u v : Fin n) (hback : closure E v u = false) {p : List (Fin n)}
    (hp : p.IsChain (fun x y => Arc (addRow E u v) y x)) : p.length < 2 * H := by
  have hb : ∀ x, rank x < H - 1 := fun x => by have := hbound x; omega
  have hh := addRow_height_le E rank (H - 1) hstrict hb u v hback hp
  have hH := hbound u
  omega

/-- Apply the insertion height bound to the actual result of the DP test. -/
theorem addRow_height_from_test (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (bound H : ℕ)
    (hstrict : ∀ x y, Arc E x y → rank x < rank y) (hbound : ∀ x, rank x < bound)
    (htest : height E rank bound < H) (u v : Fin n) (hback : closure E v u = false)
    {p : List (Fin n)} (hp : p.IsChain (fun x y => Arc (addRow E u v) y x)) :
    p.length < 2 * H :=
  addRow_height_lt E (heightRank E rank bound) H
    (fun _ _ huv => heightRank_strict E rank bound hstrict hbound huv)
    (fun x => (heightRank_bound E rank bound hstrict hbound x).trans_lt htest) u v hback hp

section Termination

/-- The proper generating rows, counted once in their directed orientation. -/
def rawRows (E : Fin n → Fin n → Bool) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ E p.1 p.2 = true)

@[simp] theorem mem_rawRows (E : Fin n → Fin n → Bool) (u v : Fin n) :
    (u, v) ∈ rawRows E ↔ Arc E u v := by simp [rawRows, Arc]

def eraseRow (E : Fin n → Fin n → Bool) (u v : Fin n) : Fin n → Fin n → Bool :=
  fun x y => if x = u ∧ y = v then false else E x y

def eraseVertex (E : Fin n → Fin n → Bool) (v : Fin n) : Fin n → Fin n → Bool :=
  fun x y => E x y && decide (x ≠ v ∧ y ≠ v)

theorem eraseRow_old (E : Fin n → Fin n → Bool) (u v x y : Fin n)
    (h : eraseRow E u v x y = true) : E x y = true := by
  by_cases hh : x = u ∧ y = v
  · simp [eraseRow, hh] at h
  · simpa only [eraseRow, if_neg hh] using h

theorem eraseVertex_old (E : Fin n → Fin n → Bool) (v x y : Fin n)
    (h : eraseVertex E v x y = true) : E x y = true := by
  simp only [eraseVertex, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem rawRows_mono (E F : Fin n → Fin n → Bool)
    (hEF : ∀ x y, E x y = true → F x y = true) : rawRows E ⊆ rawRows F := by
  rintro ⟨u, v⟩ h
  obtain ⟨hne, huv⟩ := (mem_rawRows E u v).mp h
  exact (mem_rawRows F u v).mpr ⟨hne, hEF u v huv⟩

theorem rawRows_eraseRow (E : Fin n → Fin n → Bool) (u v : Fin n) :
    rawRows (eraseRow E u v) = (rawRows E).erase (u, v) := by
  ext p
  rcases p with ⟨x, y⟩
  simp [rawRows, eraseRow, Prod.ext_iff]
  tauto

theorem eraseRow_count_lt (E : Fin n → Fin n → Bool) {u v : Fin n} (h : Arc E u v) :
    (rawRows (eraseRow E u v)).card < (rawRows E).card := by
  rw [rawRows_eraseRow]
  exact Finset.card_erase_lt_of_mem ((mem_rawRows E u v).mpr h)

theorem eraseVertex_count_le (E : Fin n → Fin n → Bool) (v : Fin n) :
    (rawRows (eraseVertex E v)).card ≤ (rawRows E).card :=
  Finset.card_le_card (rawRows_mono _ _ (eraseVertex_old E v))

/-- The finite combinatorial state whose measure certifies the repair loop. -/
structure RepairState (n : ℕ) where
  free : Finset (Fin n)
  rows : Fin n → Fin n → Bool

def RepairState.measure (s : RepairState n) : ℕ := s.free.card + (rawRows s.rows).card

/-- Every performed normalization retires a live row or a still-free vertex.
The policy supplying these moves can also carry the weak-map certificates. -/
inductive Move (s : RepairState n)
  | retire (u v : Fin n) (live : Arc s.rows u v)
  | promote (v : Fin n) (free : v ∈ s.free)

def applyMove (s : RepairState n) : Move s → RepairState n
  | .retire u v _ => ⟨s.free, eraseRow s.rows u v⟩
  | .promote v _ => ⟨s.free.erase v, eraseVertex s.rows v⟩

theorem applyMove_measure_lt (s : RepairState n) (m : Move s) :
    (applyMove s m).measure < s.measure := by
  cases m with
  | retire u v live => exact Nat.add_lt_add_left (eraseRow_count_lt s.rows live) _
  | promote v free =>
    have hfree := Finset.card_erase_lt_of_mem free
    have hrows := eraseVertex_count_le s.rows v
    exact Nat.add_lt_add_of_lt_of_le hfree hrows

/-- A total executable driver. It stops precisely when the supplied concrete
normalization policy has no further operation. The second component records
the number of operations actually performed. -/
def normalize (choose : (s : RepairState n) → Option (Move s)) (s : RepairState n) :
    RepairState n × ℕ :=
  match choose s with
  | none => (s, 0)
  | some m =>
    let r := normalize choose (applyMove s m)
    (r.1, r.2 + 1)
termination_by s.measure
decreasing_by exact applyMove_measure_lt s m

theorem normalize_spec (choose : (s : RepairState n) → Option (Move s)) (s : RepairState n) :
    (choose (normalize choose s).1).isNone = true ∧
      (normalize choose s).2 + (normalize choose s).1.measure ≤ s.measure := by
  generalize hm : s.measure = bound
  induction bound using Nat.strong_induction_on generalizing s with
  | h bound ih =>
    cases hc : choose s with
    | none =>
      have heq : normalize choose s = (s, 0) := by rw [normalize, hc]
      have hstop := congrArg (fun r : RepairState n × ℕ => (choose r.1).isNone) heq
      refine ⟨hstop.trans (by simp [hc]), ?_⟩
      simp only [heq, zero_add, hm, le_refl]
    | some m =>
      have hlt : (applyMove s m).measure < bound := by
        rw [← hm]
        exact applyMove_measure_lt s m
      have hh := ih (applyMove s m).measure hlt (applyMove s m) rfl
      have heq : normalize choose s =
          ((normalize choose (applyMove s m)).1, (normalize choose (applyMove s m)).2 + 1) := by
        rw [normalize, hc]
      have hstop := congrArg (fun r : RepairState n × ℕ => (choose r.1).isNone) heq
      refine ⟨hstop.trans hh.1, ?_⟩
      simp only [heq]
      have := hh.2
      omega

theorem normalize_stopped (choose : (s : RepairState n) → Option (Move s)) (s : RepairState n) :
    choose (normalize choose s).1 = none :=
  Option.isNone_iff_eq_none.mp (normalize_spec choose s).1

theorem normalize_steps_le (choose : (s : RepairState n) → Option (Move s)) (s : RepairState n) :
    (normalize choose s).2 ≤ s.free.card + (rawRows s.rows).card := by
  have h := (normalize_spec choose s).2
  exact (Nat.le_add_right _ _).trans h

theorem rawRows_card_le (E : Fin n → Fin n → Bool) : (rawRows E).card ≤ n * n := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using (rawRows E).card_le_univ

theorem normalize_steps_le_quadratic (choose : (s : RepairState n) → Option (Move s))
    (s : RepairState n) : (normalize choose s).2 ≤ n + n * n := by
  have hf : s.free.card ≤ n := by simpa only [Fintype.card_fin] using s.free.card_le_univ
  exact (normalize_steps_le choose s).trans (Nat.add_le_add hf (rawRows_card_le s.rows))

end Termination

end SortingAdversary.Optimal.SparseRepairGraph
