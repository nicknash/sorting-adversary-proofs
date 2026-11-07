import SortingAdversary.Optimal.PoolState
import SortingAdversary.Optimal.SeparatedPins
import SortingAdversary.Optimal.ColourTransport
import Mathlib.Data.List.Pairwise

/-!
# The finite recursive pool tree

Children are keyed by their parent's current colour positions. Palette
changes transport these keys through the proved immutable-colour embedding.
The tree invariant identifies each child's actual members exactly with its
parent's physical pins at that position; unused dummy coordinates never enter
this identification.
-/

namespace SortingAdversary.Optimal.PoolTree

open PoolState
open scoped BigOperators

inductive Tree (n : ℕ) where
  | node (identity : ℕ) (pool : Pool n) (children : List (ℕ × Tree n))

namespace Tree

variable {n : ℕ}

def pool : Tree n → Pool n
  | .node _ p _ => p

def pinIndex (p : Pool n) (x : Fin n) : Option ℕ := (p.pins x).map Fin.val

/-- The exact product of the represented map counts at all stored pools. -/
def count : Tree n → ℕ
  | .node _ p children => p.system.count * (children.map (fun a => count a.2)).prod
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹a ∈ children›
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

/-- The number of stored nodes, including the root. -/
def nodes : Tree n → ℕ
  | .node _ _ children => 1 + (children.map (fun a => nodes a.2)).sum
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹a ∈ children›
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

/-- Original-label occurrences in the finite tree. -/
def population : Tree n → ℕ
  | .node _ p children => p.members.card + (children.map (fun a => population a.2)).sum
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹a ∈ children›
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

/-- Each label's free occurrences, computed over the actual stored tree. -/
def freeOccurrences (x : Fin n) : Tree n → ℕ
  | .node _ p children => (if x ∈ p.free then 1 else 0) +
      (children.map (fun a => freeOccurrences x a.2)).sum
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹a ∈ children›
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

/-- Structural invariants of the actual recursive representation. -/
inductive WellFormed : Tree n → Prop where
  | node (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
      (keys : (children.map Prod.fst).Nodup)
      (bounds : ∀ a ∈ children, a.1 < p.palette + 1)
      (occupied : ∀ a ∈ children, a.2.pool.members.Nonempty)
      (separated : SeparatedPins.Separated p)
      (children_ok : ∀ a ∈ children, WellFormed a.2)
      (members : ∀ a ∈ children, ∀ x,
        x ∈ a.2.pool.members ↔ x ∈ p.members ∧ pinIndex p x = some a.1)
      (covered : ∀ x ∈ p.members, ∀ c, pinIndex p x = some c →
        ∃ t, (c, t) ∈ children) : WellFormed (.node identity p children)

def initial (N : ℕ) : Tree (N + 2) := .node 0 (initialRoot N) []

theorem initial_wellFormed (N : ℕ) : (initial N).WellFormed := by
  refine .node 0 (initialRoot N) [] (by simp) (by simp) (by simp)
    (SeparatedPins.root_separated N) (by simp) (by simp) ?_
  intro x hx c hc
  simp [pinIndex, initialRoot] at hc

@[simp] theorem initial_count (N : ℕ) : (initial N).count = (N + 2) ^ (N + 2) := by
  simp [initial, count]

@[simp] theorem initial_nodes (N : ℕ) : (initial N).nodes = 1 := by
  simp [initial, nodes]

@[simp] theorem initial_freeOccurrences (N : ℕ) (x : Fin (N + 2)) :
    (initial N).freeOccurrences x = 1 := by
  simp [initial, freeOccurrences]

/-- Empty child storage before its first actual admission. -/
def empty (n identity : ℕ) : Tree n := .node identity (emptyPool n) []

theorem empty_wellFormed (n identity : ℕ) : (empty n identity).WellFormed := by
  refine .node identity (emptyPool n) [] (by simp) (by simp) (by simp)
    (SeparatedPins.empty_separated n) (by simp) (by simp) ?_
  intro x hx
  simp [emptyPool] at hx

@[simp] theorem empty_count (n identity : ℕ) : (empty n identity).count = 1 := by
  simp [empty, count]

/-- Transport current colour positions while retaining the child trees. -/
def mapKeys {K L : ℕ} (e : Fin K → Fin L) (children : List (ℕ × Tree n)) :
    List (ℕ × Tree n) := children.map (fun a => (ColourTransport.extend e a.1, a.2))

theorem option_index_transport {K L : ℕ} (e : Fin K → Fin L) (o : Option (Fin K)) :
    (o.map e).map Fin.val = (o.map Fin.val).map (ColourTransport.extend e) := by
  cases o with
  | none => rfl
  | some c => simp

theorem map_option_eq_some {α β : Type*} (e : α → β) (he : Function.Injective e)
    (o : Option α) (c : α) : o.map e = some (e c) ↔ o = some c := by
  cases o with
  | none => simp
  | some d => simp only [Option.map_some, Option.some.injEq, he.eq_iff]

theorem admission_pinIndex (p : Pool n) (v : Fin n) (a : p.Admission v)
    (x : Fin n) (hx : x ≠ v) :
    pinIndex a.next x = (pinIndex p x).map (ColourTransport.extend a.embed) := by
  unfold pinIndex
  rw [a.pin_old x hx]
  exact option_index_transport a.embed _

/-- Admit an isolated new member at this root. Existing child pools retain
their laws; only their parent-colour keys may be shifted by a top append. -/
def admitRoot (t : Tree n) (v : Fin n) (hv : v ∉ t.pool.members) : Tree n :=
  match t with
  | .node identity p children =>
      let a := p.admission v hv
      .node identity a.next (mapKeys a.embed children)

theorem admitRoot_wellFormed (t : Tree n) (h : t.WellFormed)
    (v : Fin n) (hv : v ∉ t.pool.members) : (t.admitRoot v hv).WellFormed := by
  cases h with
  | node identity p children hkeys hb ho hs hchild hm hc =>
      change v ∉ p.members at hv
      let a := p.admission v hv
      change WellFormed (.node identity a.next (mapKeys a.embed children))
      have he := ColourTransport.extend_injective a.embed a.embed_strict
      refine .node identity a.next (mapKeys a.embed children) ?_ ?_ ?_
        (SeparatedPins.admission_separated p v hv a hs) ?_ ?_ ?_
      · simpa only [mapKeys, List.map_map, Function.comp_def] using hkeys.map he
      · intro b hmem
        obtain ⟨b, hbmem, rfl⟩ := List.mem_map.mp hmem
        exact ColourTransport.extend_bound a.embed b.1 (hb b hbmem)
      · intro b hmem
        obtain ⟨b, hbmem, rfl⟩ := List.mem_map.mp hmem
        exact ho b hbmem
      · intro b hmem
        obtain ⟨b, hbmem, rfl⟩ := List.mem_map.mp hmem
        exact hchild b hbmem
      · intro b hmem x
        obtain ⟨b, hbmem, rfl⟩ := List.mem_map.mp hmem
        rw [hm b hbmem x, a.members_eq]
        by_cases hx : x = v
        · subst x
          simp [hv, pinIndex, a.pin_new]
        · rw [admission_pinIndex p v a x hx, map_option_eq_some _ he]
          simp [hx]
      · intro x hx c hpin
        have hxv : x ≠ v := by
          rintro rfl
          simp [pinIndex, a.pin_new] at hpin
        have hxm : x ∈ p.members := by
          rw [a.members_eq] at hx
          exact (Finset.mem_insert.mp hx).resolve_left hxv
        rw [admission_pinIndex p v a x hxv] at hpin
        cases hpx : pinIndex p x with
        | none => simp [hpx] at hpin
        | some d =>
            have hdc : ColourTransport.extend a.embed d = c := by simpa [hpx] using hpin
            obtain ⟨child, hmem⟩ := hc x hxm d hpx
            refine ⟨child, List.mem_map.mpr ⟨(d, child), hmem, ?_⟩⟩
            simp [hdc]

/-- The exact child-birth multiplier applies to the entire existing subtree,
including any descendants that answered earlier comparisons. -/
theorem admitRoot_count (t : Tree n) (v : Fin n) (hv : v ∉ t.pool.members) :
    (t.admitRoot v hv).count = t.count * ((t.admitRoot v hv).pool.palette + 1) := by
  cases t with
  | node identity p children =>
      let a := p.admission v hv
      change (Tree.node identity a.next (mapKeys a.embed children)).count =
        (Tree.node identity p children).count * (a.next.palette + 1)
      rw [count, count, a.count_eq]
      simp only [mapKeys, List.map_map, Function.comp_def]
      ac_rfl

theorem admitRoot_nodes (t : Tree n) (v : Fin n) (hv : v ∉ t.pool.members) :
    (t.admitRoot v hv).nodes = t.nodes := by
  cases t with
  | node identity p children => simp [admitRoot, nodes, mapKeys, Function.comp_def]

end Tree

end SortingAdversary.Optimal.PoolTree
