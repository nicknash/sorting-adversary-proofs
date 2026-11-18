import SortingAdversary.Continuous.PolylogHierarchy
import SortingAdversary.Continuous.PolylogRows
import SortingAdversary.Continuous.PolylogWallTables

/-!
# Sparse storage for the rounded controller

Each label has two incidence rows, two endpoint handles and a cursor into
the hierarchy. The directory shares children having the same parent and
anchor. The reference history and the lists of path coordinates appear
only in the simulation relation.
-/

namespace SortingAdversary.Continuous.PolylogStorage

open PolylogRouting (Table)
open Optimal.PrimitiveWork (Result)
open PolylogHierarchy (Cursor)
open TreeState (Routing)
variable {n h : ℕ}

structure State (n h : ℕ) where
  graph : PolylogRows.Graph n h
  walls : PolylogWallTables.Walls ℕ h
  directory : PolylogHierarchy.Store h
  locations : Table (Cursor h) h

structure Represents (s : State n h) (nodes : List (List ℕ)) (M : Controller.Memory n)
    (decode : ℕ → ℚ) : Prop where
  graph : s.graph.Valid M.tree.system.edge
  walls : PolylogWallTables.aligned decode s.walls M.tree.system
  directory : PolylogHierarchy.Valid s.directory nodes
  located : ∀ x : Fin n, ∃ p : List ℕ, (s.locations.get x.val).value.At nodes p ∧
    p.map decode = M.tree.location x

def initial (n h zero one : ℕ) : State n h where
  graph := PolylogRows.empty n h
  walls := ⟨Table.fill zero h, Table.fill one h⟩
  directory := PolylogHierarchy.empty h
  locations := Table.fill (PolylogHierarchy.rootCursor h) h

theorem initial_represents (n h zero one : ℕ) (decode : ℕ → ℚ)
    (hz : decode zero = 0) (ho : decode one = 1) :
    Represents (initial n h zero one) [[]] (Controller.initial n) decode := by
  refine ⟨PolylogRows.empty_valid n h, ?_, PolylogHierarchy.empty_valid h, ?_⟩
  · constructor <;> intro x <;> simp [initial, Controller.initial, TreeState.initial, hz, ho]
  · intro x
    exact ⟨[], by simpa [initial] using PolylogHierarchy.root_at h, rfl⟩

def route (s : State n h) (q : Query n) : Result (Routing ℕ) :=
  let a := s.locations.get q.left.val
  let b := s.locations.get q.right.val
  let r := PolylogRouting.query a.value.row b.value.row
  ⟨r.value, a.work+b.work+r.work+2⟩

theorem route_work (s : State n h) (q : Query n) :
    (route s q).work ≤ h*(8*h+9)+16*h+16 := by
  have := PolylogRouting.query_work (s.locations.get q.left.val).value.row
    (s.locations.get q.right.val).value.row
  simp only [route, Table.get_work]
  omega

theorem route_value {s : State n h} {nodes : List (List ℕ)} {M : Controller.Memory n}
    {decode : ℕ → ℚ} (hs : Represents s nodes M decode)
    (hi : Function.Injective decode) (q : Query n) :
    PolylogRouting.decodeRoute decode (route s q).value =
      TreeState.route (M.tree.location q.left) (M.tree.location q.right) := by
  obtain ⟨p, hp, hpl⟩ := hs.located q.left
  obtain ⟨r, hr, hpr⟩ := hs.located q.right
  simp only [route, PolylogRouting.query_eq_route hp.2 hr.2, PolylogRouting.route_map decode hi, hpl, hpr]

def moveCursor (s : State n h) (x : Fin n) (c : ℕ) : Result (State n h) :=
  let p := s.locations.get x.val
  let target := PolylogHierarchy.getOrCreate s.directory p.value c
  let rows := s.locations.put x.val target.value.1
  ⟨{ s with locations := rows.value, directory := target.value.2 },
    p.work+target.work+rows.work+2⟩

theorem moveCursor_work (s : State n h) (x : Fin n) (c : ℕ) :
    (moveCursor s x c).work ≤ 36*h+18 := by
  have := PolylogHierarchy.getOrCreate_work s.directory (s.locations.get x.val).value c
  simp only [moveCursor, Table.get_work, Table.put_work]; omega

theorem moveCursor_spec {s : State n h} {nodes : List (List ℕ)} {M : Controller.Memory n}
    {decode : ℕ → ℚ} (hs : Represents s nodes M decode) (cap : n ≤ 2^h)
    (x : Fin n) (c : ℕ) (hc : c < 2^h) (space : s.directory.next < 2^h)
    (depth : (M.tree.location x).length + 1 < 2^h) :
    let t := (moveCursor s x c).value
    ∃ more : List (List ℕ), more.length ≤ 1 ∧ PolylogHierarchy.Valid t.directory (nodes ++ more) ∧
      ∀ y : Fin n, ∃ p : List ℕ, (t.locations.get y.val).value.At (nodes ++ more) p ∧
        p.map decode = if y = x then M.tree.location x ++ [decode c] else M.tree.location y := by
  obtain ⟨p, hp, hpm⟩ := hs.located x
  have dep : p.length + 1 < 2^h := by simpa [← hpm] using depth
  let r := PolylogHierarchy.getOrCreate s.directory (s.locations.get x.val).value c
  have ht := PolylogHierarchy.getOrCreate_spec hs.directory hp c hc space dep
  have changed : ∃ more : List (List ℕ), more.length ≤ 1 ∧
      PolylogHierarchy.Valid r.value.2 (nodes ++ more) ∧ r.value.1.At (nodes ++ more) (p ++ [c]) := by
    rcases ht with ⟨hv, target, _⟩ | ⟨_, hv, target, _⟩
    · exact ⟨[], by simp, by simpa [r] using hv, by simpa [r] using target⟩
    · exact ⟨[p++[c]], by simp, hv, target⟩
  obtain ⟨more, size, hv, target⟩ := changed
  refine ⟨more, size, hv, ?_⟩
  intro y
  simp only [moveCursor, Table.get_put _ _ _ _ (x.isLt.trans_le cap) (y.isLt.trans_le cap)]
  by_cases he : y = x
  · subst y
    exact ⟨p ++ [c], by simpa [r] using target, by simp [hpm]⟩
  · obtain ⟨v, atv, hv⟩ := hs.located y
    refine ⟨v, ?_, by simpa [he] using hv⟩
    simpa [show y.val ≠ x.val from fun e => he (Fin.ext e)] using atv.append more

end SortingAdversary.Continuous.PolylogStorage
