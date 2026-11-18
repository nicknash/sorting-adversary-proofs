import SortingAdversary.Continuous.PolylogStorage
import SortingAdversary.Continuous.PolylogAddressOrder
import SortingAdversary.Continuous.PolylogEmbed

/-!
# Stored memory and initialization

The label tables contain integer addresses. Extending the interned-block
heap changes the logical interpretation of newly allocated addresses.
Previously represented endpoint and path values can be transported through
that extension without any traversal or update of the label tables.
-/

namespace SortingAdversary.Continuous.PolylogCompare

open PolylogBits
open Optimal.PrimitiveWork (Result)
variable {n t b : ℕ}

structure Memory (n t b : ℕ) where
  spatial : PolylogStorage.State n t
  heap : Heap
  valid : heap.Valid
  typed : heap.Typed
  cache : Cached blockStore heap b
  zero : ℕ
  one : ℕ

noncomputable abbrev Memory.decode (m : Memory n t b) (D : ℕ) :=
  PolylogAddressOrder.decode blockStore m.heap D b

def Memory.less (m : Memory n t b) := PolylogAddressOrder.less m.heap b

theorem Memory.less_correct (m : Memory n t b) (D i j : ℕ) :
    (m.less i j).value = true ↔ m.decode D i < m.decode D j :=
  PolylogAddressOrder.correct blockStore m.heap m.valid m.typed D b i j

theorem Memory.decode_injective (m : Memory n t b) (D : ℕ) : Function.Injective (m.decode D) :=
  PolylogAddressOrder.injective blockStore m.heap m.valid D b

structure Memory.Represents (m : Memory n t b) (D : ℕ) (nodes : List (List ℕ))
    (M : Controller.Memory n) : Prop where
  spatial : PolylogStorage.Represents m.spatial nodes M (m.decode D)
  zero_value : m.decode D m.zero = 0
  one_value : m.decode D m.one = 1
  paths_nonneg : ∀ x c, c ∈ M.tree.location x → 0 ≤ c
  paths_bounded : ∀ x c, c ∈ M.tree.location x → c ≤ 1

def Memory.withHeap (m : Memory n t b) (H : Heap) (v : H.Valid) (e : H.Extends m.heap) :
    Memory n t b :=
  {m with heap := H, valid := v, typed := e.typed m.typed, cache := m.cache.lift e}

theorem Memory.storage_lift {m : Memory n t b} {D : ℕ} {nodes : List (List ℕ)}
    {M : Controller.Memory n} (hm : m.Represents D nodes M) (geom : Controller.Geometric M)
    (H : Heap) (v : H.Valid) (e : H.Extends m.heap) :
    (m.withHeap H v e).Represents D nodes M := by
  let m' := m.withHeap H v e
  have persist (i : ℕ) (hi : 0 ≤ m.decode D i) : m'.decode D i = m.decode D i :=
    PolylogAddressOrder.persistent m.valid v e hi
  refine ⟨⟨hm.spatial.graph, ⟨?_, ?_⟩, hm.spatial.directory, ?_⟩, ?_, ?_, hm.paths_nonneg, hm.paths_bounded⟩
  · intro y
    exact (persist (m.spatial.walls.lower.get y.val).value (by rw [hm.spatial.walls.1]; exact (geom.rationalBounds y).1)).trans
      (hm.spatial.walls.1 y)
  · intro y
    exact (persist (m.spatial.walls.upper.get y.val).value (by rw [hm.spatial.walls.2]; exact (geom.rationalBounds y).1.trans (geom.widths y).le)).trans
      (hm.spatial.walls.2 y)
  · intro x
    obtain ⟨p,hp,hd⟩ := hm.spatial.located x
    refine ⟨p,hp,?_⟩
    apply Eq.trans _ hd
    apply List.map_congr_left
    intro i hi
    apply persist
    apply hm.paths_nonneg x
    rw [← hd]
    exact List.mem_map.mpr ⟨i,hi,rfl⟩
  · exact (persist m.zero (by rw [hm.zero_value])).trans hm.zero_value
  · exact (persist m.one (by rw [hm.one_value]; decide)).trans hm.one_value

/-- The two initial wall handles are the all-zero block and the block with
a single one at the binary point. All unchanged rows and zero blocks are
shared through persistent tables. -/
def initialMemory (n t b D : ℕ) : Memory n t b :=
  let base := initializeCache blockStore b
  let w := PolylogEmbed.embedAddr D 0 1 base.valid base.cache (le_refl b)
  let z := base.cache.lookup b false
  ⟨PolylogStorage.initial n t z w.cell.addr, w.heap, w.valid, w.growth.typed base.typed,
    base.cache.lift w.growth, z, w.cell.addr⟩

theorem initialize_represents (n t b D : ℕ) (hD : D < 2^b) :
    (initialMemory n t b D).Represents D [[]] (Controller.initial n) := by
  let base := initializeCache blockStore b
  let w := PolylogEmbed.embedAddr D 0 1 base.valid base.cache (le_refl b)
  let z := base.cache.lookup b false
  have rz := (base.cache.spec (le_refl b) false).lift w.growth
  have hzero : PolylogAddressOrder.decode blockStore w.heap D b z = 0 := by
    rw [PolylogAddressOrder.decode_of_rep w.valid rz]
    simp [PolylogBlockAnchor.coord]
  have hone : PolylogAddressOrder.decode blockStore w.heap D b w.cell.addr = 1 := by
    obtain ⟨a,ha,hv⟩ := PolylogEmbed.embedAddr_represents D 0 1 base.valid base.cache
      (le_refl b) hD (Nat.zero_le _) (by decide)
    exact (PolylogAddressOrder.decode_of_rep w.valid ha).trans (by simpa using hv)
  refine ⟨PolylogStorage.initial_represents n t z w.cell.addr _ hzero hone, hzero, hone, ?_, ?_⟩ <;>
    simp [Controller.initial, TreeState.initial]

end SortingAdversary.Continuous.PolylogCompare
