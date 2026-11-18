import SortingAdversary.Continuous.PolylogAllocation
import SortingAdversary.Continuous.PolylogAligned
import SortingAdversary.Continuous.PolylogMint

/-!
# Correctness of an allocated refinement

The old cursor and wall handles keep their meanings in the extended heap.
The new handle decodes to an interior dyadic, so the sparse mutation has
the same normalization and exact child as the semantic controller. All
four table indices fit the fixed height throughout the move.
-/

namespace SortingAdversary.Continuous.PolylogCompare

open PolylogBits PolylogResources FiniteAveraging
open Optimal.Parameters (logCap)
variable {n b : ℕ}

theorem move_aligned (D k : ℕ) {m : Memory n (tableHeight n) b} {M : Controller.Memory n}
    (align : Aligned D (logCap n) m M) (adm : Controller.Admissible k M)
    (hb : b ≤ 5+(logCap n+1)*3) (hm : Controller.totalDepth M ≤ Controller.horizon n+logCap n+2)
    (x : Fin n) (w : WriteResult m) (c : ℚ) (written : w.out.Represents blockStore b D c)
    (growth : w.out.heap.next ≤ m.heap.next+perMove (logCap n) b)
    (inside : M.tree.system.lower x < c ∧ c < M.tree.system.upper x)
    (grid : OnDyadicGrid (logCap n + 2*Controller.totalDepth M + 2) c) :
    Aligned D (logCap n) (move k m x w).value (Controller.applyMove M (Controller.makeMove M x c)) := by
  let upgraded := m.withHeap w.out.heap w.out.valid w.out.growth
  obtain ⟨nodes, hs⟩ := align.storage
  have newRep : upgraded.Represents D nodes M :=
    Memory.storage_lift hs adm.toGeometric w.out.heap w.out.valid w.out.growth
  obtain ⟨z, hz, hc⟩ := written
  have decode : upgraded.decode D w.out.addr = c :=
    (PolylogAddressOrder.decode_of_rep w.out.valid hz).trans hc
  have pos := (adm.rationalBounds x).1.trans_lt inside.1
  have one := inside.2.trans_le (adm.rationalBounds x).2
  obtain ⟨anchor, value, _⟩ := exists_dyadicAnchor_of_grid grid pos one
  have dyadic := DyadicAnchor.ofRat_correct ⟨anchor, value⟩
  have encoded : (Controller.makeMove M x c).anchor.coordinate = c := dyadic
  obtain ⟨addr, room, depth⟩ := move_indices hs.spatial align.sized hb hm x w.out.valid growth hz
  have result := PolylogMutation.refineState_represents upgraded.less (upgraded.decode D)
    (upgraded.less_correct D) newRep.spatial adm upgraded.zero upgraded.one newRep.zero_value
    newRep.one_value (label_fits n) x w.out.addr addr room depth
    (by simpa only [decode] using dyadic) (by simpa only [decode] using inside)
  obtain ⟨more, _, next⟩ := result
  rw [decode] at next
  have paths {P : ℚ → Prop} (old : ∀ y d, d ∈ M.tree.location y → P d) (fresh : P c) :
      ∀ y d, d ∈ (Controller.applyMove M (Controller.makeMove M x c)).tree.location y → P d := by
    intro y d hd
    by_cases e : y = x
    · subst y
      simp only [Controller.applyMove, TreeState.normalize, TreeState.refineAt, Controller.makeMove_item,
        Function.update_self, List.mem_append, List.mem_singleton, encoded] at hd
      exact hd.elim (old x d) (fun eq => eq.symm ▸ fresh)
    · simp only [Controller.applyMove, TreeState.normalize, TreeState.refineAt, Controller.makeMove_item,
        Function.update_of_ne e] at hd
      exact old _ _ hd
  refine ⟨⟨nodes++more, next, newRep.zero_value, newRep.one_value,
    paths hs.paths_nonneg pos.le, paths hs.paths_bounded one.le⟩, ?_, ?_⟩
  · rw [Controller.totalDepth_applyMove, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]
    apply (align.grid.mono (by omega)).applyMove
    rwa [encoded]
  · rw [Controller.totalDepth_applyMove]
    exact move_sized k m align.sized x w growth

/-- The coordinate statement produced by the executable branch suffices:
interiority certifies that the returned word denotes a canonical block. -/
theorem move_aligned_value (D k : ℕ) {m : Memory n (tableHeight n) b} {M : Controller.Memory n}
    (align : Aligned D (logCap n) m M) (adm : Controller.Admissible k M)
    (hb : b ≤ 5+(logCap n+1)*3) (hm : Controller.totalDepth M ≤ Controller.horizon n+logCap n+2)
    (x : Fin n) (w : WriteResult m) (c : ℚ) (value : w.coordinate D = c)
    (growth : w.out.heap.next ≤ m.heap.next+perMove (logCap n) b)
    (inside : M.tree.system.lower x < c ∧ c < M.tree.system.upper x)
    (grid : OnDyadicGrid (logCap n+2*Controller.totalDepth M+2) c) :
    Aligned D (logCap n) (move k m x w).value (Controller.applyMove M (Controller.makeMove M x c)) := by
  have nonneg : 0 ≤ w.coordinate D := value ▸ ((adm.rationalBounds x).1.trans inside.1.le)
  obtain ⟨z,hz⟩ := (PolylogAddressOrder.nonneg_iff blockStore w.out.heap D b w.out.addr).mp nonneg
  exact move_aligned D k align adm hb hm x w c
    ⟨z,hz,(PolylogAddressOrder.decode_of_rep w.out.valid hz).symm.trans value⟩ growth inside grid

end SortingAdversary.Continuous.PolylogCompare
