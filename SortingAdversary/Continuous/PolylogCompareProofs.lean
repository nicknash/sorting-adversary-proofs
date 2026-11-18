import SortingAdversary.Continuous.PolylogCheckProof
import SortingAdversary.Continuous.PolylogCompareSteps

/-!
# Exact refinement of the rounded comparison controller

Starting from represented storage and an admissible active depth, the
sparse comparison returns the same answer and represents the same next
memory as the rounded policy. The prepared tests, prefix allocator,
canonical short writer, graph updates, and bounded repair are all concrete.
-/

namespace SortingAdversary.Continuous.PolylogCompare

open PolylogAdversary (parameter extra)

/-- One actual comparison. The rounded strategy fixes the binary point
and table heights at initialization. -/
theorem compare_aligned {n : ℕ} (hk : 64 ≤ parameter n) (m : ScheduledMemory n)
    (M : Controller.Memory n) (ready : Controller.Ready (parameter n) M) (align : Tracks m M)
    (depth : Controller.totalDepth M ≤ Controller.horizon n) (q : Query n) :
    let r := (PolylogAdversary.policy n).compare (parameter n) M q
    ∃ u, (compare (binaryPoint n) (parameter n) m q).value = some (u,r.answer) ∧ Tracks u r.memory := by
  apply compare_simulation hk _ _ m M ready align depth q
  · intro s N hs hN query
    obtain ⟨_,rep⟩ := hs.storage
    exact check_value extra rep hk hN.admissible (Nat.lt_size_self _) (binaryPoint_short n) query
  · intro s N hs hN x
    obtain ⟨_,rep⟩ := hs.storage
    exact candidate_value extra rep hk hN (Nat.lt_size_self _) (binaryPoint_short n) x

end SortingAdversary.Continuous.PolylogCompare
