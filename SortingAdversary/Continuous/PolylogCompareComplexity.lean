import SortingAdversary.Continuous.PolylogCompareBudget
import SortingAdversary.Continuous.PolylogTestWork

/-!
# Worst-case work for one active comparison

The bound applies to the stored implementation of the controller. Its only
state hypotheses are the semantic and storage invariants preserved across
queries. The number of trials and the length of the local repair both
appear in the composition, including on the final query before freezing.
-/

namespace SortingAdversary.Continuous.PolylogCompareWork

open PolylogCompare
open PolylogAdversary (extra parameter)
open Optimal.Parameters (logCap)
open PolylogResources (tableHeight)
open PolylogTestWork (stageBound kernelBound)

private theorem local_stage_polylog {L t b : ℕ} (ht : t ≤ 20*(L+1)) (hb : b ≤ 20*(L+1)) :
    stageBound t b L ≤ 4000000*(L+1)^8 := by
  let A := 20*(L+1)
  have t' : t ≤ A := ht
  have b' : b ≤ A := hb
  unfold stageBound kernelBound PolylogPrefix.readBound
  calc
    _ ≤ (8*A+2*L+10)*(20000*(L+1)^7) +
        (2*(7*L+4)+2*L*(4*A+3)+3+
        2*L*((1+(L+1)*((A+1)*(A+5)+4)+(A+1)*(A+7)+2*L+9)+2)+8*L+2+
        (1+(L+1)*((A+1)*(A+5)+4)+(A+1)*(A+7)+2*L+9)+
        1000*(L+1)^5+72*(L+1)^2+6*L+35) := by gcongr
    _ ≤ _ := by dsimp [A]; ring_nf; omega

theorem active_query_polylog {n : ℕ} (hk : 64 ≤ parameter n) (m : ScheduledMemory n)
    (M : Controller.Memory n) (ready : Controller.Ready (parameter n) M) (hm : Tracks m M)
    (q : Query n) :
    (PolylogCompare.compare (binaryPoint n) (parameter n) m q).work ≤
      20000000*(logCap n+1)^9 := by
  let L := logCap n
  let K := stageBound (tableHeight n) (binaryPoint n).size L
  have hc : Tests n (tableHeight n) (binaryPoint n).size (binaryPoint n) (parameter n) K := by
    intro u sh
    let z := fun j => u.cache.lookup j false
    exact ⟨PolylogTestWork.pair_work extra hk sh u.spatial.walls u.heap z _ _,
      PolylogTestWork.threshold_work extra hk sh u.spatial.walls u.heap z _ _,
      PolylogTestWork.central_work extra hk sh u.spatial.walls u.heap z _ _⟩
  have hs := PolylogSchedule.capacity_bits (extra := extra) hk (le_refl (logCap n))
  change (binaryPoint n).size ≤ 5+(L+1)*3 at hs
  have hK : K ≤ 4000000*(L+1)^8 := local_stage_polylog
    (by dsimp [tableHeight,L]; omega) (by omega)
  apply (scheduled_compare_work hk m M ready hm q hc).trans
  calc
    _ ≤ 200000*(L+1)^4 + (L+3)*(4000000*(L+1)^8) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hK) _
    _ ≤ _ := by change _ ≤ 20000000*(L+1)^9; ring_nf; omega

end SortingAdversary.Continuous.PolylogCompareWork
