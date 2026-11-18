import SortingAdversary.Continuous.PolylogWordCompare
import SortingAdversary.Continuous.PolylogKernelProfile

/-! # Instantiating the physical comparison bound with finite-window operations -/
namespace SortingAdversary.Continuous.PolylogWordCompare

open PolylogCompare
open PolylogLocalProfile (Kernels Correct Priced)
open PolylogAdversary (parameter extra)
open PolylogResources (tableHeight)
open Optimal.Parameters (logCap)
open Controller (Ready Admissible totalDepth horizon)
variable {n : ℕ}

/-- The cached parameters are an argument, as they are in the online machine. -/
def window (K : Kernels) (P : PolylogPrepared.Params) : Window n where
  pair m x y := (PolylogLocalProfile.pair K m.spatial.graph m.spatial.walls m.heap
    (fun j => m.cache.lookup j false) (binaryPoint n).size (binaryPoint n) P x y).work
  threshold m x c := (PolylogLocalProfile.threshold K m.spatial.graph m.spatial.walls m.heap
    (fun j => m.cache.lookup j false) (binaryPoint n).size (binaryPoint n) P x c).work
  central m x := (PolylogLocalProfile.central K m.spatial.graph m.spatial.walls m.heap
    (fun j => m.cache.lookup j false) (binaryPoint n).size (binaryPoint n) P x).work

private theorem window_bounded {K : Kernels} (ok : Correct K) (price : Priced K)
    (hk : 64 ≤ parameter n) : (window (n := n) K (.stage (parameter n))).Bounded
      (PolylogLocalProfile.total (tableHeight n) (binaryPoint n).size (tableHeight n) (logCap n)) := by
  intro m M hm adm depth
  obtain ⟨_,rep⟩ := hm.storage
  have shape : PolylogCompareWork.Shape m.spatial.graph (parameter n) :=
    ⟨M.tree.system.edge,rep.spatial.graph,adm.noLoop,adm.degree⟩
  have fit := (PolylogResources.indices_fit hm.sized
    (PolylogSchedule.capacity_bits (extra := extra) hk le_rfl)
    (depth.trans (depthLimit_table hk))).2
  have room : m.heap.next < 2^tableHeight n := (Nat.le_add_right ..).trans_lt fit
  have pos : 0 < tableHeight n := by unfold tableHeight; omega
  let zero := fun j => m.cache.lookup j false
  exact ⟨PolylogLocalProfile.pair_work ok price extra hk shape m.spatial.walls m.heap zero _ _ _
      m.valid pos room,
    PolylogLocalProfile.threshold_work ok price extra hk shape m.spatial.walls m.heap zero _ _ _
      m.valid pos room,
    PolylogLocalProfile.central_work ok price extra hk shape m.spatial.walls m.heap zero _ _ _
      m.valid pos room⟩

private theorem window_polynomial {B t b : ℕ} (ht : t ≤ 20*(B+1)) (hb : b ≤ 20*(B+1)) :
    PolylogLocalProfile.total t b t B ≤ 10^16*(B+1)^8 := by
  let A := 20*(B+1)
  calc
    _ ≤ PolylogLocalProfile.total A A A B := by
      simp only [PolylogLocalProfile.total_eq,PolylogPrefixProfile.bound,PolylogPrefix.readBound]
      gcongr
    _ ≤ _ := by
      simp only [PolylogLocalProfile.total_eq,PolylogPrefixProfile.bound,PolylogPrefix.readBound,
        PolylogLocalProfile.sweepCap,PolylogLocalProfile.certCap,A]
      ring_nf
      omega

theorem priced_active_work {K : Kernels} (ok : Correct K) (price : Priced K)
    (hk : 64 ≤ parameter n) (m : ScheduledMemory n) (M : Controller.Memory n)
    (ready : Ready (parameter n) M) (hm : Tracks m M) (depth : totalDepth M ≤ horizon n) (q : Query n) :
    compareWork (window K (.stage (parameter n))) m q ≤ 10^20*(logCap n+1)^10 := by
  have hb := PolylogSchedule.capacity_bits (extra := extra) hk (le_refl (logCap n))
  change (binaryPoint n).size ≤ 5+(logCap n+1)*3 at hb
  have loc := window_polynomial (t := tableHeight n) (b := (binaryPoint n).size) (B := logCap n)
    (by unfold tableHeight; omega) (by omega)
  apply (compareWork_polynomial hk (window_bounded ok price hk) loc m M hm ready depth q).trans
  exact Nat.mul_le_mul_right _ (by decide)

/-- Word and bit-operation profile of the actual finite-window kernels,
shared-block writes and sparse mutations taken by this comparison. -/
abbrev activeWork (m : ScheduledMemory n) (q : Query n) : ℕ :=
  compareWork (window PolylogKernelProfile.kernels (.stage (parameter n))) m q

theorem active_work (hk : 64 ≤ parameter n) (m : ScheduledMemory n) (M : Controller.Memory n)
    (ready : Ready (parameter n) M) (hm : Tracks m M) (depth : totalDepth M ≤ horizon n) (q : Query n) :
    activeWork m q ≤ 10^20*(logCap n+1)^10 :=
  priced_active_work PolylogKernelProfile.correct PolylogKernelProfile.priced hk m M ready hm depth q

end SortingAdversary.Continuous.PolylogWordCompare
