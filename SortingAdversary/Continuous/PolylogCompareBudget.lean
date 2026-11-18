import SortingAdversary.Continuous.PolylogCompareWork
import SortingAdversary.Continuous.PolylogCompareSteps

/-!
# Reducing the stored comparison count to its logarithmic stage budget

The sparse work between local tests is bounded in terms of the table height,
the endpoint address height, and the path search admitted by the stage.
The coefficient of the cost of a local test counts the three selection trials
and the longest possible sequence of repairs.
-/

namespace SortingAdversary.Continuous.PolylogCompareWork

open PolylogCompare PolylogMutation PolylogRepair
open Optimal.Parameters (logCap)
open PolylogAdversary (extra parameter)
open PolylogResources (tableHeight)

private theorem wholeCost_poly {t b D k L : ℕ} (K : ℕ)
    (ht : t ≤ 20*(L+1)) (hb : b ≤ 20*(L+1)) (hg : Nat.log 2 (D-2) ≤ b)
    (hk : k ≤ L) (hp : (k+1)^ArbitraryLabels.pathHeight k ≤ L)
    (hr : repairBound k (ArbitraryLabels.pathHeight k) ≤ L) (hN : 2^k ≤ L) :
    wholeCost t b D L k K ≤ 200000*(L+1)^4+(L+3)*K := by
  let A := 20*(L+1)
  have ht' : t ≤ A := ht
  have hb' : b ≤ A := hb
  have hg' : Nat.log 2 (D-2) ≤ A := hg.trans hb
  have hc : coreCost t b k ≤ 5000*(L+1)^2 := by
    unfold coreCost coreBudget
    calc
      _ ≤ 2*(L*(13*A+(3*A+6)+12)+5*A+6)+2*L*(9*A+3*L+6)+26*A+8*L+24 := by gcongr
      _ ≤ _ := by dsimp [A]; ring_nf; omega
  have pr : prefixCost t b D ≤ 15000*(L+1)^2 := by
    unfold prefixCost PolylogRawAnchor.workBound
    calc
      _ ≤ 8*A+((A+1)*(24*A+20)+(48*A+24))+4 := by gcongr
      _ ≤ _ := by dsimp [A]; ring_nf; omega
  have mv : moveCost t b k ≤ 10000*(L+1)^2 := by
    unfold moveCost
    calc
      _ ≤ 5000*(L+1)^2+36*A+22 := by gcongr
      _ ≤ _ := by dsimp [A]; ring_nf; omega
  have recCost : recordCost t b k ≤ 15000*(L+1)^2 := by
    unfold recordCost
    calc
      _ ≤ 5000*(L+1)^2+2*(A*(8*A+9)+16*A)+36 := by gcongr
      _ ≤ _ := by dsimp [A]; ring_nf; omega
  have ck : checkCost t b K ≤ 5000*(L+1)^2+K := by
    unfold checkCost
    have hm : max K (3*b+2) ≤ K+(3*A+2) := by apply max_le <;> omega
    calc
      _ ≤ A*(8*A+9)+16*A+(K+(3*A+2))+20 := by gcongr
      _ ≤ _ := by dsimp [A]; ring_nf; omega
  have sel : selectUnit t b D k K ≤ 30000*(L+1)^2+K+3 := by
    unfold selectUnit
    omega
  have wr : writeCost t b D L ≤ 15000*(L+1)^3 := by
    unfold writeCost
    apply max_le
    · apply pr.trans; ring_nf; omega
    · calc
        _ ≤ 1+(L+1)*((A+1)^2+10*A+6)+L+4 := by gcongr
        _ ≤ _ := by dsimp [A]; ring_nf; omega
  have rep : repairUnit t b D L k K ≤ K+26000*(L+1)^3 := by
    unfold repairUnit
    apply (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left wr K) mv) 3).trans
    ring_nf; omega
  unfold wholeCost
  calc
    _ ≤ 3*(30000*(L+1)^2+K+3)+1 + 15000*(L+1)^2 +
        ((L+6*L+1)*(8*A+L+8)+2) + (L*(K+26000*(L+1)^3)+1)+4 := by gcongr
    _ ≤ _ := by dsimp [A]; ring_nf; omega

/-- The only variable charge in this bound is the measured preparation and
evaluation of one of the three concrete finite-window tests. -/
theorem scheduled_compare_work {n K : ℕ} (hk : 64 ≤ parameter n)
    (m : ScheduledMemory n) (M : Controller.Memory n) (ready : Controller.Ready (parameter n) M)
    (hm : Tracks m M) (q : Query n)
    (hc : Tests n (tableHeight n) (binaryPoint n).size (binaryPoint n) (parameter n) K) :
    (PolylogCompare.compare (binaryPoint n) (parameter n) m q).work ≤
      200000*(logCap n+1)^4+(logCap n+3)*K := by
  obtain ⟨_,rep⟩ := hm.storage
  let L := logCap n
  let k := parameter n
  have sh : Shape m.spatial.graph (k-1) :=
    ⟨M.tree.system.edge,rep.spatial.graph,ready.noLoop,fun x => by have := ready.degree x; omega⟩
  apply (compare_work hc (PolylogResources.label_fits _) (by omega) m q sh).trans
  have r := (PolylogSchedule.admitted_costs (extra := extra) hk).2
  change repairBound k (ArbitraryLabels.pathHeight k) ≤ L at r
  have hH := PolylogSchedule.height_le (extra := extra) hk
  have hs := PolylogSchedule.capacity_bits (extra := extra) hk (le_refl (logCap n))
  change (binaryPoint n).size ≤ 5+(L+1)*3 at hs
  have kn : k ≤ 2^k := Nat.lt_two_pow_self.le
  have pow : 2^k ≤ ArbitraryLabels.pathHeight k := Nat.pow_le_pow_right (by decide) (Nat.le_succ k)
  change ArbitraryLabels.pathHeight k ≤ L at hH
  refine wholeCost_poly K (by dsimp [tableHeight,L]; omega) (by omega) ?_
    (kn.trans (pow.trans hH)) ?_ r (pow.trans hH)
  · apply (Nat.log_mono_right (Nat.sub_le (binaryPoint n) 2)).trans
    by_cases z : binaryPoint n = 0
    · simp [z]
    · exact (Nat.log_lt_of_lt_pow z (Nat.lt_size_self _)).le
  · change (k+1)^ArbitraryLabels.pathHeight k ≤ L
    unfold repairBound at r
    omega

end SortingAdversary.Continuous.PolylogCompareWork
