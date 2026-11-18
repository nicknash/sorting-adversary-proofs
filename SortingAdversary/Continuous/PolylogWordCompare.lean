import SortingAdversary.Continuous.PolylogProfileCompare
import SortingAdversary.Continuous.PolylogMutationProfile
import SortingAdversary.Continuous.PolylogWordWriter

/-!
# Shared-dictionary, scalar, and local-kernel work per comparison

The repair discovery routine already includes its sparse-table traversals.
This profile adds the balanced dictionary paths for heap comparisons and
writes, the physical clamp comparisons for all affected walls, and both
types of local enclosure tests taken by the actual query.
-/
namespace SortingAdversary.Continuous.PolylogWordCompare

open PolylogCompare PolylogProfileCompare
open PolylogResources (tableHeight)
open PolylogAdversary (parameter extra)
open Controller (Ready Admissible totalDepth horizon)
open Optimal.Parameters (logCap)
variable {n : ℕ}
local notation "D" => binaryPoint n
local notation "k" => parameter n

/-- Physical costs of the prepared tests, at their concrete stored inputs. -/
structure Window (n : ℕ) where
  pair : ScheduledMemory n → Fin n → Fin n → ℕ
  threshold : ScheduledMemory n → Fin n → ℕ → ℕ
  central : ScheduledMemory n → Fin n → ℕ

def Window.Bounded (W : Window n) (K : ℕ) : Prop :=
  ∀ m M, Tracks m M → Admissible k M → totalDepth M ≤ depthLimit n →
    (∀ x y, W.pair m x y ≤ K) ∧ (∀ x c, W.threshold m x c ≤ K) ∧ ∀ x, W.central m x ≤ K

/-- Match the route returned by the two hierarchy cursors. A pair of
anchored children takes only a comparison of their stored block IDs. -/
def routeCost (W : Window n) (m : ScheduledMemory n) (q : Query n) : ℕ :=
  match (PolylogStorage.route m.spatial q).value with
  | .coordinates => W.pair m q.left q.right
  | .leftFree c => W.threshold m q.left c
  | .rightFree c => W.threshold m q.right c
  | .anchors i j => ((PolylogWordWork.compareTrace m.heap (D).size i j).run m.heap).work

def rates (W : Window n) : Charges n where
  test := routeCost W
  write m x test := (PolylogWordWriter.mint D m x test).work
  central := W.central
  refine := PolylogMutationProfile.refineCost k
  record := PolylogMutationProfile.recordCost k

/-- The original count covers routing, local sparse searches, loop control
and scalar operations. Each profiled operation is charged in addition,
which allows its ordinary scalar instructions to be charged twice. -/
def compareWork (W : Window n) (m : ScheduledMemory n) (q : Query n) :=
  (PolylogCompare.compare D k m q).work + compareCharges (rates W) m q

private def allowance (n K : ℕ) :=
  K + 60000000*(logCap n+1)^4 + (3*tableHeight n+1)*(3*(binaryPoint n).size+2)

private theorem heapFits (hk : 64 ≤ k) {m : ScheduledMemory n} {M : Controller.Memory n}
    (hm : Tracks m M) (depth : totalDepth M ≤ depthLimit n) :
    m.heap.next+PolylogResources.perMove (logCap n) (D).size < 2^tableHeight n :=
  (PolylogResources.indices_fit hm.sized (PolylogSchedule.capacity_bits (extra := extra) hk le_rfl)
    (depth.trans (depthLimit_table hk))).2

private theorem rates_bounded {W : Window n} {K : ℕ} (hk : 64 ≤ k) (hK : W.Bounded K) :
    Bounded (rates W) (allowance n K) (9*tableHeight n+1) := by
  have pos : 0 < tableHeight n := by unfold tableHeight; omega
  constructor
  · intro m M hm ready depth q
    obtain ⟨pair,threshold,_⟩ := hK m M hm ready.admissible depth
    change routeCost W m q ≤ _
    unfold routeCost allowance
    split
    · exact (pair ..).trans (by omega)
    · exact (threshold ..).trans (by omega)
    · exact (threshold ..).trans (by omega)
    · rename_i a b _
      have fit := (Nat.le_add_right ..).trans_lt (heapFits hk hm depth)
      have hw := PolylogWordWork.compare_dictionary m.heap m.valid pos fit (D).size a b
      rw [PolylogActive.lessAddr_work] at hw
      omega
  · intro m M hm ready depth x
    let v := writePrefix D m x
    have room := (prefix_growth D m x).trans_lt (heapFits hk hm depth)
    have mutation := PolylogMutationProfile.refineCost_le k m x v pos room
    have write := PolylogWordWriter.writePrefix_work hk hm depth x
    change (PolylogWordWriter.writePrefix D m x).work + PolylogMutationProfile.refineCost k m x v ≤
      allowance n K + (9*tableHeight n+1)*(move k m x v).work
    unfold allowance; omega
  · intro m M hm adm depth x
    obtain ⟨_,rep⟩ := hm.storage
    let a := (candidate D k m x).value
    let v := mint D m x a
    have eq := candidate_value extra rep hk adm (Nat.lt_size_self _) (binaryPoint_short n) x
    have room := (mint_growth D m x a).trans_lt (heapFits hk hm depth)
    have mutation := PolylogMutationProfile.refineCost_le k m x v pos room
    have write := PolylogWordWriter.mint_work hk hm depth adm x a eq
    have central := (hK m M hm adm depth).2.2 x
    have sub : (move k m x v).work ≤ (repairMove D k m x).work := by
      change _ ≤ (candidate D k m x).work + (move k m x v).work+1; omega
    have wm := mutation.trans (Nat.mul_le_mul_left _ sub)
    change W.central m x + (PolylogWordWriter.mint D m x a).work + PolylogMutationProfile.refineCost k m x v ≤ _
    unfold allowance; omega
  · intro m M hm _ depth q a
    exact PolylogMutationProfile.recordCost_le k m q a pos
      ((Nat.le_add_right ..).trans_lt (heapFits hk hm depth))

theorem compareWork_le {W : Window n} {K : ℕ} (hk : 64 ≤ k) (hK : W.Bounded K)
    (m : ScheduledMemory n) (M : Controller.Memory n) (hm : Tracks m M)
    (ready : Ready k M) (depth : totalDepth M ≤ horizon n) (q : Query n) :
    compareWork W m q ≤ (2^k+3)*(2*allowance n K) +
      (9*tableHeight n+2)*(20000000*(logCap n+1)^9) := by
  have prof := compareCharges_le (rates_bounded hk hK) hk m M hm ready depth q
  have base := PolylogCompareWork.active_query_polylog hk m M ready hm q
  have mu := Nat.mul_le_mul_left (9*tableHeight n+1) base
  unfold compareWork
  rw [show 9*tableHeight n+2 = (9*tableHeight n+1)+1 by omega, Nat.add_mul (9*tableHeight n+1) 1 _,one_mul]
  omega

/-- A polynomial bound for all expanded branches from a polynomial bound
for the concrete window routines. The extra power allows the longest batch
of repairs after recording an arc. -/
theorem compareWork_polynomial {W : Window n} {K C e : ℕ} (hk : 64 ≤ k) (hK : W.Bounded K)
    (localWork : K ≤ C*(logCap n+1)^e)
    (m : ScheduledMemory n) (M : Controller.Memory n) (hm : Tracks m M)
    (ready : Ready k M) (depth : totalDepth M ≤ horizon n) (q : Query n) :
    compareWork W m q ≤ (4000000000+8*C)*(logCap n+1)^(max 10 (e+1)) := by
  let L := logCap n+1
  have pos : 1 ≤ L := by dsimp [L]; omega
  have hH := PolylogSchedule.height_le (extra := extra) hk
  have path : 2^k ≤ ArbitraryLabels.pathHeight k := Nat.pow_le_pow_right (by decide) (Nat.le_succ k)
  have h₁ : 2^k+3 ≤ 4*L := by change ArbitraryLabels.pathHeight k ≤ logCap n at hH; dsimp [L]; omega
  have t : tableHeight n ≤ 19*L := by dsimp [L,tableHeight]; omega
  have b : (D).size ≤ 8*L := by
    have h := PolylogSchedule.capacity_bits (extra := extra) hk (le_refl (logCap n))
    change (D).size ≤ 5+L*3 at h; omega
  have tag : (3*tableHeight n+1)*(3*(D).size+2) ≤ (58*L)*(26*L) :=
    Nat.mul_le_mul (by omega) (by omega)
  have f : allowance n K ≤ C*L^e+60002000*L^4 := by
    have p₂ : L^2 ≤ L^4 := Nat.pow_le_pow_right pos (by decide)
    change K+60000000*L^4+_ ≤ _
    change K ≤ C*L^e at localWork
    have prices : (3*tableHeight n+1)*(3*(D).size+2) ≤ 1508*L^2 := tag.trans_eq (by ring)
    omega
  have f1 : 9*tableHeight n+2 ≤ 173*L := by omega
  apply (compareWork_le hk hK m M hm ready depth q).trans
  change _ ≤ (4000000000+8*C)*L^(max 10 (e+1))
  calc
    _ ≤ 4*L*(2*(C*L^e+60002000*L^4)) + 173*L*(20000000*L^9) :=
      Nat.add_le_add (Nat.mul_le_mul h₁ (Nat.mul_le_mul_left 2 f)) (Nat.mul_le_mul_right _ f1)
    _ = (8*C)*L^(e+1)+480016000*L^5+3460000000*L^10 := by rw [pow_succ L e]; ring
    _ ≤ (8*C)*L^(max 10 (e+1)) + 480016000*L^(max 10 (e+1)) + 3460000000*L^(max 10 (e+1)) := by
      gcongr
      · exact le_max_right ..
      · exact (show 5 ≤ 10 by decide).trans (le_max_left ..)
      · exact le_max_left ..
    _ ≤ _ := by ring_nf; omega

end SortingAdversary.Continuous.PolylogWordCompare
