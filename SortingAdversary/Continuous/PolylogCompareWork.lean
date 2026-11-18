import SortingAdversary.Continuous.PolylogCompare
import SortingAdversary.Continuous.PolylogCompareShape
import SortingAdversary.Continuous.PolylogNeighborhoodBudget

/-!
# Cost of the active stored comparison loop

A strict degree cap at the beginning of the query suffices for all costs
inside it: selection only deletes incident rows, the answer can add one arc,
and every subsequent repair deletes incident rows. No bounds on intermediate
transcripts or calls are assumed.
-/

namespace SortingAdversary.Continuous.PolylogCompareWork

open PolylogCompare PolylogMutation PolylogRepair Optimal
open Optimal.PrimitiveWork (Result)
variable {n t b : ℕ}

/-- The three concrete local tests consume the same count allowance. -/
def Tests (n t b D k K : ℕ) : Prop :=
  ∀ m : Memory n t b, Shape m.spatial.graph k →
    (∀ x y, (PolylogPrepared.pair m.spatial.graph m.spatial.walls m.heap
      (fun h => m.cache.lookup h false) b D k x y).work ≤ K) ∧
    (∀ x c, (PolylogPrepared.threshold m.spatial.graph m.spatial.walls m.heap
      (fun h => m.cache.lookup h false) b D k x c).work ≤ K) ∧
    ∀ x, (candidate D k m x).work ≤ K

def prefixCost (t b D : ℕ) := 8*t + PolylogRawAnchor.workBound b (D-2) + 4
def writeCost (t b D e : ℕ) := max (prefixCost t b D) (1+(e+1)*((b+1)^2+10*b+6)+e+4)
def coreCost (t b k : ℕ) := coreBudget t k (ArbitraryLabels.pathHeight k) (3*b+6)
def recordCost (t b k : ℕ) := coreCost t b k + 2*(t*(8*t+9)+16*t)+36
def moveCost (t b k : ℕ) := coreCost t b k + 36*t+22
def checkCost (t b K : ℕ) := t*(8*t+9)+16*t+max K (3*b+2)+20
def selectUnit (t b D k K : ℕ) := checkCost t b K + prefixCost t b D + moveCost t b k + 3
def repairUnit (t b D e k K : ℕ) := K + writeCost t b D e + moveCost t b k + 3

theorem prefix_work (D : ℕ) (m : Memory n t b) (x : Fin n) :
    (writePrefix D m x).work ≤ prefixCost t b D := by
  have h := PolylogRawAnchor.work_bound D (D-2) m.valid m.typed m.cache (le_refl b)
    (m.spatial.walls.lower.get x.val).value (m.spatial.walls.upper.get x.val).value
  simp only [writePrefix,PolylogRouting.Table.get_work,prefixCost]
  omega

theorem mint_work (D : ℕ) (m : Memory n t b) (x : Fin n) (q : Option ℚ) :
    (mint D m x q).work ≤ writeCost t b D (Parameters.logCap n) := by
  cases q with
  | none => exact (prefix_work D m x).trans (le_max_left ..)
  | some q =>
    let e := Parameters.logCap n
    have hw := PolylogEmbed.embedAddr_work D e (PolylogAnchorWrite.numerator q e) m.valid m.cache (le_refl b)
    change _ + e + 4 ≤ _
    exact (Nat.add_le_add_right (Nat.add_le_add_right hw e) 4).trans (le_max_right ..)

theorem move_work (k : ℕ) (m : Memory n t b) (x : Fin n) (v : WriteResult m)
    (sh : Shape m.spatial.graph k) :
    (move k m x v).work ≤ v.work + moveCost t b k := by
  let m' := m.withHeap v.out.heap v.out.valid v.out.growth
  have h := refineState_work m'.less (3*b+6) (fun i j => PolylogAddressOrder.work m'.heap b i j) m'.spatial k m'.zero m'.one
    sh.bounded x v.out.addr
  change v.work + (refineState m'.less m'.spatial k m'.zero m'.one x v.out.addr).work + 2 ≤
    v.work + (coreBudget t k _ _ + 36*t+22)
  omega

theorem move_shape {k d : ℕ} (m : Memory n t b) (x : Fin n) (v : WriteResult m)
    (sh : Shape m.spatial.graph d) (small : d ≤ k) (cap : n ≤ 2^t) :
    Shape (move k m x v).value.spatial.graph d :=
  shape_refine sh small cap _ _ _ _ _

theorem record_work (k : ℕ) (m : Memory n t b) (q : Query n) (a : Answer)
    (sh : Shape m.spatial.graph k) : (record k m q a).work ≤ recordCost t b k := by
  have h := recordState_work m.less (3*b+6) (fun i j => PolylogAddressOrder.work m.heap b i j)
    m.spatial k m.zero m.one sh.bounded q a
  have r := PolylogStorage.route_work m.spatial q
  unfold record recordCost coreCost
  dsimp only
  omega

theorem check_work {D k K : ℕ} (cost : Tests n t b D k K) (m : Memory n t b)
    (q : Query n) (sh : Shape m.spatial.graph k) : (check D k m q).work ≤ checkCost t b K :=
  PolylogActive.attempt_work _ _ _ _ _ _ K (cost m sh).1 (cost m sh).2.1

theorem select_bounds {D k d K : ℕ} (cost : Tests n t b D k K)
    (cap : n ≤ 2^t) (small : d ≤ k) (q : Query n) (fuel : ℕ) (m : Memory n t b)
    (sh : Shape m.spatial.graph d) :
    (select D k q fuel m).work ≤ fuel*selectUnit t b D k K+1 ∧
    ∀ u a, (select D k q fuel m).value = some (u,a) → Shape u.spatial.graph d := by
  induction fuel generalizing m with
  | zero => simp [select]
  | succ f ih =>
    have ck := check_work cost m q (sh.mono small)
    cases dec : (check D k m q).value with
    | answer a =>
      simp only [select,dec,Option.some.injEq,Prod.mk.injEq,Nat.succ_mul]
      constructor
      · unfold selectUnit; omega
      · rintro u y ⟨rfl,rfl⟩; exact sh
    | refine x =>
      let v := writePrefix D m x
      let r := move k m x v
      have shape : Shape r.value.spatial.graph d := move_shape m x v sh small cap
      obtain ⟨tail,final⟩ := ih r.value shape
      have pm := prefix_work D m x
      have mv := move_work k m x v (sh.mono small)
      change r.work ≤ (writePrefix D m x).work + moveCost t b k at mv
      simp only [select,dec,Nat.succ_mul]
      refine ⟨?_,final⟩
      change (check D k m q).work + r.work + (select D k q f r.value).work + 3 ≤ _
      unfold selectUnit at *
      omega

theorem repairList_work {D k K : ℕ} (cost : Tests n t b D k K) (cap : n ≤ 2^t)
    (xs : List (Fin n)) (m : Memory n t b) (sh : Shape m.spatial.graph k) :
    (repairList D k xs m).work ≤ xs.length*repairUnit t b D (Parameters.logCap n) k K+1 := by
  induction xs generalizing m with
  | nil => simp [repairList]
  | cons x xs ih =>
    let a := candidate D k m x
    let v := mint D m x a.value
    let r := repairMove D k m x
    have sh' : Shape r.value.spatial.graph k := move_shape m x v sh le_rfl cap
    have tail := ih r.value sh'
    have amax : a.work ≤ K := (cost m sh).2.2 x
    have vm : v.work ≤ _ := mint_work D m x a.value
    have mv := move_work k m x v sh
    change (move k m x v).work ≤ v.work + moveCost t b k at mv
    have step : r.work ≤ K + writeCost t b D (Parameters.logCap n) + moveCost t b k + 1 := by
      change a.work+(PolylogCompare.move k m x v).work+1 ≤ _
      omega
    change r.work+(repairList D k xs r.value).work+2 ≤ _
    simp only [List.length_cons,Nat.succ_mul]
    unfold repairUnit at *
    omega

def wholeCost (t b D e k K : ℕ) :=
  3*selectUnit t b D k K+1 + recordCost t b k +
    ((repairBound k (ArbitraryLabels.pathHeight k)+6*k+1)*(8*t+k+8)+2) +
    (2^k*repairUnit t b D e k K+1) + 4

theorem compare_work {D k K : ℕ} (cost : Tests n t b D k K) (cap : n ≤ 2^t)
    (hk : 0 < k) (m : Memory n t b) (q : Query n) (sh : Shape m.spatial.graph (k-1)) :
    (PolylogCompare.compare D k m q).work ≤ wholeCost t b D (Parameters.logCap n) k K := by
  obtain ⟨sw,post⟩ := select_bounds cost cap (Nat.sub_le k 1) q 3 m sh
  cases sel : (select D k q 3 m).value with
  | none =>
    simp only [PolylogCompare.compare,sel,wholeCost]
    omega
  | some pair =>
    obtain ⟨u,a⟩ := pair
    have us := post u a sel
    have rw' := record_work k u q a (us.mono (Nat.sub_le k 1))
    let r := record k u q a
    have rs : Shape r.value.1.spatial.graph k := by
      change Shape (recordState u.less u.spatial k u.zero u.one q a).value.graph k
      simpa only [Nat.sub_add_cancel hk] using shape_record (k := k) us cap u.less u.zero u.one q a
    have rb := choose_bounds r.value.1.spatial.graph k r.value.2 rs
    let p := choose r.value.1.spatial.graph k r.value.2
    have tr := repairList_work cost cap p.value r.value.1 rs
    have tr' := tr.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ rb.2) 1)
    simp only [PolylogCompare.compare,sel]
    change _ + r.work+p.work+_+4 ≤ _
    unfold wholeCost
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add sw rw') rb.1) tr') _

end SortingAdversary.Continuous.PolylogCompareWork
