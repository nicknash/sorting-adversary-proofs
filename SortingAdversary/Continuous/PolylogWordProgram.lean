import SortingAdversary.Continuous.PolylogWordBudget
import SortingAdversary.Continuous.PolylogCached

/-!
# A single stored comparison with word-level charges

The selector and reserved repair loop call the priced kernels, heap writers
and graph mutations directly. Their counters accumulate along the selected
branches. All stage parameters are read from the supplied initialization
record. Correctness is independent of the arithmetic tariff of the kernels.
-/

namespace SortingAdversary.Continuous.PolylogWordProgram

open PolylogLocalProfile (Kernels Correct)
open PolylogPrepared (Params)
open PolylogCompare (Memory WriteResult ScheduledMemory binaryPoint)
open PolylogActive (Decision decideTest)
open Optimal.PrimitiveWork (Result)
variable {n t b : ℕ} {K : Kernels}

private abbrev pair (K : Kernels) (D : ℕ) (P : Params) (m : Memory n t b) :=
  PolylogLocalProfile.pair K m.spatial.graph m.spatial.walls m.heap (fun h => m.cache.lookup h false) b D P

private abbrev threshold (K : Kernels) (D : ℕ) (P : Params) (m : Memory n t b) :=
  PolylogLocalProfile.threshold K m.spatial.graph m.spatial.walls m.heap (fun h => m.cache.lookup h false) b D P

private abbrev central (K : Kernels) (D : ℕ) (P : Params) (m : Memory n t b) :=
  PolylogLocalProfile.central K m.spatial.graph m.spatial.walls m.heap (fun h => m.cache.lookup h false) b D P

private def branch (K : Kernels) (D : ℕ) (P : Params) (m : Memory n t b) (q : Query n) :
    TreeState.Routing ℕ → Result (Decision n)
  | .coordinates =>
    let a := pair K D P m q.left q.right
    ⟨decideTest (min q.left q.right) false a.value, a.work+3⟩
  | .leftFree i =>
    let a := threshold K D P m q.left i
    ⟨decideTest q.left false a.value, a.work+2⟩
  | .rightFree i =>
    let a := threshold K D P m q.right i
    ⟨decideTest q.right true a.value, a.work+3⟩
  | .anchors i j =>
    let c := m.heap.lessAddr b i j
    let lookups := (PolylogWordWork.compareTrace m.heap b i j).run m.heap
    ⟨.answer (if c.1 then .less else .greater), c.2+2+lookups.work⟩

def check (K : Kernels) (D : ℕ) (P : Params) (m : Memory n t b) (q : Query n) : Result (Decision n) :=
  let r := PolylogStorage.route m.spatial q
  let a := branch K D P m q r.value
  ⟨a.value,r.work+a.work+1⟩

def select (K : Kernels) (D : ℕ) (P : Params) (q : Query n) :
    ℕ → Memory n t b → Result (Option (Memory n t b × Answer))
  | 0, _ => ⟨none,1⟩
  | fuel+1, m =>
    let a := check K D P m q
    match a.value with
    | .answer z => ⟨some (m,z),a.work+2⟩
    | .refine x =>
      let w := PolylogWordWriter.writePrefix D m x
      let r := PolylogMutationProfile.refine P.k m x w
      let next := select K D P q fuel r.value
      ⟨next.value,a.work+w.work+r.work+next.work+3⟩

def repairMove (K : Kernels) (D : ℕ) (P : Params) (m : Memory n t b) (x : Fin n) :
    Result (Memory n t b) :=
  let a := central K D P m x
  let w := PolylogWordWriter.mint D m x a.value
  let r := PolylogMutationProfile.refine P.k m x w
  ⟨r.value,a.work+w.work+r.work+1⟩

def repairList (K : Kernels) (D : ℕ) (P : Params) :
    List (Fin n) → Memory n t b → Result (Memory n t b)
  | [], m => ⟨m,1⟩
  | x::xs, m =>
    let r := repairMove K D P m x
    let next := repairList K D P xs r.value
    ⟨next.value,r.work+next.work+2⟩

def compare (K : Kernels) (D : ℕ) (P : Params) (m : Memory n t b) (q : Query n) :
    Result (Option (Memory n t b × Answer)) :=
  let s := select K D P q 3 m
  match s.value with
  | none => ⟨none,s.work+1⟩
  | some (u,a) =>
    let r := PolylogMutationProfile.record P.k u q a
    let path := PolylogRepair.choose r.value.1.spatial.graph P.k r.value.2
    let next := repairList K D P path.value r.value.1
    ⟨some (next.value,a),s.work+r.work+path.work+next.work+4⟩

private abbrev oldBranch (D : ℕ) (P : Params) (m : Memory n t b) (q : Query n) :=
  PolylogActive.branch m.heap b
    (PolylogPrepared.pairWith m.spatial.graph m.spatial.walls m.heap (fun h => m.cache.lookup h false) b D P)
    (PolylogPrepared.thresholdWith m.spatial.graph m.spatial.walls m.heap (fun h => m.cache.lookup h false) b D P) q

private theorem cached_check (D : ℕ) (P : Params) (m : Memory n t b) (q : Query n) :
    PolylogCached.check D P m q =
      let r := PolylogStorage.route m.spatial q
      let a := oldBranch D P m q r.value
      ⟨a.value,r.work+a.work+1⟩ := by
  simp only [PolylogCached.check,PolylogStorage.route,PolylogActive.attempt,oldBranch]
  congr 1
  omega

private theorem refine_congr {m : Memory n t b} (k : ℕ) (x : Fin n) {w v : WriteResult m}
    (hw : w.out = v.out) : PolylogMutationProfile.refine k m x w = PolylogMutationProfile.refine k m x v := by
  cases w; cases v; cases hw; rfl

theorem check_value (ok : Correct K) (D : ℕ) (P : Params) (m : Memory n t b) (q : Query n) :
    (check K D P m q).value = (PolylogCached.check D P m q).value := by
  rw [cached_check]
  simp only [check]
  cases hr : (PolylogStorage.route m.spatial q).value <;> simp only [branch,oldBranch,
    PolylogActive.branch,pair,threshold,PolylogLocalProfile.pair_value ok,PolylogLocalProfile.threshold_value ok]

private theorem central_value (ok : Correct K) (D : ℕ) (P : Params) (m : Memory n t b) (x : Fin n) :
    (central K D P m x).value = (PolylogCached.candidate D P m x).value :=
  PolylogLocalProfile.central_value ok ..

private theorem select_value (ok : Correct K) (D : ℕ) (P : Params) (q : Query n) (f : ℕ) (m : Memory n t b) :
    (select K D P q f m).value = (PolylogCached.select D P q f m).value := by
  induction f generalizing m with
  | zero => rfl
  | succ f ih =>
    simp only [select,PolylogCached.select,check_value ok]
    cases hh : (PolylogCached.check D P m q).value with
    | answer => rfl
    | refine x => simp only [refine_congr P.k x (PolylogWordWriter.writePrefix_out D m x),
        PolylogMutationProfile.refine_value, ih]

private theorem repairMove_value (ok : Correct K) (D : ℕ) (P : Params) (m : Memory n t b) (x : Fin n) :
    (repairMove K D P m x).value = (PolylogCached.repairMove D P m x).value := by
  simp only [repairMove, PolylogCached.repairMove, central_value ok, refine_congr P.k x (PolylogWordWriter.mint_out ..),
    PolylogMutationProfile.refine_value]

private theorem repairList_value (ok : Correct K) (D : ℕ) (P : Params) (xs : List (Fin n))
    (m : Memory n t b) : (repairList K D P xs m).value = (PolylogCached.repairList D P xs m).value := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih => simp only [repairList, PolylogCached.repairList, repairMove_value ok, ih]

theorem compare_value (ok : Correct K) (D : ℕ) (P : Params) (m : Memory n t b) (q : Query n) :
    (compare K D P m q).value = (PolylogCached.compare D P m q).value := by
  simp only [compare,PolylogCached.compare,select_value ok]
  cases hs : (PolylogCached.select D P q 3 m).value with
  | none => rfl
  | some z =>
    obtain ⟨u,a⟩ := z
    simp only [PolylogMutationProfile.record_value,repairList_value ok]

section Work

open PolylogWordCompare (window rates routeCost)
open PolylogProfileCompare (selectCharges repairCharges compareCharges)
local notation "D" => binaryPoint n
local notation "k" => PolylogAdversary.parameter n
local notation "P" => (Params.stage k)
local notation "W" => (window (n := n) K P)

private theorem check_work (m : ScheduledMemory n) (q : Query n) :
    (check K D P m q).work ≤ (PolylogCompare.check D k m q).work + routeCost W m q := by
  rw [← PolylogCached.check_eq, cached_check]
  let r := PolylogStorage.route m.spatial q
  change r.work + (branch K D P m q r.value).work + 1 ≤
    r.work + (oldBranch D P m q r.value).work + 1 + _
  unfold routeCost
  cases r.value <;>
    simp only [branch,oldBranch,PolylogActive.branch,window,pair,threshold] <;> omega

private theorem select_work (ok : Correct K) (q : Query n) (f : ℕ) (m : ScheduledMemory n) :
    (select K D P q f m).work ≤ (PolylogCompare.select D k q f m).work + selectCharges (rates W) q f m := by
  induction f generalizing m with
  | zero => exact le_rfl
  | succ f ih =>
    have hc := check_work (K := K) m q
    have cv : (check K D P m q).value = (PolylogCompare.check D k m q).value :=
      (check_value ok D P m q).trans (congrArg Result.value (PolylogCached.check_eq D k m q))
    cases hz : (PolylogCompare.check D k m q).value with
    | answer a =>
      simp only [select,PolylogCompare.select,selectCharges,cv,hz,rates]
      omega
    | refine x =>
      let w := PolylogCompare.writePrefix D m x
      let next := (PolylogCompare.move k m x w).value
      have tail := ih next
      have hchange := refine_congr k x (PolylogWordWriter.writePrefix_out D m x)
      have sr : (Params.stage k).k = k := rfl
      simp only [select,PolylogCompare.select,selectCharges,cv,hz,sr,hchange,PolylogMutationProfile.refine_value,rates]
      change (check K D P m q).work + (PolylogWordWriter.writePrefix D m x).work +
        PolylogMutationProfile.refineCost k m x w + (select K D P q f next).work + 3 ≤
        (PolylogCompare.check D k m q).work + (PolylogCompare.move k m x w).work +
        (PolylogCompare.select D k q f next).work + 3 +
        (routeCost W m q + (PolylogWordWriter.writePrefix D m x).work +
          PolylogMutationProfile.refineCost k m x w + selectCharges (rates W) q f next)
      omega

private theorem repairList_work (ok : Correct K) (xs : List (Fin n)) (m : ScheduledMemory n) :
    (repairList K D P xs m).work ≤ (PolylogCompare.repairList D k xs m).work + repairCharges (rates W) xs m := by
  induction xs generalizing m with
  | nil => exact le_rfl
  | cons x xs ih =>
    let a := (PolylogCompare.candidate D k m x).value
    let w := PolylogCompare.mint D m x a
    let next := (PolylogCompare.repairMove D k m x).value
    have tail := ih next
    have eq : (repairMove K D P m x).value = next := (repairMove_value ok D P m x).trans
      (congrArg Result.value (PolylogCached.repairMove_eq D k m x))
    have cv : (central K D P m x).value = a := central_value ok D P m x
    have hchange := refine_congr k x (PolylogWordWriter.mint_out D m x a)
    have sr : (Params.stage k).k = k := rfl
    simp only [repairList,PolylogCompare.repairList,repairCharges,eq]
    have lead : (repairMove K D P m x).work =
        (W).central m x + (PolylogWordWriter.mint D m x a).work + PolylogMutationProfile.refineCost k m x w + 1 := by
      simp only [repairMove,cv,sr,hchange]; rfl
    rw [lead]
    change _ ≤ (PolylogCompare.repairMove D k m x).work + (PolylogCompare.repairList D k xs next).work +
      2 + ((W).central m x + (PolylogWordWriter.mint D m x a).work + PolylogMutationProfile.refineCost k m x w +
        repairCharges (rates W) xs next)
    have one : 1 ≤ (PolylogCompare.repairMove D k m x).work := by dsimp [PolylogCompare.repairMove]; omega
    omega

theorem compare_work (ok : Correct K) (m : ScheduledMemory n) (q : Query n) :
    (compare K D P m q).work ≤ PolylogWordCompare.compareWork W m q := by
  have hsel := select_work ok q 3 m
  have sv := (select_value ok D P q 3 m).trans (congrArg Result.value (PolylogCached.select_eq D k q 3 m))
  have sr : (Params.stage k).k = k := rfl
  cases hs : (PolylogCompare.select D k q 3 m).value with
  | none =>
    simp only [compare,PolylogWordCompare.compareWork,PolylogCompare.compare,compareCharges,sv,hs]; omega
  | some z =>
    obtain ⟨u,a⟩ := z
    let r := (PolylogCompare.record k u q a).value
    let path := PolylogRepair.choose r.1.spatial.graph k r.2
    have hrp := repairList_work ok path.value r.1
    simp only [compare,PolylogWordCompare.compareWork,PolylogCompare.compare,compareCharges,sv,hs,sr,
      PolylogMutationProfile.record_value,rates]
    change (select K D P q 3 m).work + PolylogMutationProfile.recordCost k u q a + path.work +
      (repairList K D P path.value r.1).work + 4 ≤
      (PolylogCompare.select D k q 3 m).work + (PolylogCompare.record k u q a).work + path.work +
      (PolylogCompare.repairList D k path.value r.1).work + 4 +
      (selectCharges (rates W) q 3 m + PolylogMutationProfile.recordCost k u q a + repairCharges (rates W) path.value r.1)
    omega

end Work

end SortingAdversary.Continuous.PolylogWordProgram
