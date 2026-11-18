import SortingAdversary.Continuous.PolylogGraph
import SortingAdversary.Continuous.NeighborhoodWork
import SortingAdversary.Continuous.PolylogEnclosure

/-!
# Constructing the retained graph from sparse rows

The input query is a list of at most two ambient labels. Traversal reads
undirected adjacency rows and may visit a vertex more than once. Only the
visited labels are sorted and indexed. The dense matrix used by the finite
digit sweeps is materialized only on this small set.
-/

namespace SortingAdversary.Continuous.PolylogNeighborhood

open FiniteAveraging OrderRegion InducedEnclosure EnclosureWork
open Optimal Optimal.GraphBalls PrimitiveWork
variable {n m : ℕ}

def walk (adj : Fin n → List (Fin n)) (r : ℕ) (roots : List (Fin n)) : Result (List (Fin n)) :=
  flatMap (fun x => let entry := PolylogGraph.emit adj r x ([],0); ⟨entry.1,entry.2⟩) roots

theorem walk_value (adj : Fin n → List (Fin n)) (r : ℕ) (roots : List (Fin n)) :
    (walk adj r roots).value = roots.flatMap (PolylogGraph.visit adj r) := by
  simp only [walk, flatMap_value, (PolylogGraph.emit_spec ..).1, List.append_nil]

theorem walk_mem (D : System (Fin n) ℚ) (adj : Fin n → List (Fin n))
    (ha : ∀ x y, y ∈ adj x ↔ y ∈ neighbors D.edge x) (r : ℕ) (roots : List (Fin n)) (x : Fin n) :
    x ∈ (walk adj r roots).value ↔ x ∈ retained D roots.toFinset r := by
  simp only [walk_value, List.mem_flatMap, retained, Finset.mem_biUnion, List.mem_toFinset,
    PolylogGraph.visit_iff_mem_ball D.edge adj ha]

theorem walk_length (adj : Fin n → List (Fin n)) (d : ℕ) (hd : ∀ x, (adj x).length ≤ d)
    (r : ℕ) (roots : List (Fin n)) : (walk adj r roots).value.length ≤ roots.length*(d+1)^r := by
  rw [walk_value]
  induction roots with
  | nil => simp
  | cons x xs ih =>
    simpa only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul,Nat.add_comm]
      using Nat.add_le_add (PolylogGraph.visit_length_le adj d hd r x) ih

theorem walk_work (adj : Fin n → List (Fin n)) (d : ℕ) (hd : ∀ x, (adj x).length ≤ d)
    (r : ℕ) (roots : List (Fin n)) :
    (walk adj r roots).work ≤ roots.length*(4*(d+1)^r+2)+1 := by
  let f := fun x => let a := PolylogGraph.emit adj r x ([],0); (⟨a.1,a.2⟩ : Result (List (Fin n)))
  have vl x : (f x).value.length ≤ (d+1)^r := by
    simpa only [f,(PolylogGraph.emit_spec ..).1,List.append_nil] using PolylogGraph.visit_length_le adj d hd r x
  have h := flatMap_work f roots _ _ (fun x _ => PolylogGraph.emit_work_le adj d hd r x) (fun x _ => vl x)
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1)

def unique {α : Type*} [DecidableEq α] : List α → Result (List α)
  | [] => ⟨[],1⟩
  | x :: xs =>
    let t := unique xs
    let found := PrimitiveWork.any (fun y => ⟨decide (x=y),1⟩) t.value
    ⟨if found.value then t.value else x::t.value, t.work+found.work+2⟩

private theorem unique_spec {α : Type*} [DecidableEq α] (xs : List α) :
    ((unique xs).value.Nodup ∧ (∀ x, x ∈ (unique xs).value ↔ x ∈ xs)) ∧
      (unique xs).value.length ≤ xs.length := by
  induction xs with
  | nil => simp [unique]
  | cons x xs ih =>
    simp only [unique,PrimitiveWork.any_value]
    by_cases h : x ∈ (unique xs).value
    · have hb : (unique xs).value.any (fun y => decide (x=y)) = true :=
        List.any_eq_true.mpr ⟨x,h,by simp⟩
      simp only [hb,if_true]
      refine ⟨⟨ih.1.1,fun y => ?_⟩,by have := ih.2; simp; omega⟩
      have hx := (ih.1.2 x).mp h
      simp only [ih.1.2, List.mem_cons]
      grind
    · have hb : (unique xs).value.any (fun y => decide (x=y)) = false := by
        apply Bool.eq_false_iff.mpr
        intro e
        obtain ⟨y,hy,he⟩ := List.any_eq_true.mp e
        exact h ((of_decide_eq_true he) ▸ hy)
      simp only [hb,Bool.false_eq_true,if_false,List.nodup_cons,List.mem_cons,List.length_cons]
      exact ⟨⟨⟨h,ih.1.1⟩,fun y => or_congr Iff.rfl (ih.1.2 y)⟩,Nat.succ_le_succ ih.2⟩

private theorem unique_work {α : Type*} [DecidableEq α] (xs : List α) :
    (unique xs).work ≤ 8*(xs.length+1)^2 := by
  induction xs with
  | nil => simp [unique]
  | cons x xs ih =>
    have h := PrimitiveWork.any_work_le (fun y : α => (⟨decide (x=y),1⟩ : Result Bool))
      (unique xs).value 1 (fun _ _ => le_rfl)
    have hl := (unique_spec xs).2
    simp only [unique, List.length_cons]
    nlinarith

def sortedLabels (adj : Fin n → List (Fin n)) (r : ℕ) (roots : List (Fin n)) : Result (List (Fin n)) :=
  let visited := walk adj r roots
  let distinct := unique visited.value
  let ordered := HubSortWork.sort (fun x y => ⟨decide (x≤y),1⟩) distinct.value
  ⟨ordered.value,visited.work+distinct.work+ordered.work⟩

theorem sortedLabels_value (D : System (Fin n) ℚ) (adj : Fin n → List (Fin n))
    (ha : ∀ x y, y ∈ adj x ↔ y ∈ neighbors D.edge x) (r : ℕ) (roots : List (Fin n)) :
    (sortedLabels adj r roots).value = (retained D roots.toFinset r).sort (· ≤ ·) := by
  let xs := (walk adj r roots).value
  let ys := (unique xs).value
  have perm := List.perm_insertionSort (· ≤ ·) ys
  have nodup := perm.nodup_iff.mpr (unique_spec xs).1.1
  change (HubSortWork.sort _ ys).value = _
  simp only [HubSortWork.sort_value,decide_eq_true_eq]
  apply List.SortedLT.eq_of_mem_iff
  · exact (List.sortedLE_insertionSort (l := ys)).sortedLT_of_nodup nodup
  · exact (retained D roots.toFinset r).sortedLT_sort
  · intro x
    rw [perm.mem_iff, (unique_spec xs).1.2, Finset.mem_sort]
    exact walk_mem D adj ha r roots x

theorem sortedLabels_work (adj : Fin n → List (Fin n)) (d : ℕ) (hd : ∀ x, (adj x).length ≤ d)
    (r : ℕ) (roots : List (Fin n)) :
    (sortedLabels adj r roots).work ≤ roots.length*(4*(d+1)^r+2)+1 +
      13*(roots.length*(d+1)^r+1)^2 := by
  let xs := (walk adj r roots).value
  have hw := walk_work adj d hd r roots
  have hl := walk_length adj d hd r roots
  have hu := unique_work xs
  have hn := (unique_spec xs).2
  have hs := HubSortWork.sort_work_le (fun x y : Fin n => (⟨decide (x≤y),1⟩ : Result Bool))
    (unique xs).value 1 (fun _ _ => le_rfl)
  change xs.length ≤ _ at hl
  have h1 : (xs.length+1)^2 ≤ (roots.length*(d+1)^r+1)^2 := by gcongr
  have h2 : ((unique xs).value.length+1)^2 ≤ (roots.length*(d+1)^r+1)^2 := by gcongr; omega
  change _ + (unique xs).work + _ ≤ _
  dsimp only [xs] at *
  omega


/-- Numbered rows provide constant-size label handles. Wall reads can be a
pair of short-grid prefix reads supplied by the dyadic storage layer. -/
structure Reads (n : ℕ) where
  lower : Fin n → Result ℚ
  upper : Fin n → Result ℚ
  outgoing : Fin n → List (Fin n)

def Reads.system (P : Reads n) : System (Fin n) ℚ :=
  ⟨fun x => (P.lower x).value, fun x => (P.upper x).value, fun x y => decide (y ∈ P.outgoing x)⟩

def Reads.gather (P : Reads n) (v : Vector (Fin n) m) : Result (StoredSystem m) :=
  let lo := PrimitiveWork.vector fun x => P.lower v[x]
  let hi := PrimitiveWork.vector fun x => P.upper v[x]
  let edges := PrimitiveWork.vector fun x : Fin m => PrimitiveWork.vector fun y : Fin m =>
    PrimitiveWork.any (fun z => ⟨decide (z = v[y]),1⟩) (P.outgoing v[x])
  ⟨⟨lo.value,hi.value,edges.value⟩,lo.work+hi.work+edges.work+4*m^2+4*m+1⟩

private theorem system_ext {ι K : Type*} (A B : System ι K)
    (hl : A.lower = B.lower) (hu : A.upper = B.upper) (he : A.edge = B.edge) : A = B := by
  cases A; cases B; simp_all

theorem Reads.gather_value (P : Reads n) (v : Vector (Fin n) m) (e : Fin m ↪ Fin n)
    (hv : ∀ x, v[x] = e x) : (P.gather v).value.system = induced P.system e := by
  apply system_ext <;> funext x
  · simp [Reads.gather,Reads.system,induced,StoredSystem.system,hv]
  · simp [Reads.gather,Reads.system,induced,StoredSystem.system,hv]
  · funext y
    apply Bool.eq_iff_iff.mpr
    simp [Reads.gather,Reads.system,induced,StoredSystem.system,SparseClosure.lookup,hv,List.any_eq_true]

def gatherCost (m d W : ℕ) := 2*(m*(W+2)) + m*(m*(4*d+4)+2) + 4*m^2+4*m+1

theorem Reads.gather_work (P : Reads n) (v : Vector (Fin n) m) (d W : ℕ)
    (hd : ∀ x, (P.outgoing x).length ≤ d)
    (hl : ∀ x, (P.lower x).work ≤ W) (hu : ∀ x, (P.upper x).work ≤ W) :
    (P.gather v).work ≤ gatherCost m d W := by
  have hb (x y : Fin m) : (PrimitiveWork.any (fun z => (⟨decide (z=v[y]),1⟩ : Result Bool))
      (P.outgoing v[x])).work ≤ 4*d+2 := by
    have h := PrimitiveWork.any_work_le (fun z => (⟨decide (z=v[y]),1⟩ : Result Bool)) (P.outgoing v[x]) 1
      (fun _ _ => le_rfl)
    have := hd v[x]
    omega
  have hlo := PrimitiveWork.vector_work_le (fun x : Fin m => P.lower v[x]) W (fun x => hl _)
  have hhi := PrimitiveWork.vector_work_le (fun x : Fin m => P.upper v[x]) W (fun x => hu _)
  have he := PrimitiveWork.vector_work_le _ (m*(4*d+4)) (fun x : Fin m =>
    PrimitiveWork.vector_work_le _ (4*d+2) (hb x))
  unfold Reads.gather gatherCost
  dsimp only
  omega

/-- The proof cast is erased. The runtime vector is allocated from the
locally materialized list. -/
def labelsVector (D : System (Fin n) ℚ) (adj : Fin n → List (Fin n))
    (ha : ∀ x y, y ∈ adj x ↔ y ∈ neighbors D.edge x) (r : ℕ) (roots : List (Fin n)) :
    Result (Vector (Fin n) (retained D roots.toFinset r).card) :=
  let xs := sortedLabels adj r roots
  ⟨⟨xs.value.toArray,by simp only [xs,List.size_toArray,sortedLabels_value D adj ha,Finset.length_sort]⟩,
    xs.work+3*xs.value.length+1⟩

theorem labelsVector_get (D : System (Fin n) ℚ) (adj : Fin n → List (Fin n))
    (ha : ∀ x y, y ∈ adj x ↔ y ∈ neighbors D.edge x) (r : ℕ) (roots : List (Fin n))
    (x : Fin (retained D roots.toFinset r).card) :
    (labelsVector D adj ha r roots).value[x] = label (retained D roots.toFinset r) x := by
  simp only [labelsVector,Fin.getElem_fin,Vector.getElem_mk,List.getElem_toArray]
  simp only [sortedLabels_value D adj ha]
  exact (Finset.orderEmbOfFin_apply _ rfl x).symm

/-- Compute the topological order using the local matrix and compose its
local permutation with the sorted global label vector. -/
def ordered {m : ℕ} (P : Reads n) (labels : Vector (Fin n) m) : Result (Vector (Fin n) m) :=
  let raw := P.gather labels
  let order := NeighborhoodWork.orderVector raw.value
  let result := PrimitiveWork.vector fun x : Fin m => (⟨labels[order.value[x]],2⟩ : Result (Fin n))
  ⟨result.value,raw.work+order.work+result.work⟩

theorem ordered_get (P : Reads n) (R : Finset (Fin n)) (v : Vector (Fin n) R.card)
    (hv : ∀ x, v[x] = label R x) (x : Fin R.card) :
    (ordered P v).value[x] = NeighborhoodWork.localEmbedding P.system R x := by
  have hg := P.gather_value v (label R) hv
  simp only [ordered, PrimitiveWork.vector_value, Fin.getElem_fin, Vector.getElem_ofFn]
  change v[(NeighborhoodWork.orderVector (P.gather v).value).value[x]] = _
  simp only [NeighborhoodWork.orderVector_get,hg,hv,NeighborhoodWork.localEmbedding,
    Function.Embedding.trans_apply,Equiv.toEmbedding_apply]

theorem ordered_work (P : Reads n) (labels : Vector (Fin n) m) (d W : ℕ)
    (hd : ∀ x, (P.outgoing x).length ≤ d)
    (hl : ∀ x, (P.lower x).work ≤ W) (hu : ∀ x, (P.upper x).work ≤ W) :
    (ordered P labels).work ≤ gatherCost m d W + 110*(m+1)^3 + 4*m := by
  have a := P.gather_work labels d W hd hl hu
  have b := PrimitiveWork.vector_work_le (fun x : Fin m =>
    (⟨labels[(NeighborhoodWork.orderVector (P.gather labels).value).value[x]],2⟩ : Result (Fin n))) 2
    (fun _ => le_rfl)
  have c := NeighborhoodWork.orderVector_work (P.gather labels).value
  unfold ordered
  dsimp only
  omega


/-- Scan only the locally indexed vertices to mark the query locations. -/
def localMask (v : Vector (Fin n) m) (roots : List (Fin n)) : Result (SubsetWork.Mask m) :=
  PrimitiveWork.vector fun x =>
    PrimitiveWork.any (fun y => ⟨decide (y=v[x]),1⟩) roots

theorem localMask_set (v : Vector (Fin n) m) (roots : List (Fin n)) :
    SubsetWork.asSet (localMask v roots).value = Finset.univ.filter (fun x : Fin m => v[x] ∈ roots) := by
  ext x
  simp [SubsetWork.mem_asSet,localMask,List.any_eq_true]

theorem localMask_work (v : Vector (Fin n) m) (roots : List (Fin n)) :
    (localMask v roots).work ≤ m*(3*roots.length+4) := by
  apply (PrimitiveWork.vector_work_le _ (roots.length*3+2) (fun x =>
    PrimitiveWork.any_work_le _ roots 1 (fun _ _ => le_rfl))).trans
  exact Nat.mul_le_mul_left _ (by omega)

/-- Run the interior breadth layers and repeated sweep on the small matrix. -/
def schedule (D : StoredSystem m) (Q : SubsetWork.Mask m) (r t : ℕ) : Result (List (Fin m)) :=
  let interior := NeighborhoodWork.retainedMask D.edge Q r
  let xs := NeighborhoodWork.maskList interior.value
  let repeated := NeighborhoodWork.repeatList xs.value t
  ⟨repeated.value,interior.work+xs.work+repeated.work⟩

theorem schedule_value (D : StoredSystem m) (Q : SubsetWork.Mask m) (r t : ℕ) :
    (schedule D Q r t).value = localSchedule (retained D.system (SubsetWork.asSet Q) r) t := by
  simp only [schedule,NeighborhoodWork.repeat_value,NeighborhoodWork.maskList_value,localSchedule]
  congr 1
  apply List.filter_congr
  intro x _
  apply Bool.eq_iff_iff.mpr
  rw [← SubsetWork.mem_asSet,NeighborhoodWork.retainedMask_set]
  simp

theorem schedule_work (D : StoredSystem m) (Q : SubsetWork.Mask m) (r t : ℕ) :
    (schedule D Q r t).work ≤ 40*(r+2)*(m+1)^3 + (7*m+2) + 3*(t+1)^2*(m+1) := by
  let interior := NeighborhoodWork.retainedMask D.edge Q r
  let xs := NeighborhoodWork.maskList interior.value
  have hi := NeighborhoodWork.retainedMask_work D.edge Q r
  have hx := NeighborhoodWork.maskList_work interior.value
  have hr := NeighborhoodWork.repeat_work xs.value t
  have hm : xs.value.length ≤ m := by
    rw [show xs.value.length = _ from NeighborhoodWork.maskList_length interior.value]
    simpa using Finset.card_le_univ (SubsetWork.asSet interior.value)
  change interior.work + xs.work + _ ≤ _
  change interior.work ≤ _ at hi
  change xs.work ≤ _ at hx
  apply Nat.add_le_add (Nat.add_le_add hi hx)
  exact hr.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hm 1))


structure Prepared (n m : ℕ) where
  embedding : Vector (Fin n) m
  data : StoredSystem m
  schedule : List (Fin m)

def prepareFrom (P : Reads n) (v : Vector (Fin n) m)
    (roots : List (Fin n)) (r t : ℕ) : Result (Prepared n m) :=
  let e := ordered P v
  let data := P.gather e.value
  let q := localMask e.value roots
  let s := schedule data.value q.value r t
  ⟨⟨e.value,data.value,s.value⟩,e.work+data.work+q.work+s.work⟩

/-- Reindex the result only after all array allocations. In the actual
program their size is the length of the sorted, locally discovered list. -/
private def fromList (P : Reads n) (xs roots : List (Fin n)) (r t : ℕ)
    (size : xs.length = m) : Result (Prepared n m) :=
  let v : Vector (Fin n) xs.length := ⟨xs.toArray,by simp⟩
  let out := prepareFrom P v roots r t
  size ▸ out

private theorem fromList_eq (P : Reads n) (xs roots : List (Fin n)) (r t : ℕ)
    (size : xs.length = m) : fromList P xs roots r t size =
      prepareFrom P ⟨xs.toArray,by simpa only [List.size_toArray] using size⟩ roots r t := by
  subst m
  rfl

def prepare (P : Reads n) (D : System (Fin n) ℚ) (adj : Fin n → List (Fin n))
    (ha : ∀ x y, y ∈ adj x ↔ y ∈ neighbors D.edge x) (roots : List (Fin n)) (r t : ℕ) :
    Result (Prepared n (retained D roots.toFinset (r+1)).card) :=
  let labs := sortedLabels adj (r+1) roots
  let out := fromList P labs.value roots r t (by
    simp only [labs, sortedLabels_value D adj ha, Finset.length_sort])
  ⟨out.value, labs.work+3*labs.value.length+1+out.work⟩

private theorem prepare_value (P : Reads n) (D : System (Fin n) ℚ) (adj : Fin n → List (Fin n))
    (ha : ∀ x y, y ∈ adj x ↔ y ∈ neighbors D.edge x) (roots : List (Fin n)) (r t : ℕ) :
    (prepare P D adj ha roots r t).value = (prepareFrom P
      (labelsVector D adj ha (r+1) roots).value roots r t).value := by
  simp only [prepare,fromList_eq,labelsVector]

private theorem localEmbedding_eq (A D : System (Fin n) ℚ) (eq : A.edge = D.edge) (R : Finset (Fin n)) :
    NeighborhoodWork.localEmbedding A R = NeighborhoodWork.localEmbedding D R := by
  simp only [NeighborhoodWork.localEmbedding, GraphOrder.orderEquiv, GraphOrder.graphRank,
    induced, eq]

section Calibrated
variable (P : Reads n) (D : System (Fin n) ℚ) (eq : P.system.edge = D.edge)
  (adj : Fin n → List (Fin n)) (ha : ∀ x y, y ∈ adj x ↔ y ∈ neighbors D.edge x)
  (roots : List (Fin n)) (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)

def calibrated :=
  let t := Neighborhood.sweeps k H hk w hw
  prepare P D adj ha roots (H*t) t

include eq in
theorem calibrated_embedding (x : Fin (Neighborhood.labels D k H hk w hw roots.toFinset).card) :
    (calibrated P D adj ha roots k H hk w hw).value.embedding[x] =
      Neighborhood.embedding D k H hk w hw roots.toFinset x := by
  rw [calibrated,prepare_value]
  exact (ordered_get P _ _ (labelsVector_get D adj ha _ roots) x).trans
    (DFunLike.congr_fun (localEmbedding_eq P.system D eq _) x)

include eq in
theorem calibrated_edge (x y : Fin (Neighborhood.labels D k H hk w hw roots.toFinset).card) :
    (calibrated P D adj ha roots k H hk w hw).value.data.system.edge x y =
      (Neighborhood.system D k H hk w hw roots.toFinset).edge x y := by
  let v := (calibrated P D adj ha roots k H hk w hw).value.embedding
  have hg := P.gather_value v (Neighborhood.embedding D k H hk w hw roots.toFinset)
    (calibrated_embedding P D eq adj ha roots k H hk w hw)
  rw [show (calibrated P D adj ha roots k H hk w hw).value.data = (P.gather v).value by
    simp only [v,calibrated,prepare_value,prepareFrom]]
  rw [hg]
  change P.system.edge _ _ = D.edge _ _
  rw [eq]
  rfl

include eq in
theorem calibrated_schedule :
    (calibrated P D adj ha roots k H hk w hw).value.schedule =
      Neighborhood.schedule D k H hk w hw roots.toFinset := by
  let N := (calibrated P D adj ha roots k H hk w hw).value
  let e := Neighborhood.embedding D k H hk w hw roots.toFinset
  let t := Neighborhood.sweeps k H hk w hw
  have he : N.data.system.edge = (Neighborhood.system D k H hk w hw roots.toFinset).edge :=
    funext fun x => funext fun y => calibrated_edge P D eq adj ha roots k H hk w hw x y
  have hq : SubsetWork.asSet (localMask N.embedding roots).value =
      Neighborhood.queries D k H hk w hw roots.toFinset := by
    rw [localMask_set]
    ext x
    simp only [Neighborhood.mem_queries,Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset]
    rw [show N.embedding[x] = e x from calibrated_embedding P D eq adj ha roots k H hk w hw x]
    exact List.mem_toFinset.symm.trans (Neighborhood.mem_queries D k H hk w hw roots.toFinset x).symm
  rw [show (calibrated P D adj ha roots k H hk w hw).value.schedule =
      (schedule N.data (localMask N.embedding roots).value (H*t) t).value by
    simp only [N,t,calibrated,prepare_value,prepareFrom]]
  rw [schedule_value,hq]
  exact congrArg (fun E => localSchedule ((Neighborhood.queries D k H hk w hw roots.toFinset).biUnion
    (fun x => ball E x (H*t))) t) he

end Calibrated


/-- Recover a local index from its original label by inspecting the short
embedding vector. There is no label-sized inverse array. -/
def queryIndex (v : Vector (Fin n) m) (x : Fin n) : Result (Option (Fin m)) :=
  let indices := FiniteLoopWork.indices m
  let found := PrimitiveWork.find (fun i => ⟨decide (v[i]=x),2⟩) indices.value
  ⟨found.value,indices.work+found.work⟩

theorem queryIndex_value (v : Vector (Fin n) m) (e : Fin m ↪ Fin n) (hv : ∀ i, v[i] = e i)
    (i : Fin m) : (queryIndex v (e i)).value = some i := by
  simp only [queryIndex, PrimitiveWork.find_value,FiniteLoopWork.indices,hv]
  generalize he : (List.finRange m).find? (fun j => decide (e j = e i)) = o
  cases o with
  | none =>
    have hn := List.find?_eq_none.mp he i (by simp)
    simp at hn
  | some j =>
    exact congrArg some (e.injective (of_decide_eq_true (List.find?_some (p := fun j => decide (e j = e i)) he)))

theorem queryIndex_work (v : Vector (Fin n) m) (x : Fin n) : (queryIndex v x).work ≤ 7*m+2 := by
  have h := PrimitiveWork.find_work_le (fun i : Fin m => (⟨decide (v[i]=x),2⟩ : Result Bool))
    (List.finRange m) 2 (fun _ _ => le_rfl)
  simp only [List.length_finRange] at h
  simp only [queryIndex,FiniteLoopWork.indices]
  omega

/-- The local work is polynomial in the number of possible visits, the
radius, sweep count, and cost of fetching an individual wall. -/
def prepCost (m d W roots r t : ℕ) :=
  gatherCost m d W + 110*(m+1)^3 + 4*m + gatherCost m d W +
    m*(3*roots+4) + (40*(r+2)*(m+1)^3 + (7*m+2) + 3*(t+1)^2*(m+1))

theorem prepareFrom_work (P : Reads n) (v : Vector (Fin n) m) (roots : List (Fin n))
    (r t d W : ℕ) (hd : ∀ x, (P.outgoing x).length ≤ d)
    (hl : ∀ x, (P.lower x).work ≤ W) (hu : ∀ x, (P.upper x).work ≤ W) :
    (prepareFrom P v roots r t).work ≤ prepCost m d W roots.length r t := by
  let e := ordered P v
  let data := P.gather e.value
  let q := localMask e.value roots
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (ordered_work P v d W hd hl hu)
    (P.gather_work _ _ _ hd hl hu)) (localMask_work e.value roots))
      (schedule_work data.value q.value r t)

def totalCost (d W roots r t : ℕ) :=
  let m := roots*(d+1)^(r+1)
  roots*(4*(d+1)^(r+1)+2)+1 + 13*(m+1)^2 + 3*m + 1 + prepCost m d W roots r t

theorem prepare_work (P : Reads n) (D : System (Fin n) ℚ) (adj : Fin n → List (Fin n))
    (ha : ∀ x y, y ∈ adj x ↔ y ∈ neighbors D.edge x) (roots : List (Fin n)) (r t d W : ℕ)
    (hd : ∀ x, (adj x).length ≤ d) (ho : ∀ x, (P.outgoing x).length ≤ d)
    (hl : ∀ x, (P.lower x).work ≤ W) (hu : ∀ x, (P.upper x).work ≤ W) :
    (prepare P D adj ha roots r t).work ≤ totalCost d W roots.length r t := by
  let R := retained D roots.toFinset (r+1)
  let labs := sortedLabels adj (r+1) roots
  have bound := walk_length adj d hd (r+1) roots
  have hc : R.card ≤ roots.length*(d+1)^(r+1) := by
    have hs : R = (walk adj (r+1) roots).value.toFinset := by
      ext x
      exact ((walk_mem D adj ha (r+1) roots x).symm).trans List.mem_toFinset.symm
    rw [hs]
    exact (List.toFinset_card_le _).trans bound
  have len : labs.value.length = R.card := by simp only [labs,R,sortedLabels_value D adj ha,Finset.length_sort]
  have wp := sortedLabels_work adj d hd (r+1) roots
  let v := (labelsVector D adj ha (r+1) roots).value
  have wf := prepareFrom_work P v roots r t d W ho hl hu
  have cap : prepCost R.card d W roots.length r t ≤ prepCost (roots.length*(d+1)^(r+1)) d W roots.length r t := by
    unfold prepCost gatherCost
    gcongr
  change labs.work + 3*labs.value.length + 1 + _ ≤ _
  rw [fromList_eq]
  change labs.work + 3*labs.value.length + 1 + (prepareFrom P v roots r t).work ≤ _
  unfold totalCost
  dsimp only
  change labs.work ≤ _ at wp
  change (prepareFrom P v roots r t).work ≤ prepCost R.card d W roots.length r t at wf
  omega

/-- Run a caller on a dynamically sized neighborhood, using only stored row
readers, query labels and stage parameters. The charge covers the concrete
cost of one row access in the chosen dictionary representation. -/
def withPrepared {α : Type*} (P : Reads n) (adj : Fin n → List (Fin n)) (roots : List (Fin n))
    (r t charge : ℕ) (f : ∀ {m}, Prepared n m → Result α) : Result α :=
  let labs := sortedLabels adj (r+1) roots
  let v : Vector (Fin n) labs.value.length := ⟨labs.value.toArray,by simp⟩
  let env := prepareFrom P v roots r t
  let out := f env.value
  ⟨out.value,charge*(labs.work+3*labs.value.length+1+env.work)+out.work⟩

private theorem consume_eq {α : Type*} (P : Reads n) (xs roots : List (Fin n)) (r t : ℕ)
    (f : ∀ {m}, Prepared n m → Result α) (size : xs.length=m) :
    f (prepareFrom P (⟨xs.toArray,by simp⟩ : Vector (Fin n) xs.length) roots r t).value =
      f (fromList P xs roots r t size).value ∧
    (prepareFrom P (⟨xs.toArray,by simp⟩ : Vector (Fin n) xs.length) roots r t).work =
      (fromList P xs roots r t size).work := by
  subst m
  exact ⟨rfl,rfl⟩

theorem withPrepared_eq {α : Type*} (P : Reads n) (D : System (Fin n) ℚ) (adj : Fin n → List (Fin n))
    (ha : ∀ x y, y ∈ adj x ↔ y ∈ neighbors D.edge x) (roots : List (Fin n)) (r t charge : ℕ)
    (f : ∀ {m}, Prepared n m → Result α) :
    let env := prepare P D adj ha roots r t
    withPrepared P adj roots r t charge f = ⟨(f env.value).value,charge*env.work+(f env.value).work⟩ := by
  let labs := sortedLabels adj (r+1) roots
  have sz : labs.value.length = (retained D roots.toFinset (r+1)).card := by
    simp only [labs,sortedLabels_value D adj ha,Finset.length_sort]
  obtain ⟨out,cost⟩ := consume_eq P labs.value roots r t @f sz
  unfold withPrepared prepare
  dsimp only
  rw [show _ = _ from out,show _ = _ from cost]

end SortingAdversary.Continuous.PolylogNeighborhood
