import SortingAdversary.Continuous.ArbitraryLabels
import SortingAdversary.Continuous.EnclosureWork
import SortingAdversary.Continuous.GraphWork
import SortingAdversary.Optimal.FiniteLoopWork
import SortingAdversary.Optimal.HubSortWork
import SortingAdversary.Optimal.SubsetWork

/-!
# Counted extraction of the local update schedule

Undirected balls are computed by stored Boolean tables, one breadth layer
at a time. The retained labels and their graph order are materialized before
constructing the interior schedule. The final schedule uses ambient labels;
`Neighborhood.enclose_full` proves that its endpoint calculations equal the
retained-graph calculation exactly. Ambient vectors add only polynomial
copying and scanning costs.
-/

namespace SortingAdversary.Continuous.NeighborhoodWork

open FiniteAveraging OrderRegion EnclosureWork
open SortingAdversary.Optimal
open PrimitiveWork
open SortingAdversary.Optimal.GraphBalls

variable {n m : ℕ}

/-- One Boolean breadth layer, sharing the previous table and label list. -/
def ballStep (E T : SparseClosure.Table n) : Result (SparseClosure.Table n) :=
  let domain := FiniteLoopWork.indices n
  let result := PrimitiveWork.vector fun x => PrimitiveWork.vector fun y =>
    PrimitiveWork.any (fun z =>
      ⟨(decide (z = x) || E[x][z] || E[z][x]) && T[z][y], 9⟩) domain.value
  ⟨result.value, domain.work + result.work⟩

@[simp] theorem ballStep_true (E T : SparseClosure.Table n) (x y : Fin n) :
    (ballStep E T).value[x][y] = true ↔
      ∃ z ∈ closedNeighbors (SparseClosure.lookup E) x, T[z][y] = true := by
  simp [ballStep, PrimitiveWork.vector_value, PrimitiveWork.any_value,
    FiniteLoopWork.indices, List.any_eq_true, mem_closedNeighbors,
    SparseClosure.lookup, or_assoc]

theorem ballStep_work (E T : SparseClosure.Table n) :
    (ballStep E T).work ≤ 20 * (n + 1) ^ 3 := by
  have ha (x y : Fin n) := PrimitiveWork.any_work_le
    (fun z : Fin n => (⟨(decide (z = x) || E[x][z] || E[z][x]) && T[z][y], 9⟩ : Result Bool))
    (List.finRange n) 9 (fun _ _ => le_rfl)
  simp only [List.length_finRange, Nat.reduceAdd] at ha
  have hr (x : Fin n) := PrimitiveWork.vector_work_le
    (fun y => PrimitiveWork.any (fun z : Fin n =>
      (⟨(decide (z = x) || E[x][z] || E[z][x]) && T[z][y], 9⟩ : Result Bool))
      (List.finRange n)) (n * 11 + 2) (ha x)
  have ht := PrimitiveWork.vector_work_le
    (fun x => PrimitiveWork.vector fun y => PrimitiveWork.any (fun z : Fin n =>
      (⟨(decide (z = x) || E[x][z] || E[z][x]) && T[z][y], 9⟩ : Result Bool))
      (List.finRange n)) (n * (n * 11 + 2 + 2)) hr
  change 3 * n + 1 + _ ≤ _
  dsimp only [FiniteLoopWork.indices]
  nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)]

def balls (E : SparseClosure.Table n) : ℕ → Result (SparseClosure.Table n)
  | 0 => PrimitiveWork.vector fun x => PrimitiveWork.vector fun y => atom (decide (y = x))
  | r + 1 =>
      let old := balls E r
      let next := ballStep E old.value
      ⟨next.value, old.work + next.work + 1⟩

@[simp] theorem balls_true (E : SparseClosure.Table n) (r : ℕ) (x y : Fin n) :
    (balls E r).value[x][y] = true ↔ y ∈ ball (SparseClosure.lookup E) x r := by
  induction r generalizing x y with
  | zero => simp [balls, atom]
  | succ r ih =>
    simp only [balls, ballStep_true, mem_ball_succ]
    exact exists_congr fun z => and_congr_right fun _ => ih z y

theorem balls_work (E : SparseClosure.Table n) (r : ℕ) :
    (balls E r).work ≤ (r + 1) * (20 * (n + 1) ^ 3 + 1) := by
  induction r with
  | zero =>
    have hi (x : Fin n) := PrimitiveWork.vector_work_le
      (fun y : Fin n => atom (decide (y = x))) 1 (fun _ => le_rfl)
    have hh := PrimitiveWork.vector_work_le
      (fun x : Fin n => PrimitiveWork.vector fun y : Fin n => atom (decide (y = x)))
      (n * 3) hi
    change (PrimitiveWork.vector _).work ≤ _
    nlinarith [Nat.zero_le (n ^ 3)]
  | succ r ih =>
    have hs := ballStep_work E (balls E r).value
    change (balls E r).work + (ballStep E (balls E r).value).work + 1 ≤ _
    nlinarith

/-- Union of the balls around a stored query mask. -/
def retainedMask (E : SparseClosure.Table n) (Q : SubsetWork.Mask n) (r : ℕ) :
    Result (SubsetWork.Mask n) :=
  let table := balls E r
  let domain := FiniteLoopWork.indices n
  let mask := PrimitiveWork.vector fun x => PrimitiveWork.any
    (fun q => ⟨Q[q] && table.value[q][x], 4⟩) domain.value
  ⟨mask.value, table.work + domain.work + mask.work⟩

@[simp] theorem retainedMask_true (E : SparseClosure.Table n) (Q : SubsetWork.Mask n)
    (r : ℕ) (x : Fin n) :
    (retainedMask E Q r).value[x] = true ↔
      ∃ q ∈ SubsetWork.asSet Q, x ∈ ball (SparseClosure.lookup E) q r := by
  simp [retainedMask, PrimitiveWork.vector_value, PrimitiveWork.any_value,
    FiniteLoopWork.indices, List.any_eq_true]
  exact exists_congr fun q => and_congr_right fun _ => balls_true E r q x

theorem retainedMask_set (D : StoredSystem n) (Q : SubsetWork.Mask n) (r : ℕ) :
    SubsetWork.asSet (retainedMask D.edge Q r).value =
      InducedEnclosure.retained D.system (SubsetWork.asSet Q) r := by
  ext x
  simp only [SubsetWork.mem_asSet, retainedMask_true, InducedEnclosure.retained,
    Finset.mem_biUnion, StoredSystem.system]

theorem retainedMask_work (E : SparseClosure.Table n) (Q : SubsetWork.Mask n) (r : ℕ) :
    (retainedMask E Q r).work ≤ 40 * (r + 2) * (n + 1) ^ 3 := by
  have hb := balls_work E r
  have ha (x : Fin n) := PrimitiveWork.any_work_le
    (fun q : Fin n => (⟨Q[q] && (balls E r).value[q][x], 4⟩ : Result Bool))
    (List.finRange n) 4 (fun _ _ => le_rfl)
  simp only [List.length_finRange, Nat.reduceAdd] at ha
  have hv := PrimitiveWork.vector_work_le
    (fun x => PrimitiveWork.any (fun q : Fin n =>
      (⟨Q[q] && (balls E r).value[q][x], 4⟩ : Result Bool)) (List.finRange n))
    (n * 6 + 2) ha
  change (balls E r).work + (3 * n + 1) + _ ≤ _
  dsimp only [FiniteLoopWork.indices]
  nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)]

/-- An explicit finite scan, already in increasing original-label order. -/
def maskList (Q : SubsetWork.Mask n) : Result (List (Fin n)) :=
  let domain := FiniteLoopWork.indices n
  let xs := FiniteLoopWork.filter (fun x => ⟨Q[x], 1⟩) domain.value
  ⟨xs.value, domain.work + xs.work⟩

@[simp] theorem maskList_value (Q : SubsetWork.Mask n) :
    (maskList Q).value = (List.finRange n).filter (fun x => Q[x]) := by
  simp only [maskList, FiniteLoopWork.filter_value, FiniteLoopWork.indices]

@[simp] theorem maskList_length (Q : SubsetWork.Mask n) :
    (maskList Q).value.length = (SubsetWork.asSet Q).card := by
  rw [maskList_value, RankWork.filter_finRange_length]
  rfl

theorem maskList_work (Q : SubsetWork.Mask n) : (maskList Q).work ≤ 7 * n + 2 := by
  have h := FiniteLoopWork.filter_work_le
    (fun x : Fin n => (⟨Q[x], 1⟩ : Result Bool)) (List.finRange n) 1 (fun _ _ => le_rfl)
  simp only [List.length_finRange, Nat.reduceAdd] at h
  change 3 * n + 1 + _ ≤ _
  dsimp only [FiniteLoopWork.indices]
  omega

theorem maskList_sort (Q : SubsetWork.Mask n) :
    (maskList Q).value = (SubsetWork.asSet Q).sort (· ≤ ·) := by
  have hp : (maskList Q).value.Perm ((SubsetWork.asSet Q).sort (· ≤ ·)) := by
    rw [maskList_value]
    apply (List.perm_ext_iff_of_nodup
      ((List.nodup_finRange n).filter (fun x => Q[x]))
      ((SubsetWork.asSet Q).sort_nodup (· ≤ ·))).mpr
    intro x
    simp
  have hsorted := (Finset.pairwise_sort (Finset.univ : Finset (Fin n)) (· ≤ ·))
  rw [Fin.sort_univ] at hsorted
  exact hp.eq_of_pairwise' (by simpa only [maskList_value] using hsorted.filter (fun x => Q[x]))
    (Finset.pairwise_sort _ _)

/-- Cache the increasing embedding in a vector. Proof casts erase. -/
def labelVector (Q : SubsetWork.Mask n) :
    Result (Vector (Fin n) (SubsetWork.asSet Q).card) :=
  let xs := maskList Q
  ⟨⟨xs.value.toArray, by
      change (maskList Q).value.toArray.size = _
      simpa only [List.size_toArray] using maskList_length Q⟩, xs.work + 3 * xs.value.length + 1⟩

@[simp] theorem labelVector_get (Q : SubsetWork.Mask n)
    (x : Fin (SubsetWork.asSet Q).card) :
    (labelVector Q).value[x] = InducedEnclosure.label (SubsetWork.asSet Q) x := by
  simp only [labelVector, Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray]
  simp only [maskList_sort]
  exact (Finset.orderEmbOfFin_apply _ rfl x).symm

theorem labelVector_work (Q : SubsetWork.Mask n) : (labelVector Q).work ≤ 10 * n + 3 := by
  have hm := maskList_work Q
  have hc : (SubsetWork.asSet Q).card ≤ n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (SubsetWork.asSet Q)
  change (maskList Q).work + 3 * (maskList Q).value.length + 1 ≤ _
  rw [maskList_length]
  omega

/-- Pull back all three stored arrays through a materialized label vector. -/
def gather (D : StoredSystem n) (e : Vector (Fin n) m) : Result (StoredSystem m) :=
  let lo := PrimitiveWork.vector (fun x => ⟨D.lower[e[x]], 2⟩)
  let hi := PrimitiveWork.vector (fun x => ⟨D.upper[e[x]], 2⟩)
  let edges := PrimitiveWork.vector fun x => PrimitiveWork.vector fun y =>
    (⟨D.edge[e[x]][e[y]], 4⟩ : Result Bool)
  ⟨⟨lo.value, hi.value, edges.value⟩, lo.work + hi.work + edges.work + 1⟩

@[simp] theorem gather_lower (D : StoredSystem n) (e : Vector (Fin n) m) (x : Fin m) :
    (gather D e).value.system.lower x = D.system.lower e[x] := by
  simp [gather, StoredSystem.system]

@[simp] theorem gather_upper (D : StoredSystem n) (e : Vector (Fin n) m) (x : Fin m) :
    (gather D e).value.system.upper x = D.system.upper e[x] := by
  simp [gather, StoredSystem.system]

@[simp] theorem gather_edge (D : StoredSystem n) (e : Vector (Fin n) m) (x y : Fin m) :
    (gather D e).value.system.edge x y = D.system.edge e[x] e[y] := by
  simp [gather, StoredSystem.system, SparseClosure.lookup]

theorem gather_work (D : StoredSystem n) (e : Vector (Fin n) m) :
    (gather D e).work ≤ 6 * m ^ 2 + 10 * m + 1 := by
  have hlo := PrimitiveWork.vector_work_le (fun x : Fin m => (⟨D.lower[e[x]], 2⟩ : Result ℚ)) 2
    (fun _ => le_rfl)
  have hhi := PrimitiveWork.vector_work_le (fun x : Fin m => (⟨D.upper[e[x]], 2⟩ : Result ℚ)) 2
    (fun _ => le_rfl)
  have hr (x : Fin m) := PrimitiveWork.vector_work_le
    (fun y : Fin m => (⟨D.edge[e[x]][e[y]], 4⟩ : Result Bool)) 4 (fun _ => le_rfl)
  have he := PrimitiveWork.vector_work_le
    (fun x : Fin m => PrimitiveWork.vector fun y : Fin m =>
      (⟨D.edge[e[x]][e[y]], 4⟩ : Result Bool)) (m * 6) hr
  change _ + _ + _ + 1 ≤ _
  nlinarith

private theorem graphRank_injective (D : StoredSystem n) :
    Function.Injective (GraphOrder.graphRank D.system) := by
  intro x y h
  apply PublicOrder.extensionRank_injective (SparseClosure.closure D.system.edge)
  apply Fin.ext
  simpa only [GraphOrder.graphRank_eq] using h

def orderedLabels (D : StoredSystem n) : Result (List (Fin n)) :=
  let ranks := GraphWork.closureRanks (fun x y => ⟨D.edge[x][y], 2⟩)
  let domain := FiniteLoopWork.indices n
  let result := HubSortWork.sort (fun x y => ⟨decide (ranks.value[x].val ≤ ranks.value[y].val), 3⟩)
    domain.value
  ⟨result.value, ranks.work + domain.work + result.work⟩

@[simp] theorem orderedLabels_value (D : StoredSystem n) :
    (orderedLabels D).value = rankOrder (GraphOrder.graphRank D.system) := by
  let r := fun x y : Fin n => GraphOrder.graphRank D.system x ≤ GraphOrder.graphRank D.system y
  letI : Std.Total r := ⟨fun x y => le_total _ _⟩
  letI : IsTrans (Fin n) r := ⟨fun _ _ _ h₁ h₂ => le_trans h₁ h₂⟩
  letI : Std.Antisymm r := ⟨fun _ _ h₁ h₂ => graphRank_injective D (le_antisymm h₁ h₂)⟩
  have hgraph (x : Fin n) := GraphWork.closureRanks_graphRank D.system
    (fun x y => (⟨D.edge[x][y], 2⟩ : Result Bool)) rfl x
  simp only [orderedLabels, HubSortWork.sort_value, FiniteLoopWork.indices, hgraph,
    decide_eq_true_eq]
  exact (List.mergeSort_eq_insertionSort r (List.finRange n)).symm

theorem orderedLabels_work (D : StoredSystem n) :
    (orderedLabels D).work ≤ 100 * (n + 1) ^ 3 := by
  have hr := GraphWork.closureRanks_work
    (fun x y : Fin n => (⟨D.edge[x][y], 2⟩ : Result Bool)) 2 (fun _ _ => le_rfl)
  have hs := HubSortWork.sort_work_le
    (fun x y : Fin n => (⟨decide
      ((GraphWork.closureRanks (fun x y => ⟨D.edge[x][y], 2⟩)).value[x].val ≤
       (GraphWork.closureRanks (fun x y => ⟨D.edge[x][y], 2⟩)).value[y].val), 3⟩ : Result Bool))
    (List.finRange n) 3 (fun _ _ => le_rfl)
  simp only [List.length_finRange, Nat.reduceAdd] at hs
  change _ + (3 * n + 1) + _ ≤ _
  dsimp only [FiniteLoopWork.indices]
  unfold GraphWork.closureRanksBound ClosureWork.workBound at hr
  nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)]

def orderVector (D : StoredSystem n) : Result (Vector (Fin n) n) :=
  let xs := orderedLabels D
  ⟨⟨xs.value.toArray, by
      change (orderedLabels D).value.toArray.size = _
      simp only [List.size_toArray, orderedLabels_value, rankOrder_length]⟩, xs.work + 3 * n + 1⟩

@[simp] theorem orderVector_get (D : StoredSystem n) (x : Fin n) :
    (orderVector D).value[x] = GraphOrder.orderEquiv D.system x := by
  simp only [orderVector, Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray,
    GraphOrder.orderEquiv, rankEquiv_apply, List.get_eq_getElem]
  simp only [orderedLabels_value]

theorem orderVector_work (D : StoredSystem n) :
    (orderVector D).work ≤ 110 * (n + 1) ^ 3 := by
  have h := orderedLabels_work D
  change (orderedLabels D).work + 3 * n + 1 ≤ _
  nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)]

def repeatList (xs : List α) : ℕ → Result (List α)
  | 0 => ⟨[], 1⟩
  | t + 1 =>
      let old := repeatList xs t
      let joined := FiniteLoopWork.append old.value xs
      ⟨joined.value, old.work + joined.work + 1⟩

@[simp] theorem repeat_value (xs : List α) (t : ℕ) :
    (repeatList xs t).value = repeatSchedule xs t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [repeatList, FiniteLoopWork.append_value, ih, repeatSchedule]

theorem repeat_work (xs : List α) (t : ℕ) :
    (repeatList xs t).work ≤ 3 * (t + 1) ^ 2 * (xs.length + 1) := by
  induction t with
  | zero => simp only [repeatList]; nlinarith
  | succ t ih =>
    change (repeatList xs t).work + (FiniteLoopWork.append (repeatList xs t).value xs).work + 1 ≤ _
    rw [FiniteLoopWork.append_work, repeat_value, repeatSchedule_length]
    nlinarith [Nat.zero_le (t * xs.length)]

private theorem system_ext {ι K : Type*} (A B : System ι K)
    (hl : A.lower = B.lower) (hu : A.upper = B.upper) (he : A.edge = B.edge) : A = B := by
  cases A
  cases B
  cases hl
  cases hu
  cases he
  rfl

theorem gather_system (D : StoredSystem n) (v : Vector (Fin n) m)
    (e : Fin m ↪ Fin n) (he : ∀ x, v[x] = e x) :
    (gather D v).value.system = InducedEnclosure.induced D.system e := by
  apply system_ext
  · funext x
    simpa only [InducedEnclosure.induced, he] using gather_lower D v x
  · funext x
    simpa only [InducedEnclosure.induced, he] using gather_upper D v x
  · funext x y
    simpa only [InducedEnclosure.induced, he] using gather_edge D v x y

def localEmbedding (D : System (Fin n) ℚ) (R : Finset (Fin n)) : Fin R.card ↪ Fin n :=
  (GraphOrder.orderEquiv (InducedEnclosure.induced D (InducedEnclosure.label R))).toEmbedding.trans
    (InducedEnclosure.label R)

abbrev retainedSet (D : StoredSystem n) (Q : SubsetWork.Mask n) (r : ℕ) : Finset (Fin n) :=
  SubsetWork.asSet (retainedMask D.edge Q (r + 1)).value

def embeddingVector (D : StoredSystem n) (Q : SubsetWork.Mask n) (r : ℕ) :
    Result (Vector (Fin n) (retainedSet D Q r).card) :=
  let retained := retainedMask D.edge Q (r + 1)
  let labels := labelVector retained.value
  let raw := gather D labels.value
  let order := orderVector raw.value
  let result := PrimitiveWork.vector (fun x => ⟨labels.value[order.value[x]], 2⟩)
  ⟨result.value, retained.work + labels.work + raw.work + order.work + result.work⟩

@[simp] theorem embeddingVector_get (D : StoredSystem n) (Q : SubsetWork.Mask n)
    (r : ℕ) (x : Fin (retainedSet D Q r).card) :
    (embeddingVector D Q r).value[x] = localEmbedding D.system (retainedSet D Q r) x := by
  let mask := (retainedMask D.edge Q (r + 1)).value
  have hraw := gather_system D (labelVector mask).value (InducedEnclosure.label (SubsetWork.asSet mask))
    (labelVector_get mask)
  change (PrimitiveWork.vector (fun z =>
    (⟨(labelVector mask).value[(orderVector (gather D (labelVector mask).value).value).value[z]], 2⟩ :
      Result (Fin n)))).value[x] = _
  simp only [PrimitiveWork.vector_value, Fin.getElem_fin, Vector.getElem_ofFn]
  change (labelVector mask).value[(orderVector (gather D (labelVector mask).value).value).value[x]] = _
  simp only [orderVector_get, hraw, labelVector_get, localEmbedding,
    Function.Embedding.trans_apply, Equiv.toEmbedding_apply]
  rfl

theorem embeddingVector_work (D : StoredSystem n) (Q : SubsetWork.Mask n) (r : ℕ) :
    (embeddingVector D Q r).work ≤ 200 * (r + 3) * (n + 1) ^ 3 := by
  let mask := (retainedMask D.edge Q (r + 1)).value
  let m := (SubsetWork.asSet mask).card
  have hm : m ≤ n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (SubsetWork.asSet mask)
  have hmask := retainedMask_work D.edge Q (r + 1)
  have hl := labelVector_work mask
  have hg := gather_work D (labelVector mask).value
  have ho := orderVector_work (gather D (labelVector mask).value).value
  have hv := PrimitiveWork.vector_work_le
    (fun x : Fin m => (⟨(labelVector mask).value[
      (orderVector (gather D (labelVector mask).value).value).value[x]], 2⟩ : Result (Fin n)))
    2 (fun _ => le_rfl)
  change _ + _ + _ + _ + _ ≤ _
  dsimp only [mask, m] at hm hv
  have hm2 := Nat.pow_le_pow_left hm 2
  have hm3 := Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) 3
  dsimp only [mask] at hl hg ho hv
  nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)]

def queriesMask (Q : SubsetWork.Mask n) (e : Vector (Fin n) m) : Result (SubsetWork.Mask m) :=
  PrimitiveWork.vector (fun x => ⟨Q[e[x]], 2⟩)

@[simp] theorem queriesMask_get (Q : SubsetWork.Mask n) (e : Vector (Fin n) m) (x : Fin m) :
    (queriesMask Q e).value[x] = Q[e[x]] := by simp [queriesMask]

theorem queriesMask_work (Q : SubsetWork.Mask n) (e : Vector (Fin n) m) :
    (queriesMask Q e).work ≤ 4 * m := by
  simpa only [queriesMask, Nat.mul_comm, Nat.reduceAdd] using PrimitiveWork.vector_work_le
    (fun x : Fin m => (⟨Q[e[x]], 2⟩ : Result Bool)) 2 (fun _ => le_rfl)

def scheduleSpec (D : System (Fin n) ℚ) (R Q : Finset (Fin n)) (r t : ℕ) : List (Fin n) :=
  let e := localEmbedding D R
  let E := InducedEnclosure.induced D e
  let queries := Finset.univ.filter (fun x => e x ∈ Q)
  (localSchedule (InducedEnclosure.retained E queries r) t).map e

def fullScheduleAt (D : StoredSystem n) (Q : SubsetWork.Mask n) (r t : ℕ) : Result (List (Fin n)) :=
  let embedding := embeddingVector D Q r
  let localData := gather D embedding.value
  let queries := queriesMask Q embedding.value
  let interior := retainedMask localData.value.edge queries.value r
  let once := maskList interior.value
  let repeated := repeatList once.value t
  let answer := PrimitiveWork.map (fun x => ⟨embedding.value[x], 1⟩) repeated.value
  ⟨answer.value, embedding.work + localData.work + queries.work + interior.work + once.work +
      repeated.work + answer.work⟩

theorem fullScheduleAt_value (D : StoredSystem n) (Q : SubsetWork.Mask n) (r t : ℕ) :
    (fullScheduleAt D Q r t).value =
      scheduleSpec D.system (retainedSet D Q r) (SubsetWork.asSet Q) r t := by
  let e := localEmbedding D.system (retainedSet D Q r)
  have hlocal := gather_system D (embeddingVector D Q r).value e (embeddingVector_get D Q r)
  have hquery : SubsetWork.asSet (queriesMask Q (embeddingVector D Q r).value).value =
      Finset.univ.filter (fun x => e x ∈ SubsetWork.asSet Q) := by
    ext x
    simp only [SubsetWork.mem_asSet, queriesMask_get, embeddingVector_get,
      Finset.mem_filter, Finset.mem_univ, true_and, e]
  have hinterior := retainedMask_set (gather D (embeddingVector D Q r).value).value
    (queriesMask Q (embeddingVector D Q r).value).value r
  rw [hlocal, hquery] at hinterior
  unfold fullScheduleAt scheduleSpec
  simp only [PrimitiveWork.map_value, repeat_value, maskList_value, embeddingVector_get]
  congr 1
  unfold localSchedule
  congr 1
  apply List.filter_congr
  intro x hx
  exact Bool.eq_iff_iff.mpr (by
    simpa only [decide_eq_true_eq, ← SubsetWork.mem_asSet] using
      (show x ∈ SubsetWork.asSet
          (retainedMask (gather D (embeddingVector D Q r).value).value.edge
            (queriesMask Q (embeddingVector D Q r).value).value r).value ↔
        x ∈ InducedEnclosure.retained (InducedEnclosure.induced D.system e)
          (Finset.univ.filter fun x => e x ∈ SubsetWork.asSet Q) r by rw [hinterior]))

private theorem schedule_work_arithmetic {n m r t l E D Q I O P A : ℕ}
    (hm : m ≤ n) (hl : l ≤ m)
    (he : E ≤ 200 * (r + 3) * (n + 1) ^ 3)
    (hd : D ≤ 6 * m ^ 2 + 10 * m + 1) (hq : Q ≤ 4 * m)
    (hi : I ≤ 40 * (r + 2) * (m + 1) ^ 3) (ho : O ≤ 7 * m + 2)
    (hp : P ≤ 3 * (t + 1) ^ 2 * (l + 1)) (ha : A ≤ l * t * 3 + 1) :
    E + D + Q + I + O + P + A ≤
      400 * (r + 3) * (n + 1) ^ 3 + 20 * (t + 1) ^ 2 * (n + 1) := by
  have hd' : D ≤ 6 * n ^ 2 + 10 * n + 1 := hd.trans (by gcongr)
  have hq' : Q ≤ 4 * n := hq.trans (Nat.mul_le_mul_left 4 hm)
  have hi' : I ≤ 40 * (r + 2) * (n + 1) ^ 3 := hi.trans (by gcongr)
  have ho' : O ≤ 7 * n + 2 := ho.trans (by gcongr)
  have hp' : P ≤ 3 * (t + 1) ^ 2 * (n + 1) := hp.trans (by gcongr; exact hl.trans hm)
  have ha' : A ≤ n * t * 3 + 1 := ha.trans (by gcongr; exact hl.trans hm)
  calc
    _ ≤ 200 * (r + 3) * (n + 1) ^ 3 + (6 * n ^ 2 + 10 * n + 1) +
        4 * n + 40 * (r + 2) * (n + 1) ^ 3 + (7 * n + 2) +
        3 * (t + 1) ^ 2 * (n + 1) + (n * t * 3 + 1) := by omega
    _ ≤ _ := by ring_nf; omega

theorem fullScheduleAt_work (D : StoredSystem n) (Q : SubsetWork.Mask n) (r t : ℕ) :
    (fullScheduleAt D Q r t).work ≤
      400 * (r + 3) * (n + 1) ^ 3 + 20 * (t + 1) ^ 2 * (n + 1) := by
  let emb := embeddingVector D Q r
  let data := gather D emb.value
  let queries := queriesMask Q emb.value
  let mask := retainedMask data.value.edge queries.value r
  let once := maskList mask.value
  let reps := repeatList once.value t
  let m := (retainedSet D Q r).card
  have hm : m ≤ n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (retainedSet D Q r)
  have hlen : once.value.length ≤ m := by
    change (maskList mask.value).value.length ≤ m
    rw [maskList_length]
    simpa only [Fintype.card_fin] using Finset.card_le_univ (SubsetWork.asSet mask.value)
  have ha := PrimitiveWork.map_work_le
    (fun x : Fin m => (⟨emb.value[x], 1⟩ : Result (Fin n))) reps.value
    1 (fun _ _ => le_rfl)
  have hreps : reps.value.length = once.value.length * t := by
    exact (congrArg List.length (repeat_value once.value t)).trans (repeatSchedule_length once.value t)
  rw [hreps] at ha
  change emb.work + data.work + queries.work + mask.work + once.work + reps.work + _ ≤ _
  exact schedule_work_arithmetic hm hlen (embeddingVector_work D Q r)
    (gather_work D emb.value) (queriesMask_work Q emb.value)
    (retainedMask_work data.value.edge queries.value r) (maskList_work mask.value)
    (repeat_work once.value t) ha

theorem fullScheduleAt_work_admitted (D : StoredSystem n) (Q : SubsetWork.Mask n)
    (H t : ℕ) (hH : H ≤ n) (ht : t ≤ n) :
    (fullScheduleAt D Q (H * t) t).work ≤ 10000 * (n + 1) ^ 5 := by
  have h := fullScheduleAt_work D Q (H * t) t
  have hp : H * t ≤ n ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hH ht
  have hfirst := Nat.mul_le_mul_right ((n + 1) ^ 3) (Nat.mul_le_mul_left 400
    (Nat.add_le_add_right hp 3))
  have hsecond := Nat.mul_le_mul_right (n + 1) (Nat.mul_le_mul_left 20
    (Nat.pow_le_pow_left (Nat.add_le_add_right ht 1) 2))
  have hb := h.trans (Nat.add_le_add hfirst hsecond)
  nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 4), Nat.zero_le (n ^ 5)]

/-- The measured preparation computes the exact schedule in the local
certificate, using the already materialized numeric calibration. -/
theorem fullScheduleAt_calibrated (D : StoredSystem n) (Q : SubsetWork.Mask n)
    (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w) (t : ℕ)
    (ht : t = Neighborhood.sweeps k H hk w hw) :
    (fullScheduleAt D Q (H * t) t).value =
      Neighborhood.fullSchedule D.system k H hk w hw (SubsetWork.asSet Q) := by
  rw [fullScheduleAt_value]
  unfold retainedSet
  rw [retainedMask_set]
  subst t
  rfl

def singletonMask (x : Fin n) : Result (SubsetWork.Mask n) :=
  PrimitiveWork.vector (fun y => ⟨decide (y = x), 1⟩)

def pairMask (x y : Fin n) : Result (SubsetWork.Mask n) :=
  PrimitiveWork.vector (fun z => ⟨decide (z = x ∨ z = y), 3⟩)

@[simp] theorem singletonMask_set (x : Fin n) :
    SubsetWork.asSet (singletonMask x).value = {x} := by
  ext y
  simp [singletonMask, SubsetWork.mem_asSet]

@[simp] theorem pairMask_set (x y : Fin n) :
    SubsetWork.asSet (pairMask x y).value = {x, y} := by
  ext z
  simp [pairMask, SubsetWork.mem_asSet]

theorem singletonMask_work (x : Fin n) : (singletonMask x).work ≤ 3 * n := by
  simpa only [singletonMask, Nat.reduceAdd, Nat.mul_comm] using
    PrimitiveWork.vector_work_le (fun y : Fin n => (⟨decide (y = x), 1⟩ : Result Bool))
      1 (fun _ => le_rfl)

theorem pairMask_work (x y : Fin n) : (pairMask x y).work ≤ 5 * n := by
  simpa only [pairMask, Nat.reduceAdd, Nat.mul_comm] using
    PrimitiveWork.vector_work_le (fun z : Fin n => (⟨decide (z = x ∨ z = y), 3⟩ : Result Bool))
      3 (fun _ => le_rfl)

def oneSchedule (D : StoredSystem n) (H t : ℕ) (x : Fin n) : Result (List (Fin n)) :=
  let queries := singletonMask x
  let prepared := fullScheduleAt D queries.value (H * t) t
  ⟨prepared.value, queries.work + prepared.work⟩

def twoSchedule (D : StoredSystem n) (H t : ℕ) (x y : Fin n) : Result (List (Fin n)) :=
  let queries := pairMask x y
  let prepared := fullScheduleAt D queries.value (H * t) t
  ⟨prepared.value, queries.work + prepared.work⟩

theorem oneSchedule_value (D : StoredSystem n) (k H : ℕ) (hk : 0 < k) (t : ℕ)
    (ht : t = Neighborhood.sweeps k H hk (ArbitraryLabels.widthThreshold k H)
      (ArbitraryLabels.widthThreshold_pos k H)) (x : Fin n) :
    (oneSchedule D H t x).value = ArbitraryLabels.fullSchedule D.system k H hk {x} := by
  unfold oneSchedule
  rw [fullScheduleAt_calibrated D _ k H hk _ _ t ht, singletonMask_set]
  rfl

theorem twoSchedule_value (D : StoredSystem n) (k H : ℕ) (hk : 0 < k) (t : ℕ)
    (ht : t = Neighborhood.sweeps k H hk (ArbitraryLabels.widthThreshold k H)
      (ArbitraryLabels.widthThreshold_pos k H)) (x y : Fin n) :
    (twoSchedule D H t x y).value = ArbitraryLabels.fullSchedule D.system k H hk {x, y} := by
  unfold twoSchedule
  rw [fullScheduleAt_calibrated D _ k H hk _ _ t ht, pairMask_set]
  rfl

theorem oneSchedule_work (D : StoredSystem n) (H t : ℕ) (hH : H ≤ n) (ht : t ≤ n) (x : Fin n) :
    (oneSchedule D H t x).work ≤ 10010 * (n + 1) ^ 5 := by
  have hm := singletonMask_work x
  have hs := fullScheduleAt_work_admitted D (singletonMask x).value H t hH ht
  change _ + _ ≤ _
  nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 4), Nat.zero_le (n ^ 5)]

theorem twoSchedule_work (D : StoredSystem n) (H t : ℕ) (hH : H ≤ n) (ht : t ≤ n) (x y : Fin n) :
    (twoSchedule D H t x y).work ≤ 10010 * (n + 1) ^ 5 := by
  have hm := pairMask_work x y
  have hs := fullScheduleAt_work_admitted D (pairMask x y).value H t hH ht
  change _ + _ ≤ _
  nlinarith [Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 4), Nat.zero_le (n ^ 5)]

end SortingAdversary.Continuous.NeighborhoodWork
