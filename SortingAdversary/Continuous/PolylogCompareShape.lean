import SortingAdversary.Continuous.PolylogMutation
import SortingAdversary.Continuous.PolylogRepair

/-! # A row-size invariant throughout one stored comparison -/
namespace SortingAdversary.Continuous.PolylogCompareWork

open Optimal Optimal.GraphBalls Optimal.SparseRepairGraph
open PolylogRows (Graph)
open PolylogMutation PolylogWallTables PolylogRepair

variable {n t : ℕ}

def Shape (g : Graph n t) (d : ℕ) : Prop :=
  ∃ E : Fin n → Fin n → Bool, g.Valid E ∧ (∀ x, E x x = false) ∧ ∀ x, (neighbors E x).card ≤ d

theorem Shape.mono {g : Graph n t} {d k : ℕ} (sh : Shape g d) (h : d ≤ k) : Shape g k := by
  obtain ⟨E,hg,hl,hd⟩ := sh
  exact ⟨E,hg,hl,fun x => (hd x).trans h⟩

theorem Shape.bounded {g : Graph n t} {d : ℕ} (sh : Shape g d) : Bounded g d := by
  obtain ⟨E,hg,hl,hd⟩ := sh
  exact bounded_of_degree hg d hl hd

theorem Shape.erase {g : Graph n t} {d k : ℕ} (sh : Shape g d) (small : d ≤ k)
    (cap : n ≤ 2^t) (x : Fin n) : Shape (PolylogRows.erase g k x).value d := by
  obtain ⟨E,hg,hl,hd⟩ := sh
  have bd := bounded_of_degree hg k hl (fun x => (hd x).trans small)
  refine ⟨eraseVertex E x,PolylogRows.erase_valid hg cap k bd.1 bd.2 x,fun y => by simp [eraseVertex,hl],?_⟩
  intro y
  exact (Finset.card_le_card (neighbors_mono _ _ (fun a b h => (Bool.and_eq_true_iff.mp h).1) y)).trans (hd y)

theorem Shape.add {g : Graph n t} {d : ℕ} (sh : Shape g d) (cap : n ≤ 2^t)
    (x y : Fin n) (hne : x ≠ y) : Shape (PolylogRows.add g x y).value (d+1) := by
  obtain ⟨E,hg,hl,hd⟩ := sh
  refine ⟨addRow E x y,PolylogRows.add_valid hg cap x y,?_,addRow_degree_le E x y d hd⟩
  intro z
  apply Bool.eq_false_iff.mpr
  intro e
  rcases (addRow_true ..).mp e with e | ⟨e₁,e₂⟩
  · simp [hl] at e
  · exact hne (e₁.symm.trans e₂)

theorem shape_refine {s : Sparse n t} {d k : ℕ} (sh : Shape s.graph d) (small : d ≤ k)
    (cap : n ≤ 2^t) (lt : ℕ → ℕ → PrimitiveWork.Result Bool) (z o : ℕ) (x : Fin n) (c : ℕ) :
    Shape (refineState lt s k z o x c).value.graph d := sh.erase small cap x

theorem shape_record {s : Sparse n t} {d k : ℕ} (sh : Shape s.graph d)
    (cap : n ≤ 2^t) (lt : ℕ → ℕ → PrimitiveWork.Result Bool) (z o : ℕ) (q : Query n) (a : Answer) :
    Shape (recordState lt s k z o q a).value.graph (d+1) := by
  change Shape (graphOp s.graph k (forRecord (PolylogStorage.route s q).value q a)).value (d+1)
  cases (PolylogStorage.route s q).value <;> cases a <;>
    first | exact sh.add cap _ _ q.distinct | exact sh.add cap _ _ (Ne.symm q.distinct)
          | exact sh.mono (Nat.le_succ d)

private theorem path_length {g : Graph n t} {E : Fin n → Fin n → Bool} (valid : g.Valid E)
    (k : ℕ) (u : Fin n) (xs : List (Fin n))
    (hp : (firstPath (prev g) (nextRow g) (ArbitraryLabels.pathHeight k) (2^k-1) u).value = some xs) :
    xs.length = 2^k := by
  simp only [firstPath,GraphScanWork.minimum_value,fromStarts_value E (nextRow g) valid.1] at hp
  obtain ⟨x,_,hx⟩ := List.mem_flatMap.mp (List.min?_eq_some_iff.mp hp).1
  obtain ⟨p,hm,rfl⟩ := List.mem_map.mp hx
  have h := ((GraphPaths.mem_pathsFrom E _ _ p).mp hm).1
  simp only [List.length_cons]
  have ppos : 0 < 2^k := by positivity
  omega

/-- This resource lemma does not require a rank or a geometric state. A
cycle could duplicate one neighbor in the concatenated row, whose length is
still at most twice the degree. The candidate paths have a fixed length. -/
theorem choose_bounds (g : Graph n t) (k : ℕ) (ev : Option (Fin n × Fin n)) (sh : Shape g k) :
    (choose g k ev).work ≤ (repairBound k (ArbitraryLabels.pathHeight k) + 6*k+1)*(8*t+k+8)+2 ∧
      (choose g k ev).value.length ≤ 2^k := by
  obtain ⟨E,hg,hl,hd⟩ := sh
  have bd := bounded_of_degree hg k hl hd
  have ap (x) : (adjacent g x).length ≤ 2*k := by
    simp only [adjacent,List.length_append,prev,nextRow]
    have := bd.1 x
    have := bd.2 x
    omega
  cases ev with
  | none => simp [choose]
  | some uv =>
    obtain ⟨u,v⟩ := uv
    let h := 2^k-1
    let r := ArbitraryLabels.pathHeight k
    let p := firstPath (prev g) (nextRow g) r h u
    have hp := firstPath_work E (nextRow g) hg.1 (prev g) k r h u hl hd bd.2
    have hq := degreeChoice_work (adjacent g) k u v (2*k) ap
    have hH : 2^k ≤ r := Nat.pow_le_pow_right (by decide) (Nat.le_succ k)
    have cap := pathCost_closed k r h (by dsimp [h]; omega)
    have pp : 0 < 2^k := by positivity
    change p.work ≤ _ at hp
    cases hh : p.value with
    | some xs =>
      have len := path_length hg k u xs hh
      change (firstPath (prev g) (nextRow g) (ArbitraryLabels.pathHeight k) (2^k-1) u).value = some xs at hh
      simp only [choose,hh]
      change (p.work+1)*(8*t+k+8)+2 ≤ (repairBound k r+6*k+1)*(8*t+k+8)+2 ∧ _
      exact ⟨Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _,len.le⟩
    | none =>
      change (firstPath (prev g) (nextRow g) (ArbitraryLabels.pathHeight k) (2^k-1) u).value = none at hh
      simp only [choose,hh]
      refine ⟨Nat.add_le_add_right (Nat.mul_le_mul_right _ ?_) _,?_⟩
      · change p.work + _ + 1 ≤ repairBound k r + 6*k+1
        omega
      · cases (degreeChoice (adjacent g) k u v).value <;> simp <;> omega

end SortingAdversary.Continuous.PolylogCompareWork
