import SortingAdversary.Continuous.PolylogGraph
import SortingAdversary.Continuous.GraphScanWork
import SortingAdversary.Continuous.OneArcRepair

/-!
# Finding a sparse repair after a single insertion

Every newly forbidden path contains the inserted tail. The search enumerates
its predecessor cone, then paths starting in that cone, using the stored
outgoing adjacency rows. Taking the least candidate preserves the reference
controller's lexicographic tie break, even when the traversal repeats a start.
-/

namespace SortingAdversary.Continuous.PolylogRepair

open Optimal Optimal.GraphBalls Optimal.SparseRepairGraph
open EnclosureWork (flatMap flatMap_value flatMap_work)
open OneArcRepair

variable {n : ℕ}
abbrev Rows (n : ℕ) := Fin n → List (Fin n)

/-- Finite paths with exactly `h` more vertices beyond `x`. One unit reads
the adjacency-list pointer. The measured list routines charge for each cell. -/
def tails (next : Rows n) : ℕ → Fin n → PrimitiveWork.Result (List (List (Fin n)))
  | 0, _ => ⟨[[]], 2⟩
  | h+1, x =>
    let r := flatMap (fun y =>
      let t := tails next h y
      let m := PrimitiveWork.map (fun p => ⟨y :: p, 1⟩) t.value
      ⟨m.value, t.work + m.work⟩) (next x)
    ⟨r.value, r.work + 1⟩

variable (E : Fin n → Fin n → Bool) (next : Rows n)
  (rows : ∀ x, next x = GraphPaths.outgoing E x)

include rows in
theorem tails_value (h : ℕ) (x : Fin n) :
    (tails next h x).value = GraphPaths.pathsFrom E h x := by
  induction h generalizing x with
  | zero => rfl
  | succ h ih => simp only [tails, flatMap_value, PrimitiveWork.map_value, ih, rows, GraphPaths.pathsFrom]

def tailCost (d : ℕ) : ℕ → ℕ
  | 0 => 2
  | h+1 => d * (tailCost d h + 4*d^h + 3) + 2

include rows in
theorem tails_work (d : ℕ) (hloop : ∀ x, E x x = false)
    (deg : ∀ x, (neighbors E x).card ≤ d) (h : ℕ) (x : Fin n) :
    (tails next h x).work ≤ tailCost d h := by
  induction h generalizing x with
  | zero => exact le_rfl
  | succ h ih =>
    let branch := fun y : Fin n =>
      let t := tails next h y
      let m := PrimitiveWork.map (fun p => ⟨y :: p, 1⟩) t.value
      (⟨m.value, t.work + m.work⟩ : PrimitiveWork.Result (List (List (Fin n))))
    have hl y : (tails next h y).value.length ≤ d^h := by
      rw [tails_value E next rows]
      exact GraphPaths.pathsFrom_length_le E d hloop deg h y
    have hbw (y : Fin n) : (branch y).work ≤ tailCost d h + 3*d^h + 1 := by
      have hm := PrimitiveWork.map_work_le (fun p : List (Fin n) =>
        (⟨y :: p, 1⟩ : PrimitiveWork.Result (List (Fin n)))) (tails next h y).value 1 (fun _ _ => le_rfl)
      dsimp only [branch]
      have := ih y
      have := hl y
      omega
    have hbl (y : Fin n) : (branch y).value.length ≤ d^h := by
      simpa only [branch, PrimitiveWork.map_value, List.length_map] using hl y
    have hf := flatMap_work branch (next x) _ _ (fun y _ => hbw y) (fun y _ => hbl y)
    have hn : (next x).length ≤ d := by rw [rows]; exact GraphPaths.outgoing_length_le E d hloop deg x
    change (flatMap branch (next x)).work + 1 ≤ _
    apply (Nat.add_le_add_right hf 1).trans
    change _ ≤ d * (tailCost d h + 4*d^h + 3) + 2
    apply Nat.add_le_add_right _ 2
    exact Nat.mul_le_mul hn (by omega)

def fromStarts (next : Rows n) (h : ℕ) (starts : List (Fin n)) :
    PrimitiveWork.Result (List (List (Fin n))) :=
  flatMap (fun x =>
    let t := tails next h x
    let m := PrimitiveWork.map (fun p => ⟨x::p,1⟩) t.value
    ⟨m.value,t.work + m.work⟩) starts

include rows in
theorem fromStarts_value (h : ℕ) (starts : List (Fin n)) :
    (fromStarts next h starts).value =
      starts.flatMap (fun x => (GraphPaths.pathsFrom E h x).map (x :: ·)) := by
  simp only [fromStarts, flatMap_value, PrimitiveWork.map_value, tails_value E next rows]

include rows in
theorem fromStarts_work (d : ℕ) (hloop : ∀ x, E x x = false)
    (deg : ∀ x, (neighbors E x).card ≤ d) (h : ℕ) (starts : List (Fin n)) :
    (fromStarts next h starts).work ≤ starts.length * (tailCost d h + 4*d^h + 3) + 1 := by
  let f := fun x : Fin n =>
    let t := tails next h x
    let m := PrimitiveWork.map (fun p => ⟨x::p,1⟩) t.value
    (⟨m.value,t.work + m.work⟩ : PrimitiveWork.Result (List (List (Fin n))))
  have hl x : (tails next h x).value.length ≤ d^h := by
    rw [tails_value E next rows]; exact GraphPaths.pathsFrom_length_le E d hloop deg h x
  have hw (x : Fin n) : (f x).work ≤ tailCost d h + 3*d^h + 1 := by
    have hm := PrimitiveWork.map_work_le (fun p : List (Fin n) =>
      (⟨x::p,1⟩ : PrimitiveWork.Result (List (Fin n)))) (tails next h x).value 1 (fun _ _ => le_rfl)
    have := tails_work E next rows d hloop deg h x
    have := hl x
    dsimp only [f]
    omega
  have hL (x : Fin n) : (f x).value.length ≤ d^h := by
    simpa [f] using hl x
  exact (flatMap_work f starts _ _ (fun x _ => hw x) (fun x _ => hL x)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1)

private theorem chain_reaches {E : Fin n → Fin n → Bool} {x u : Fin n} {p : List (Fin n)}
    (hc : (x::p).IsChain (fun a b => E a b = true)) (hm : u ∈ x::p) :
    Relation.ReflTransGen (fun a b => E a b = true) x u := by
  induction p generalizing x with
  | nil =>
    obtain rfl : u = x := by simpa using hm
    exact .refl
  | cons y ys ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact .refl
    · have hh := List.isChain_cons_cons.mp hc
      exact (ih hh.2 hm).head hh.1

private theorem min_eq_of_members {α : Type*} [LinearOrder α] {s t : List α}
    (hm : ∀ x, x ∈ s ↔ x ∈ t) : s.min? = t.min? := by
  cases h : s.min? with
  | none =>
    symm
    apply List.min?_eq_none_iff.mpr
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    have hs := List.min?_eq_none_iff.mp h
    simpa [hs] using (hm x).mpr hx
  | some x =>
    symm
    have hx := List.min?_eq_some_iff.mp h
    exact List.min?_eq_some_iff.mpr ⟨(hm x).mp hx.1, fun y hy => hx.2 y ((hm y).mpr hy)⟩

/-- Search paths of `h+1` vertices with a predecessor-cone fuel `R`. -/
def firstPath (prev next : Rows n) (R h : ℕ) (u : Fin n) :
    PrimitiveWork.Result (Option (List (Fin n))) :=
  let seeds := PolylogGraph.emit prev R u ([],0)
  let paths := fromStarts next h seeds.1
  let best := GraphScanWork.minimum paths.value
  ⟨best.value, seeds.2 + paths.work + best.work⟩

include rows in
theorem firstPath_value (old : Fin n → Fin n → Bool) (u v : Fin n)
    (edge : E = addRow old u v) (prev : Rows n) (rank : Fin n → ℕ)
    (pred : ∀ x y, y ∈ prev x ↔ E y x = true) (hr : ∀ x y, E x y = true → rank x < rank y)
    (R h : ℕ) (bound : ∀ x, rank x < R) (height : HeightBelow old (h+1)) :
    (firstPath prev next R h u).value = GraphPaths.firstPath E (h+1) := by
  rw [firstPath, GraphPaths.firstPath]
  change (GraphScanWork.minimum _).value = _
  rw [GraphScanWork.minimum_value, fromStarts_value E next rows, (PolylogGraph.emit_spec ..).1,
    List.append_nil]
  apply min_eq_of_members
  intro p
  constructor
  · intro hm
    obtain ⟨x,_,hx⟩ := List.mem_flatMap.mp hm
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
    exact List.mem_flatMap.mpr ⟨x, by simp, List.mem_map.mpr ⟨t,ht,rfl⟩⟩
  · intro hm
    obtain ⟨len,chain⟩ := (GraphPaths.mem_paths E _ p).mp hm
    cases p with
    | nil => simp at len
    | cons x t =>
      have hl y : E y y = false := Bool.eq_false_iff.mpr (fun hh => (hr y y hh).false)
      have hu : u ∈ x :: t := by
        apply (path_contains_new_endpoints old u v (h+1) height _ _ len.ge).1
        simpa only [← edge] using path_of_chain E hl chain
      have rev : Relation.ReflTransGen (fun a b => b ∈ prev a) u x := by
        have hh := chain_reaches chain hu
        clear hu edge
        induction hh with
        | refl => exact .refl
        | @tail y z _ hy ih => exact ih.head ((pred z y).mpr hy)
      apply List.mem_flatMap.mpr
      refine ⟨x, PolylogGraph.reaches_mem_visit prev rank (fun a b hp => hr b a ((pred a b).mp hp))
        rev R (bound u).le, List.mem_map.mpr ⟨t,?_,rfl⟩⟩
      exact (GraphPaths.mem_pathsFrom E h x t).mpr ⟨by simpa using len, chain⟩

private theorem flat_length (f : Fin n → List (List (Fin n))) (xs : List (Fin n)) (L : ℕ)
    (hb : ∀ x, (f x).length ≤ L) : (xs.flatMap f).length ≤ xs.length*L := by
  induction xs with
  | nil => simp
  | cons x xs ih => simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add (hb x) ih

def pathCost (d R h : ℕ) :=
  3*(d+1)^R + ((d+1)^R * (tailCost d h + 4*d^h + 3) + 1) +
    ((d+1)^R * d^h * (5*(h+1)+4) + 1)

include rows in
theorem firstPath_work (prev : Rows n) (d R h : ℕ) (u : Fin n)
    (hloop : ∀ x, E x x = false) (degree : ∀ x, (neighbors E x).card ≤ d)
    (hd : ∀ x, (prev x).length ≤ d) : (firstPath prev next R h u).work ≤ pathCost d R h := by
  let seeds := PolylogGraph.emit prev R u ([],0)
  have se : seeds.1 = PolylogGraph.visit prev R u := by simpa [seeds] using (PolylogGraph.emit_spec prev R u [] 0).1
  have sl : seeds.1.length ≤ (d+1)^R := se ▸ PolylogGraph.visit_length_le prev d hd R u
  have sw := PolylogGraph.emit_work_le prev d hd R u
  let candidates := fromStarts next h seeds.1
  have cw := fromStarts_work E next rows d hloop degree h seeds.1
  have cv := fromStarts_value E next rows h seeds.1
  have cl : candidates.value.length ≤ seeds.1.length * d^h := by
    rw [show candidates.value = _ from cv]
    apply flat_length
    intro x
    simpa using GraphPaths.pathsFrom_length_le E d hloop degree h x
  have mw := GraphScanWork.minimum_work candidates.value (h+1) (by
    intro p hp
    rw [show candidates.value = _ from cv] at hp
    obtain ⟨x,_,hx⟩ := List.mem_flatMap.mp hp
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
    simp [(GraphPaths.mem_pathsFrom E h x t).mp ht |>.1])
  exact Nat.add_le_add (Nat.add_le_add sw (cw.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ sl) 1)))
    (mw.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (cl.trans (Nat.mul_le_mul_right _ sl))) 1))


/-- Scan the two stored undirected neighbor rows, and select the least
endpoint whose degree equals the threshold. -/
def degreeChoice (adj : Rows n) (k : ℕ) (u v : Fin n) : PrimitiveWork.Result (Option (Fin n)) :=
  let rows := GraphScanWork.filter (fun x =>
    let count := PrimitiveWork.count (fun _ : Fin n => ⟨true,0⟩) (adj x)
    ⟨decide (count.value = k), count.work + 2⟩) [u,v]
  ⟨rows.value.min?,rows.work + 3⟩

theorem degreeChoice_value (old : Fin n → Fin n → Bool) (k : ℕ) (u v : Fin n)
    (adj : Rows n) (ha : ∀ x, (adj x).length = (neighbors (addRow old u v) x).card)
    (hd : DegreeBelow old k) :
    (degreeChoice adj k u v).value = (List.finRange n).find?
      (fun x => decide ((neighbors (addRow old u v) x).card = k)) := by
  have allRows (x : Fin n) : (adj x).filter (fun _ => true) = adj x := List.filter_eq_self.mpr (by simp)
  let P := fun x => decide ((neighbors (addRow old u v) x).card = k)
  have hsorted := ((List.sortedLT_finRange n).pairwise.filter P).imp
    (fun {a b : Fin n} (h : a < b) => min_eq_left h.le)
  rw [← List.head?_filter, ← List.min?_eq_head? hsorted]
  change (degreeChoice adj k u v).value = ((List.finRange n).filter P).min?
  simp only [degreeChoice, GraphScanWork.filter_value, PrimitiveWork.count_value,
    allRows, ha]
  apply min_eq_of_members
  intro x
  simp only [List.mem_filter, List.mem_cons, List.not_mem_nil, or_false, List.mem_finRange,
    true_and, decide_eq_true_eq, P]
  constructor
  · exact And.right
  · exact fun hx => ⟨degree_witness_is_endpoint old u v k hd x hx.ge,hx⟩

theorem degreeChoice_work (adj : Rows n) (k : ℕ) (u v : Fin n) (d : ℕ)
    (hd : ∀ x, (adj x).length ≤ d) : (degreeChoice adj k u v).work ≤ 6*d+14 := by
  let f := fun x =>
    let c := PrimitiveWork.count (fun _ : Fin n => ⟨true,0⟩) (adj x)
    (⟨decide (c.value = k),c.work+2⟩ : PrimitiveWork.Result Bool)
  have hc x := PrimitiveWork.count_work_le (fun _ : Fin n => ⟨true,0⟩) (adj x) 0 (fun _ _ => le_rfl)
  have hf : ∀ x ∈ [u,v], (f x).work ≤ 3*d+3 := by
    intro x _
    dsimp only [f]
    have := hc x
    have := hd x
    omega
  have ht := GraphScanWork.filter_work f [u,v] _ hf
  change (GraphScanWork.filter f [u,v]).work + 3 ≤ _
  simp only [List.length_cons, List.length_nil] at ht
  omega

/-- A stage cost expressible with addition, multiplication, and exponentiation. -/
def repairBound (d R : ℕ) : ℕ :=
  3*(d+1)^R + ((d+1)^R * ((8*(d+1))^(R+1) + 4*(d+1)^R + 3) + 1) +
    ((d+1)^R*(d+1)^R*(5*(R+1)+4) + 1) + (6*d+14)

private theorem tailCost_power (d h : ℕ) : tailCost d h ≤ (8*(d+1))^(h+1) := by
  induction h with
  | zero => simp [tailCost]; omega
  | succ h ih =>
    let A := 8*(d+1)
    have hp : 1 ≤ A^(h+1) := Nat.one_le_pow _ _ (by dsimp [A]; omega)
    have hd : d^h ≤ A^(h+1) :=
      (Nat.pow_le_pow_left (by dsimp [A]; omega : d ≤ A) h).trans
        (Nat.pow_le_pow_right (by dsimp [A]; omega) (Nat.le_succ h))
    change d*(tailCost d h + 4*d^h + 3)+2 ≤ A^((h+1)+1)
    rw [pow_succ]
    have hm := Nat.mul_le_mul_left d (show tailCost d h + 4*d^h + 3 ≤ 8*A^(h+1) by
      change tailCost d h ≤ A^(h+1) at ih
      omega)
    change _ ≤ _ * (8*(d+1))
    nlinarith

theorem pathCost_closed (d R h : ℕ) (hr : h ≤ R) :
    pathCost d R h + (6*d+14) ≤ repairBound d R := by
  have t := (tailCost_power d h).trans (Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right hr 1))
  have e : d^h ≤ (d+1)^R := (Nat.pow_le_pow_left (Nat.le_succ d) h).trans
    (Nat.pow_le_pow_right (by omega) hr)
  unfold pathCost repairBound
  gcongr

open Optimal.CappedArithmetic

/-- An optional stage-budget component covering both local repair scans. -/
def repairRecipe : Expr :=
  let d := UniformStages.Recipe.degree
  let R := UniformStages.Recipe.height
  let B := Expr.pow (.add d (.lit 1)) R
  let T := Expr.pow (.mul (.lit 8) (.add d (.lit 1))) (.add R (.lit 1))
  .add (.add (.add (.mul (.lit 3) B)
    (.add (.mul B (.add (.add T (.mul (.lit 4) B)) (.lit 3))) (.lit 1)))
    (.add (.mul (.mul B B) (.add (.mul (.lit 5) (.add R (.lit 1))) (.lit 4))) (.lit 1)))
    (.add (.mul (.lit 6) d) (.lit 14))

theorem repairRecipe_value (j : ℕ) : repairRecipe.value j =
    repairBound (UniformStages.degree j) (ArbitraryLabels.pathHeight (UniformStages.degree j)) := rfl

end SortingAdversary.Continuous.PolylogRepair
