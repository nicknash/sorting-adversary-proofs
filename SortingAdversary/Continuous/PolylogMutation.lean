import SortingAdversary.Continuous.PolylogStorage
import SortingAdversary.Continuous.RecordInvariant
import SortingAdversary.Continuous.PolylogRows
import SortingAdversary.Continuous.PolylogWallTables

/-!
# Updating the sparse graph and endpoint tables together

Both the cone traversals and the incidence updates read the same old graph.
Bounds for finite row and wall operations compose for each real mutation.
-/

namespace SortingAdversary.Continuous.PolylogMutation

open TreeState FiniteAveraging OrderRegion PolylogWallTables
open PolylogRows (Graph)
open Optimal.PrimitiveWork (Result)
open SortingAdversary.Optimal.GraphBalls (neighbors)

variable {α : Type} {n h : ℕ}

/-- Degree cap on the actual stored incoming and outgoing lists. -/
def Bounded (g : Graph n h) (d : ℕ) : Prop :=
  (∀ x : Fin n, (g.succs.get x.val).value.length ≤ d) ∧
    ∀ x : Fin n, (g.preds.get x.val).value.length ≤ d

theorem bounded_of_degree {g : Graph n h} {E : Fin n → Fin n → Bool} (hg : g.Valid E)
    (d : ℕ) (loop : ∀ x, E x x = false) (degree : ∀ x, (neighbors E x).card ≤ d) :
    Bounded g d := by
  constructor
  · intro x; rw [hg.1]; exact GraphPaths.outgoing_length_le E d loop degree x
  · intro x; rw [hg.2]
    apply GraphPaths.outgoing_length_le (fun a b => E b a) d loop _ x
    intro y
    have eq : neighbors (fun a b => E b a) y = neighbors E y := by
      ext z; simp [Optimal.GraphBalls.mem_neighbors, or_comm]
    rw [eq]; exact degree y

def graphOp (g : Graph n h) (d : ℕ) : Change α n → Result (Graph n h)
  | .arc a b => PolylogRows.add g a b
  | .fix x _ => PolylogRows.erase g d x
  | _ => ⟨g, 1⟩

theorem graphOp_valid (D : System (Fin n) ℚ) (g : Graph n h) (hg : g.Valid D.edge)
    (cap : n ≤ 2^h) (d : ℕ) (bd : Bounded g d) (op : Change α n) (decode : α → ℚ) :
    (graphOp g d op).value.Valid (raw decode D op).edge := by
  cases op with
  | arc a b => exact PolylogRows.add_valid hg cap a b
  | above x c => exact hg
  | below x c => exact hg
  | unchanged => exact hg
  | fix x c =>
    change (PolylogRows.erase g d x).value.Valid (resetCoordinate D x (decode c)).edge
    rw [OneArcRepair.resetCoordinate_edge]
    exact PolylogRows.erase_valid hg cap d bd.1 bd.2 x

theorem graphOp_work (g : Graph n h) (d : ℕ) (bd : Bounded g d) (op : Change α n) :
    (graphOp g d op).work ≤ 2*d*(9*h+3*d+6)+18*h+8*d+13 := by
  cases op with
  | arc a b => exact (PolylogRows.add_work g a b d (bd.1 a) (bd.2 b)).trans (by omega)
  | fix x c => exact (PolylogRows.erase_work g d x (bd.1 x) (bd.2 x)).trans (by omega)
  | above | below | unchanged => simp [graphOp]

/-- One mutation of the two wall tables and the graph's two incidence tables. -/
def updateCore (lt : α → α → Result Bool) (g : Graph n h) (w : Walls α h) (d H : ℕ)
    (zref oref : α) (op : Change α n) : Result (Graph n h × Walls α h) :=
  let b := update lt g.succs g.preds H zref oref w op
  let e := graphOp g d op
  ⟨(e.value,b.value),b.work + e.work + 2⟩

def coreBudget (h d H B : ℕ) :=
  2*((d+1)^H*(13*h+B+12)+5*h+6)+2*d*(9*h+3*d+6)+26*h+8*d+24

theorem updateCore_work (lt : α → α → Result Bool) (B : ℕ) (hc : ∀ a b, (lt a b).work ≤ B)
    (g : Graph n h) (w : Walls α h) (d H : ℕ) (bd : Bounded g d)
    (zref oref : α) (op : Change α n) :
    (updateCore lt g w d H zref oref op).work ≤ coreBudget h d H B := by
  have := graphOp_work g d bd op
  have := update_work lt B hc g.succs g.preds d bd.1 bd.2 H zref oref w op
  dsimp only [updateCore, coreBudget]
  omega

/-- Exact agreement of all four tables with the reference system after oref
mutation. The rank and strict assignment occur only in the specification. -/
theorem updateCore_reference (lt : α → α → Result Bool) (decode : α → ℚ)
    (correct : ∀ a b, (lt a b).value = true ↔ decode a < decode b)
    (g : Graph n h) (w : Walls α h) (d H : ℕ) (zref oref : α)
    (hz : decode zref = 0) (ho : decode oref = 1) (cap : n ≤ 2^h) (bd : Bounded g d)
    (D : System (Fin n) ℚ) (hg : g.Valid D.edge) (hw : aligned decode w D)
    (rank : Fin n → ℕ) (hr : ∀ x y, D.edge x y = true → rank x < rank y)
    (height : ∀ x, rank x < H) (norm : Normalized D)
    (op : Change α n) (valid : permitted D decode op)
    (X : Fin n → ℝ) (feas : (raw decode D op).toReal.StrictlyFeasible X) :
    let r := (updateCore lt g w d H zref oref op).value
    let data := raw decode D op
    let canon := OrderRegion.normalize data (rankOrder (GraphOrder.graphRank data))
    r.1.Valid canon.edge ∧ aligned decode r.2 canon := by
  constructor
  · simpa only [updateCore, normalize_edge] using graphOp_valid D g hg cap d bd op decode
  · apply update_reference lt decode correct H g.succs g.preds zref oref hz ho w D hw cap
      _ _ rank hr height norm op valid X feas
    · intro x y; rw [hg.1, GraphPaths.mem_outgoing]
    · intro x y; rw [hg.2, GraphPaths.mem_outgoing]

section Memory

open Controller
open PolylogStorage (Represents)
abbrev Sparse := PolylogStorage.State

/-- The answer branch first routes the labels and updates the incidence and
endpoint tables. Locations and the node directory are shared unchanged. -/
def recordState (lt : ℕ → ℕ → Result Bool) (s : Sparse n h) (k zref oref : ℕ)
    (q : Query n) (a : Answer) : Result (Sparse n h) :=
  let r := PolylogStorage.route s q
  let next := updateCore lt s.graph s.walls k (ArbitraryLabels.pathHeight k) zref oref (forRecord r.value q a)
  ⟨{s with graph := next.value.1, walls := next.value.2}, r.work + next.work + 2⟩

/-- A restriction deletes its old incident arcs, canonically clips the old
node's neighbors, and moves the label's cursor to the correct shared child. -/
def refineState (lt : ℕ → ℕ → Result Bool) (s : Sparse n h) (k zref oref : ℕ)
    (x : Fin n) (c : ℕ) : Result (Sparse n h) :=
  let next := updateCore lt s.graph s.walls k (ArbitraryLabels.pathHeight k) zref oref (.fix x c)
  let cur := PolylogStorage.moveCursor s x c
  ⟨{ cur.value with graph := next.value.1, walls := next.value.2 }, next.work + cur.work + 2⟩

theorem recordState_work (lt : ℕ → ℕ → Result Bool) (B : ℕ) (cost : ∀ a b, (lt a b).work ≤ B)
    (s : Sparse n h) (k zref oref : ℕ) (bd : Bounded s.graph k) (q : Query n) (a : Answer) :
    (recordState lt s k zref oref q a).work ≤
      coreBudget h k (ArbitraryLabels.pathHeight k) B + h*(8*h+9)+16*h+18 := by
  have := PolylogStorage.route_work s q
  have := updateCore_work lt B cost s.graph s.walls k (ArbitraryLabels.pathHeight k) bd zref oref
    (forRecord (PolylogStorage.route s q).value q a)
  dsimp only [recordState]; omega

theorem refineState_work (lt : ℕ → ℕ → Result Bool) (B : ℕ) (cost : ∀ a b, (lt a b).work ≤ B)
    (s : Sparse n h) (k zref oref : ℕ) (bd : Bounded s.graph k) (x : Fin n) (c : ℕ) :
    (refineState lt s k zref oref x c).work ≤ coreBudget h k (ArbitraryLabels.pathHeight k) B + 36*h+20 := by
  have := PolylogStorage.moveCursor_work s x c
  have := updateCore_work lt B cost s.graph s.walls k (ArbitraryLabels.pathHeight k) bd zref oref (.fix x c)
  dsimp only [refineState]; omega

private theorem underlying_feasible (D : System (Fin n) ℚ) (order : List (Fin n))
    (positive : 0 < MeasureTheory.volume (region (OrderRegion.normalize D order).toReal)) :
    ∃ X, D.toReal.StrictlyFeasible X := by
  rw [normalizeSystem_toReal, normalize_region] at positive
  exact (volume_pos_iff_nonempty _).mp positive

/-- Pull the state invariants into the common core proof, with the *old*
admissible rank bound. Positivity of the raw update is supplied by the
verified reference move/answer. -/
private theorem core_rep (lt : ℕ → ℕ → Result Bool) (decode : ℕ → ℚ)
    (hc : ∀ a b, (lt a b).value = true ↔ decode a < decode b)
    {s : Sparse n h} {nodes : List (List ℕ)} {M : Memory n} (hs : Represents s nodes M decode)
    {k : ℕ} (geo : Admissible k M) (zref oref : ℕ) (hz : decode zref = 0) (ho : decode oref = 1)
    (cap : n ≤ 2^h) (op : Change ℕ n) (valid : permitted M.tree.system decode op)
    (feas : ∃ X, (raw decode M.tree.system op).toReal.StrictlyFeasible X) :
    let c := (updateCore lt s.graph s.walls k (ArbitraryLabels.pathHeight k) zref oref op).value
    let data := raw decode M.tree.system op
    let canon := OrderRegion.normalize data (rankOrder (GraphOrder.graphRank data))
    c.1.Valid canon.edge ∧ aligned decode c.2 canon := by
  obtain ⟨rank,hr,hh⟩ := geo.rank
  obtain ⟨X,hX⟩ := feas
  apply updateCore_reference lt decode hc s.graph s.walls k _ zref oref hz ho cap
    (bounded_of_degree hs.graph k geo.noLoop geo.degree) _ hs.graph hs.walls rank hr
    (fun y => hh y) _ op valid X hX
  intro x y he
  have hb := geo.normalized x y he
  exact ⟨(Rat.cast_le (K := ℝ)).mp hb.1, (Rat.cast_le (K := ℝ)).mp hb.2⟩

theorem recordState_represents (lt : ℕ → ℕ → Result Bool) (decode : ℕ → ℚ)
    (hc : ∀ a b, (lt a b).value = true ↔ decode a < decode b) (inj : Function.Injective decode)
    {s : Sparse n h} {nodes : List (List ℕ)} {M : Memory n} (hs : Represents s nodes M decode)
    {k : ℕ} (geo : Admissible k M) (zref oref : ℕ) (hz : decode zref = 0) (ho : decode oref = 1)
    (cap : n ≤ 2^h) (q : Query n) (a : Answer) (post : Geometric (recorded M q a)) :
    Represents (recordState lt s k zref oref q a).value nodes (recorded M q a) decode := by
  let r := (PolylogStorage.route s q).value
  let cmd := forRecord r q a
  have e : raw decode M.tree.system cmd = (record M.tree q a).system := by
    rw [show raw decode M.tree.system cmd = _ from raw_record decode M.tree.system r q a,
      show PolylogRouting.decodeRoute decode r = _ from PolylogStorage.route_value hs inj q]
    rfl
  have v : permitted M.tree.system decode cmd := by
    cases hr : r <;> cases a <;> simp [cmd, hr, forRecord, permitted]
  have p : ∃ X, (raw decode M.tree.system cmd).toReal.StrictlyFeasible X := by
    rw [e]; exact underlying_feasible _ (answerOrder M q a) post.positive
  have core := core_rep lt decode hc hs geo zref oref hz ho cap cmd v p
  dsimp only at core
  rw [e] at core
  exact ⟨core.1,core.2,hs.directory,hs.located⟩

theorem refineState_represents (lt : ℕ → ℕ → Result Bool) (decode : ℕ → ℚ)
    (hc : ∀ a b, (lt a b).value = true ↔ decode a < decode b)
    {s : Sparse n h} {nodes : List (List ℕ)} {M : Memory n} (hs : Represents s nodes M decode)
    {k : ℕ} (geo : Admissible k M) (zref oref : ℕ) (hz : decode zref = 0) (ho : decode oref = 1)
    (cap : n ≤ 2^h) (x : Fin n) (c : ℕ) (addr : c < 2^h)
    (room : s.directory.next < 2^h) (depth : (M.tree.location x).length + 1 < 2^h)
    (dyadic : (DyadicAnchor.ofRat (decode c)).coordinate = decode c)
    (inside : M.tree.system.lower x < decode c ∧ decode c < M.tree.system.upper x) :
    let m := makeMove M x (decode c)
    ∃ more : List (List ℕ), more.length ≤ 1 ∧
      Represents (refineState lt s k zref oref x c).value (nodes ++ more) (applyMove M m) decode := by
  let m := makeMove M x (decode c)
  have anchor : m.anchor.coordinate = decode c := dyadic
  have pos : Geometric (applyMove M m) := geo.toGeometric.applyMove m (anchor ▸ inside) rfl
  have feas : ∃ X, (resetCoordinate M.tree.system x (decode c)).toReal.StrictlyFeasible X := by
    rw [← anchor]
    exact underlying_feasible _ m.order pos.positive
  have core := core_rep lt decode hc hs geo zref oref hz ho cap (.fix x c) ⟨inside,geo.noLoop x⟩ feas
  dsimp only [raw] at core
  obtain ⟨more,size,dir,loc⟩ := PolylogStorage.moveCursor_spec hs cap x c addr room depth
  refine ⟨more,size,?_,?_,dir,?_⟩
  · let upd := (updateCore lt s.graph s.walls k (ArbitraryLabels.pathHeight k) zref oref (.fix x c)).value
    change upd.1.Valid (OrderRegion.normalize (resetCoordinate M.tree.system x m.anchor.coordinate) m.order).edge
    rw [normalize_edge, anchor]
    simpa only [normalize_edge] using core.1
  · let upd := (updateCore lt s.graph s.walls k (ArbitraryLabels.pathHeight k) zref oref (.fix x c)).value
    change aligned decode upd.2 (OrderRegion.normalize (resetCoordinate M.tree.system x m.anchor.coordinate)
      (rankOrder (GraphOrder.graphRank (resetCoordinate M.tree.system x m.anchor.coordinate))))
    rw [anchor]
    exact core.2
  · intro y
    obtain ⟨p,hp,py⟩ := loc y
    refine ⟨p,hp,?_⟩
    by_cases e : y = x <;> simp_all [applyMove, TreeState.normalize, refineAt, m, makeMove]

end Memory

end SortingAdversary.Continuous.PolylogMutation
