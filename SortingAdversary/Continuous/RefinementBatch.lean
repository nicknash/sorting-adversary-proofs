import SortingAdversary.Continuous.TreeVolume

/-!
# Restoring a complete batch of refined coordinates

Undoing the fresh child coordinates recovers a feasible assignment in the
original parent. Thus the anchors chosen while refining a directed path are
strictly ordered and distinct, even though earlier moves erased some of the
path's arcs. Every move includes the actual optional normalization pass.
-/

namespace SortingAdversary.Continuous.TreeState

open FiniteAveraging OrderRegion

variable {n : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def restoreMoves (moves : List (Fin n × K)) (Y : Fin n → K) : Fin n → K :=
  moves.foldr (fun m X => Function.update X m.1 m.2) Y

/-- A concrete sequence of interior refinements, with the normalization
order recorded at each step. This relation only describes local mutations. -/
inductive RefinementSteps : State n K → List (Fin n × K) → State n K → Prop
  | nil (s : State n K) : RefinementSteps s [] s
  | cons (s : State n K) (x : Fin n) (c : K) (order : List (Fin n))
      (moves : List (Fin n × K)) (s' : State n K)
      (hxx : s.system.edge x x = false)
      (hc : s.system.lower x < c ∧ c < s.system.upper x)
      (tail : RefinementSteps (normalize (refineAt s x c) order) moves s') :
      RefinementSteps s ((x, c) :: moves) s'

theorem RefinementSteps.restore_feasible {s s' : State n K}
    {moves : List (Fin n × K)} (h : RefinementSteps s moves s')
    {Y : Fin n → K} (hY : s'.system.StrictlyFeasible Y) :
    s.system.StrictlyFeasible (restoreMoves moves Y) := by
  induction h with
  | nil s => exact hY
  | cons s x c order moves s' hxx hc tail ih =>
    have hN := (normalize_feasible_iff (refineAt s x c).system order _).mp (ih hY)
    exact ((resetCoordinate_feasible_iff s.system x c hxx hc _).mp hN).2

theorem restoreMoves_at (moves : List (Fin n × K)) (Y : Fin n → K)
    (hn : (moves.map Prod.fst).Nodup) (x : Fin n) (c : K) (hx : (x, c) ∈ moves) :
    restoreMoves moves Y x = c := by
  induction moves with
  | nil => simp at hx
  | cons m ms ih =>
    have hn' : m.1 ∉ ms.map Prod.fst ∧ (ms.map Prod.fst).Nodup := by simpa using hn
    rcases List.mem_cons.mp hx with he | he
    · cases he
      simp [restoreMoves]
    · have hxm : x ≠ m.1 := by
        intro hxm
        apply hn'.1
        rw [← hxm]
        exact List.mem_map.mpr ⟨(x, c), he, rfl⟩
      simpa [restoreMoves, Function.update_of_ne hxm] using ih hn'.2 he

theorem feasible_reaches_le (D : System (Fin n) K) {X : Fin n → K}
    (hX : D.StrictlyFeasible X) {x y : Fin n} (hxy : Reaches D x y) : X x ≤ X y := by
  induction hxy with
  | refl => exact le_rfl
  | tail hxy hyz ih => exact ih.trans (hX.2 _ _ hyz).le

theorem feasible_reaches_lt (D : System (Fin n) K) {X : Fin n → K}
    (hX : D.StrictlyFeasible X) {x y : Fin n} (hne : x ≠ y)
    (hxy : Reaches D x y) : X x < X y := by
  cases hxy with
  | refl => exact (hne rfl).elim
  | tail hxy hyz => exact (feasible_reaches_le D hX hxy).trans_lt (hX.2 _ _ hyz)

/-- Every earlier/later pair on the reserved original path has increasing
anchors, regardless of which of its arcs survive the intermediate states. -/
theorem RefinementSteps.anchors_pairwise {s s' : State n K}
    {moves : List (Fin n × K)} (h : RefinementSteps s moves s')
    (hn : (moves.map Prod.fst).Nodup)
    (hp : (moves.map Prod.fst).Pairwise (Reaches s.system))
    (hne : ∃ Y, s'.system.StrictlyFeasible Y) :
    (moves.map Prod.snd).Pairwise (· < ·) := by
  obtain ⟨Y, hY⟩ := hne
  have hX := h.restore_feasible hY
  have hnp := List.nodup_iff_pairwise_ne.mp hn
  rw [List.pairwise_map] at hp hnp ⊢
  have hboth := hnp.and hp
  apply List.Pairwise.imp_of_mem ?_ hboth
  intro a b ha hb hab
  have hc := feasible_reaches_lt s.system hX hab.1 hab.2
  simpa only [restoreMoves_at moves Y hn a.1 a.2 ha,
    restoreMoves_at moves Y hn b.1 b.2 hb] using hc

end SortingAdversary.Continuous.TreeState
