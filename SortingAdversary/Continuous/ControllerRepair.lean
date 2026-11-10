import SortingAdversary.Continuous.ControllerLocal
import SortingAdversary.Continuous.RecordInvariant

/-!
# Correctness of the executable repair

The reserved path is refined in its original order. The genuine sequence
of interior moves restores a feasible assignment in the original graph,
which proves that the actual dyadic anchors are distinct. The resulting
path or degree action has the required accounting tariff, and removing an
endpoint of the newly inserted arc restores both strict graph bounds.
-/

namespace SortingAdversary.Continuous.Controller

open FiniteAveraging OrderRegion TreeState TraceAccounting OneArcRepair MeasureTheory
open SortingAdversary.Optimal.GraphBalls

variable {n : ℕ}

def realMoves (ms : List (Move n)) : List (Fin n × ℝ) :=
  ms.map fun m => (m.item, (m.anchor.coordinate : ℝ))

@[simp] theorem realMoves_labels (ms : List (Move n)) :
    (realMoves ms).map Prod.fst = ms.map Move.item := by
  simp [realMoves, List.map_map, Function.comp_def]

theorem pathBatch_admissible (k : ℕ) (hk : 64 ≤ k) (M : Memory n)
    (hM : Admissible k M) (xs : List (Fin n)) :
    Admissible k (pathBatch k M xs).1 := by
  induction xs generalizing M with
  | nil => exact hM
  | cons x xs ih => exact ih _ (anchor_move_spec M k hk hM x).2.2.2.1

theorem pathBatch_steps (k : ℕ) (hk : 64 ≤ k) (M : Memory n)
    (hM : Admissible k M) (xs : List (Fin n)) :
    RefinementSteps M.tree.toReal (realMoves (pathBatch k M xs).2)
      (pathBatch k M xs).1.tree.toReal := by
  induction xs generalizing M with
  | nil => exact .nil _
  | cons x xs ih =>
    let c := ArbitraryLabels.chooseAnchor M.tree.system k x
    let m := makeMove M x c
    have hs := anchor_move_spec M k hk hM x
    have ht := ih (Controller.applyMove M m) hs.2.2.2.1
    have hc : M.tree.toReal.system.lower x < (m.anchor.coordinate : ℝ) ∧
        (m.anchor.coordinate : ℝ) < M.tree.toReal.system.upper x := by
      rw [show m.anchor.coordinate = c from hs.1]
      exact ⟨(Rat.cast_lt (K := ℝ)).mpr hs.2.1, (Rat.cast_lt (K := ℝ)).mpr hs.2.2.1⟩
    rw [applyMove_tree] at ht
    exact .cons M.tree.toReal x (m.anchor.coordinate : ℝ) m.order _ _ (hM.noLoop x) hc ht

theorem pathBatch_tariffs (k : ℕ) (hk : 64 ≤ k) (M : Memory n)
    (hM : Admissible k M) (xs : List (Fin n)) :
    ∀ r ∈ gainRecords M.tree.toReal (pathBatch k M xs).2,
      stopMass k * r.1.1 - 4 ≤ r.2 := by
  induction xs generalizing M with
  | nil => simp [pathBatch, gainRecords]
  | cons x xs ih =>
    let c := ArbitraryLabels.chooseAnchor M.tree.system k x
    let m := makeMove M x c
    have hs := anchor_move_spec M k hk hM x
    intro r hr
    change r ∈ (m.anchor, m.gain M.tree.toReal) ::
      gainRecords (m.apply M.tree.toReal) (pathBatch k (Controller.applyMove M m) xs).2 at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hs.2.2.2.2.le
    · rw [← applyMove_tree] at hr
      exact ih _ hs.2.2.2.1 r hr

theorem pathBatch_anchors_nodup (k : ℕ) (hk : 64 ≤ k) (M : Memory n)
    (hM : Admissible k M) (xs : List (Fin n))
    (hp : xs.IsChain (fun x y => M.tree.system.edge x y = true)) :
    ((pathBatch k M xs).2.map Move.anchor).Nodup := by
  obtain ⟨rank, hrank, _⟩ := hM.rank
  have hn := GraphPaths.path_nodup M.tree.system.edge rank hrank hp
  letI : Trans (Reaches M.tree.toReal.system) (Reaches M.tree.toReal.system)
      (Reaches M.tree.toReal.system) := ⟨Relation.ReflTransGen.trans⟩
  have hreach : xs.Pairwise (Reaches M.tree.toReal.system) :=
    List.isChain_iff_pairwise.mp (hp.imp (fun _ _ h => Relation.ReflTransGen.single h))
  have hsteps := pathBatch_steps k hk M hM xs
  have hfinal := pathBatch_admissible k hk M hM xs
  have hpair := hsteps.anchors_pairwise
    (by simpa only [realMoves_labels, pathBatch_labels] using hn)
    (by simpa only [realMoves_labels, pathBatch_labels] using hreach)
    ((volume_pos_iff_nonempty _).mp hfinal.positive)
  apply List.Nodup.of_map (fun c : DyadicAnchor => (c.coordinate : ℝ))
  apply List.nodup_iff_pairwise_ne.mpr
  have hne := hpair.imp (fun h => ne_of_lt h)
  simpa only [realMoves, List.map_map, Function.comp_def] using hne

theorem pathBatch_valid (k : ℕ) (hk : 64 ≤ k) (M : Memory n)
    (hM : Admissible k M) (xs : List (Fin n))
    (hp : GraphPaths.firstPath M.tree.system.edge (2 ^ k) = some xs)
    (F : Frame n) (hF : M.Represents F) :
    (Action.path (pathBatch k M xs).2).Valid k F := by
  obtain ⟨hlen, hchain, _⟩ := GraphPaths.firstPath_some _ _ _ hp
  apply valid_path_of_tariffs F _ (pathBatch_anchors_nodup k hk M hM xs hchain)
  · have hlabels := congrArg List.length (pathBatch_labels k M xs)
    simpa only [List.length_map, hlen] using hlabels
  · rw [← hF.1]
    exact pathBatch_tariffs k hk M hM xs

theorem repair_valid (k : ℕ) (hk : 64 ≤ k) (M : Memory n)
    (hM : Admissible k M) (F : Frame n) (hF : M.Represents F) :
    Valid k F (repair k M).2 := by
  cases hp : GraphPaths.firstPath M.tree.system.edge (2 ^ k) with
  | some xs =>
    simpa only [repair, hp, Valid, and_true] using pathBatch_valid k hk M hM xs hp F hF
  | none =>
    cases hd : degreeChoice M k with
    | none => simp [repair, hp, hd, Valid]
    | some x =>
      have hdegree : k ≤ (ArcBudget.incident M.tree.system.toReal x).card := by
        rw [← degreeChoice_some M k x hd]
        exact ArcBudget.neighbors_card_le_incident M.tree.system.toReal x
      simpa only [repair, hp, hd, Valid, and_true] using
        anchor_move_valid_degree M k hk hM x F hF hdegree

theorem applyMoves_edge_old (M : Memory n) (ms : List (Move n)) :
    ∀ x y, (Controller.applyMoves M ms).tree.system.edge x y = true →
      M.tree.system.edge x y = true := by
  induction ms generalizing M with
  | nil => exact fun _ _ h => h
  | cons m ms ih =>
    intro x y h
    exact applyMove_edge_old M m x y (ih _ x y h)

theorem pathBatch_edge_old (k : ℕ) (M : Memory n) (xs : List (Fin n)) :
    ∀ x y, (pathBatch k M xs).1.tree.system.edge x y = true →
      M.tree.system.edge x y = true := by
  rw [pathBatch_apply]
  exact applyMoves_edge_old M _

/-- The post-answer repair restores both strict graph bounds. Its only
graph premise is the literal zero-or-one-arc update performed by recording. -/
theorem repair_recorded_ready (k : ℕ) (hk : 64 ≤ k) (M : Memory n)
    (hM : Ready k M) (q : Query n) (a : Answer)
    (hnew : Geometric (recorded M q a)) :
    Ready k (repair k (recorded M q a)).1 := by
  let N := recorded M q a
  have hN : Admissible k N := hM.recordedAdmissible q a hnew
  cases hp : GraphPaths.firstPath N.tree.system.edge (2 ^ k) with
  | some xs =>
    have hbatch := pathBatch_admissible k hk N hN xs
    have hsteps := pathBatch_steps k hk N hN xs
    have hpath : GraphPaths.firstPath N.tree.toReal.system.edge (2 ^ k) =
        some ((realMoves (pathBatch k N xs).2).map Prod.fst) := by
      change GraphPaths.firstPath N.tree.system.edge (2 ^ k) = _
      simpa only [realMoves_labels, pathBatch_labels] using hp
    have hrestore : HeightBelow (pathBatch k N xs).1.tree.system.edge (2 ^ k) ∧
        DegreeBelow (pathBatch k N xs).1.tree.system.edge k := by
      rcases record_edge_cases M q a with he | he | he
      · have hmono := pathBatch_edge_old k N xs
        change N.tree.system.edge = M.tree.system.edge at he
        rw [he] at hmono
        exact ⟨heightBelow_mono _ _ _ hmono hM.height,
          degreeBelow_mono _ _ _ hmono hM.degree⟩
      · exact firstPath_refinement_restores (K := ℝ) M.tree.system.edge q.left q.right (2 ^ k) k
          hM.height hM.degree (s := N.tree.toReal) (s' := (pathBatch k N xs).1.tree.toReal)
          he hN.noLoop hpath hsteps
      · exact firstPath_refinement_restores (K := ℝ) M.tree.system.edge q.right q.left (2 ^ k) k
          hM.height hM.degree (s := N.tree.toReal) (s' := (pathBatch k N xs).1.tree.toReal)
          he hN.noLoop hpath hsteps
    have hout : Ready k (pathBatch k N xs).1 := ⟨hbatch.toGeometric, hrestore.2, hrestore.1⟩
    simpa only [repair, hp, N] using hout
  | none =>
    cases hd : degreeChoice N k with
    | none =>
      have hdegree : DegreeBelow N.tree.system.edge k := by
        intro x
        have hne := (degreeChoice_none N k).mp hd x
        exact lt_of_le_of_ne (hN.degree x) hne
      have hheight := (firstPath_none_iff_heightBelow N.tree.system.edge (2 ^ k) hN.noLoop).mp hp
      have hout : Ready k N := ⟨hN.toGeometric, hdegree, hheight⟩
      simpa only [repair, hp, hd, N] using hout
    | some x =>
      let c := ArbitraryLabels.chooseAnchor N.tree.system k x
      let m := makeMove N x c
      have hs := anchor_move_spec N k hk hN x
      have hc : N.tree.toReal.system.lower x < (m.anchor.coordinate : ℝ) ∧
          (m.anchor.coordinate : ℝ) < N.tree.toReal.system.upper x := by
        rw [show m.anchor.coordinate = c from hs.1]
        exact ⟨(Rat.cast_lt (K := ℝ)).mpr hs.2.1, (Rat.cast_lt (K := ℝ)).mpr hs.2.2.1⟩
      have hsteps : RefinementSteps N.tree.toReal [(x, (m.anchor.coordinate : ℝ))]
          (Controller.applyMove N m).tree.toReal := by
        rw [applyMove_tree]
        exact .cons _ x (m.anchor.coordinate : ℝ) m.order [] _ (hN.noLoop x) hc (.nil _)
      have hdegree := (degreeChoice_some N k x hd).ge
      have hrestore : HeightBelow (Controller.applyMove N m).tree.system.edge (2 ^ k) ∧
          DegreeBelow (Controller.applyMove N m).tree.system.edge k := by
        rcases record_edge_cases M q a with he | he | he
        · have hmono := applyMove_edge_old N m
          change N.tree.system.edge = M.tree.system.edge at he
          rw [he] at hmono
          exact ⟨heightBelow_mono _ _ _ hmono hM.height,
            degreeBelow_mono _ _ _ hmono hM.degree⟩
        · exact degree_refinement_restores (K := ℝ) M.tree.system.edge q.left q.right (2 ^ k) k
            hM.height hM.degree (s := N.tree.toReal) (s' := (Controller.applyMove N m).tree.toReal)
            x (m.anchor.coordinate : ℝ) he hdegree hsteps
        · exact degree_refinement_restores (K := ℝ) M.tree.system.edge q.right q.left (2 ^ k) k
            hM.height hM.degree (s := N.tree.toReal) (s' := (Controller.applyMove N m).tree.toReal)
            x (m.anchor.coordinate : ℝ) he hdegree hsteps
      have hout : Ready k (Controller.applyMove N m) :=
        ⟨hs.2.2.2.1.toGeometric, hrestore.2, hrestore.1⟩
      simpa only [repair, hp, hd, N, m, c] using hout

end SortingAdversary.Continuous.Controller
