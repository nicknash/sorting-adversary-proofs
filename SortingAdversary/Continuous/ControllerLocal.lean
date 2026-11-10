import SortingAdversary.Continuous.ControllerInvariant
import SortingAdversary.Continuous.ControllerSemantics
import SortingAdversary.Continuous.ArbitraryLabelProofs
import SortingAdversary.Continuous.TraceGuarantees

/-!
# Local guarantees at the actual controller calls

Routing preserves query orientation, including the reversed right-free
threshold branch. Actual refinement values decode back to their proved
dyadic anchors. The resulting concrete moves preserve the controller
invariants and satisfy the density tariffs consumed by trace accounting.
-/

namespace SortingAdversary.Continuous.Controller

open FiniteAveraging OrderRegion TreeState Density MeasureTheory Set
open TraceAccounting (Move Frame Action)

variable {n : ℕ}

theorem route_real (M : Memory n) (q : Query n) :
    route (M.tree.toReal.location q.left) (M.tree.toReal.location q.right) =
      (route (M.tree.location q.left) (M.tree.location q.right)).toReal :=
  TreeState.route_toReal _ _

theorem attempt_anchorAnswer (M : Memory n) (k : ℕ) (q : Query n) (a : Answer)
    (h : attempt M k q = .answer a) :
    (route (M.tree.toReal.location q.left) (M.tree.toReal.location q.right)).AnchorAnswer a := by
  rw [route_real]
  cases hr : route (M.tree.location q.left) (M.tree.location q.right) with
  | coordinates => trivial
  | leftFree c => trivial
  | rightFree c => trivial
  | anchors c d =>
    have hne := route_anchors_distinct _ _ hr
    simp only [attempt, hr] at h
    by_cases hcd : c < d
    · simp only [if_pos hcd, LocalSelection.Result.answer.injEq] at h
      subst a
      change (c : ℝ) < (d : ℝ)
      exact_mod_cast hcd
    · simp only [if_neg hcd, LocalSelection.Result.answer.injEq] at h
      subst a
      change (d : ℝ) < (c : ℝ)
      exact_mod_cast (lt_of_le_of_ne (le_of_not_gt hcd) hne.symm)

/-- Every actual answer has the required original routing-event mass and,
in the fixed-anchor case, agrees with the order already stored in the paths. -/
theorem attempt_answer_probability (M : Memory n) (k : ℕ) (hk : 0 < k)
    (hM : Geometric M) (q : Query n) (a : Answer) (h : attempt M k q = .answer a) :
    (route (M.tree.toReal.location q.left) (M.tree.toReal.location q.right)).AnchorAnswer a ∧
      answerRetained k ≤ (uniformMeasure M.tree.system.toReal).real
        {X | (route (M.tree.toReal.location q.left) (M.tree.toReal.location q.right)).Holds
          (X q.left) (X q.right) a} := by
  have ha := attempt_anchorAnswer M k q a h
  refine ⟨ha, ?_⟩
  cases hr : route (M.tree.location q.left) (M.tree.location q.right) with
  | coordinates =>
    have hs : ArbitraryLabels.select M.tree.system k q.left q.right = .answer a := by
      simpa only [attempt, hr] using h
    have hp := ArbitraryLabels.select_probability M.tree.system k hk hM.noLoop hM.positive q.left q.right a hs
    rw [route_real, hr]
    cases a <;> simpa only [answerRetained, Routing.toReal, Routing.Holds, Routing.Less,
      Routing.Greater, LocalSelection.comparisonEvent] using hp
  | leftFree c =>
    have hs : ArbitraryLabels.selectThreshold M.tree.system k q.left c = .answer a := by
      simpa only [attempt, hr] using h
    have hp := ArbitraryLabels.selectThreshold_probability M.tree.system k hk hM.noLoop hM.positive q.left c a hs
    rw [route_real, hr]
    cases a <;> simpa only [answerRetained, Routing.toReal, Routing.Holds, Routing.Less,
      Routing.Greater, LocalSelection.thresholdEvent] using hp
  | rightFree c =>
    cases hs : ArbitraryLabels.selectThreshold M.tree.system k q.right c with
    | answer b =>
      have hab : reverseAnswer b = a := by simpa only [attempt, hr, hs, reverseResult,
        LocalSelection.Result.answer.injEq] using h
      subst a
      have hp := ArbitraryLabels.selectThreshold_probability M.tree.system k hk hM.noLoop hM.positive q.right c b hs
      rw [route_real, hr]
      cases b <;> simpa only [answerRetained, reverseAnswer, Routing.toReal, Routing.Holds,
        Routing.Less, Routing.Greater, LocalSelection.thresholdEvent] using hp
    | refine z c' =>
      simp only [attempt, hr, hs, reverseResult] at h
      cases h
  | anchors c d =>
    have hE : {X : Fin n → ℝ |
        (route (M.tree.toReal.location q.left) (M.tree.toReal.location q.right)).Holds
          (X q.left) (X q.right) a} = univ := by
      apply Set.eq_univ_of_forall
      intro X
      rw [route_real, hr] at ha ⊢
      cases a <;> exact ha
    haveI := isProbabilityMeasure_uniformMeasure M.tree.system.toReal hM.positive
    rw [hE]
    have hbound : answerRetained (k : ℝ) ≤ 1 := by
      unfold answerRetained
      have hnonneg : (0 : ℝ) ≤ 1 / (100 * (k : ℝ)) := by positivity
      linarith
    simpa only [Measure.real_def, measure_univ, ENNReal.toReal_one] using hbound

@[simp] theorem makeMove_item (M : Memory n) (x : Fin n) (c : ℚ) : (makeMove M x c).item = x := rfl

theorem makeMove_anchor (M : Memory n) (x : Fin n) (q : ℚ) (c : DyadicAnchor)
    (hc : c.coordinate = q) : (makeMove M x q).anchor = c := by
  simp only [makeMove, ← hc, DyadicAnchor.ofRat_coordinate]

theorem makeMove_order (M : Memory n) (x : Fin n) (q : ℚ) :
    (makeMove M x q).order = rankOrder (GraphOrder.graphRank
      (resetCoordinate M.tree.system x (makeMove M x q).anchor.coordinate)) := rfl

/-- The routed refinement is one of the original queried labels, and the
stored decoder recovers exactly the proved dyadic value and its level. -/
theorem attempt_refine_spec (M : Memory n) (k : ℕ) (hk : 64 ≤ k)
    (hM : Admissible k M) (q : Query n) (z : Fin n) (v : ℚ)
    (h : attempt M k q = .refine z v) :
    (z = q.left ∨ z = q.right) ∧ (makeMove M z v).anchor.coordinate = v ∧
      M.tree.system.lower z < v ∧ v < M.tree.system.upper z ∧
      (k : ℝ) < log2 (density M.tree.system.toReal z (v : ℝ)) ∧
      stopMass k * (makeMove M z v).anchor.1 - 4 <
        log2 (density M.tree.system.toReal z (v : ℝ)) := by
  obtain ⟨rank, hrank, hheight⟩ := hM.rank
  have hgeom := hM.toGeometric
  have hs : (z = q.left ∨ z = q.right) ∧ ∃ c : DyadicAnchor, c.coordinate = v ∧
      M.tree.system.lower z < v ∧ v < M.tree.system.upper z ∧
      (k : ℝ) < log2 (density M.tree.system.toReal z (v : ℝ)) ∧
      stopMass k * c.1 - 4 < log2 (density M.tree.system.toReal z (v : ℝ)) := by
    cases hr : route (M.tree.location q.left) (M.tree.location q.right) with
    | coordinates =>
      exact ArbitraryLabels.select_refine_spec M.tree.system k hk hgeom.normalized hgeom.positive
        hgeom.widths hgeom.rationalBounds rank hrank hheight hM.degree
        q.left q.right z q.distinct v (by simpa only [attempt, hr] using h)
    | leftFree c =>
      have ht := ArbitraryLabels.selectThreshold_refine_spec M.tree.system k hk hgeom.normalized hgeom.positive
        hgeom.widths hgeom.rationalBounds rank hrank hheight hM.degree q.left z c v
        (by simpa only [attempt, hr] using h)
      exact ⟨Or.inl ht.1, ht.2⟩
    | rightFree c =>
      have hs : ArbitraryLabels.selectThreshold M.tree.system k q.right c = .refine z v := by
        cases ht : ArbitraryLabels.selectThreshold M.tree.system k q.right c with
        | answer b =>
          simp only [attempt, hr, ht, reverseResult] at h
          cases h
        | refine w u =>
          have he : w = z ∧ u = v := by simpa only [attempt, hr, ht, reverseResult,
            LocalSelection.Result.refine.injEq] using h
          simpa only [he.1, he.2] using ht
      have ht := ArbitraryLabels.selectThreshold_refine_spec M.tree.system k hk hgeom.normalized hgeom.positive
        hgeom.widths hgeom.rationalBounds rank hrank hheight hM.degree q.right z c v hs
      exact ⟨Or.inr ht.1, ht.2⟩
    | anchors c d =>
      simp only [attempt, hr] at h
      cases h
  obtain ⟨hz, c, hc, hl, hu, hg, ht⟩ := hs
  rw [makeMove_anchor M z v c hc]
  exact ⟨hz, hc, hl, hu, hg, ht⟩

theorem attempt_refine_admissible (M : Memory n) (k : ℕ) (hk : 64 ≤ k)
    (hM : Admissible k M) (q : Query n) (z : Fin n) (v : ℚ)
    (h : attempt M k q = .refine z v) :
    Admissible k (Controller.applyMove M (makeMove M z v)) := by
  obtain ⟨_, hc, hl, hu, _, _⟩ := attempt_refine_spec M k hk hM q z v h
  apply hM.applyMove (makeMove M z v) _ (makeMove_order M z v)
  simpa only [makeMove_item, hc] using And.intro hl hu

theorem attempt_refine_ready (M : Memory n) (k : ℕ) (hk : 64 ≤ k)
    (hM : Ready k M) (q : Query n) (z : Fin n) (v : ℚ)
    (h : attempt M k q = .refine z v) :
    Ready k (Controller.applyMove M (makeMove M z v)) := by
  obtain ⟨_, hc, hl, hu, _, _⟩ := attempt_refine_spec M k hk hM.admissible q z v h
  apply hM.applyMove (makeMove M z v) _ (makeMove_order M z v)
  simpa only [makeMove_item, hc] using And.intro hl hu

theorem makeMove_gain (M : Memory n) (hM : Geometric M) (x : Fin n) (v : ℚ)
    (hc : (makeMove M x v).anchor.coordinate = v)
    (hin : M.tree.system.lower x < v ∧ v < M.tree.system.upper x)
    (hnew : Geometric (Controller.applyMove M (makeMove M x v))) :
    (makeMove M x v).gain M.tree.toReal = log2 (density M.tree.system.toReal x (v : ℝ)) := by
  have hinside : M.tree.toReal.system.lower (makeMove M x v).item <
        ((makeMove M x v).anchor.coordinate : ℝ) ∧
      ((makeMove M x v).anchor.coordinate : ℝ) < M.tree.toReal.system.upper (makeMove M x v).item := by
    simp only [makeMove_item, hc]
    exact ⟨(Rat.cast_lt (K := ℝ)).mpr hin.1, (Rat.cast_lt (K := ℝ)).mpr hin.2⟩
  have hV' : 0 < nodeVolume ((makeMove M x v).apply M.tree.toReal).system := by
    rw [← applyMove_tree]
    exact nodeVolume_pos _ hnew.positive
  have hg := (makeMove M x v).gain_eq_log_density_of_positive M.tree.toReal
    (hM.noLoop _) hinside (nodeVolume_pos _ hM.positive) hV'
  simpa only [makeMove_item, hc, State.toReal] using hg

theorem attempt_refine_gain (M : Memory n) (k : ℕ) (hk : 64 ≤ k)
    (hM : Admissible k M) (q : Query n) (z : Fin n) (v : ℚ)
    (h : attempt M k q = .refine z v) :
    (k : ℝ) < (makeMove M z v).gain M.tree.toReal ∧
      stopMass k * (makeMove M z v).anchor.1 - 4 < (makeMove M z v).gain M.tree.toReal := by
  obtain ⟨_, hc, hl, hu, hg, ht⟩ := attempt_refine_spec M k hk hM q z v h
  rw [makeMove_gain M hM.toGeometric z v hc ⟨hl, hu⟩
    (attempt_refine_admissible M k hk hM q z v h).toGeometric]
  exact ⟨hg, ht⟩

theorem attempt_refine_valid (M : Memory n) (k : ℕ) (hk : 64 ≤ k)
    (hM : Admissible k M) (q : Query n) (z : Fin n) (v : ℚ)
    (h : attempt M k q = .refine z v) (F : Frame n) (hF : M.Represents F) :
    (Action.selection (makeMove M z v)).Valid k F := by
  change (k : ℝ) < (makeMove M z v).gain F.state ∧
    stopMass k * (makeMove M z v).anchor.1 - 4 ≤ (makeMove M z v).gain F.state
  rw [← hF.1]
  have hg := attempt_refine_gain M k hk hM q z v h
  exact ⟨hg.1, hg.2.le⟩

/-- Repair anchors use the same actual decoder and preserve admissibility;
their tariff is stated directly in terms of the concrete move's volume gain. -/
theorem anchor_move_spec (M : Memory n) (k : ℕ) (hk : 64 ≤ k)
    (hM : Admissible k M) (x : Fin n) :
    let v := ArbitraryLabels.chooseAnchor M.tree.system k x
    let m := makeMove M x v
    m.anchor.coordinate = v ∧ M.tree.system.lower x < v ∧ v < M.tree.system.upper x ∧
      Admissible k (Controller.applyMove M m) ∧
      stopMass k * m.anchor.1 - 4 < m.gain M.tree.toReal := by
  obtain ⟨rank, hrank, hheight⟩ := hM.rank
  have hgeom := hM.toGeometric
  obtain ⟨c, hc, hl, hu, ht⟩ := ArbitraryLabels.chooseAnchor_spec M.tree.system k hk
    hgeom.normalized hgeom.positive hgeom.widths hgeom.rationalBounds rank hrank hheight hM.degree x
  let v := ArbitraryLabels.chooseAnchor M.tree.system k x
  have hanchor : (makeMove M x v).anchor = c := makeMove_anchor M x v c hc
  have hcoord : (makeMove M x v).anchor.coordinate = v := by rw [hanchor]; exact hc
  have hinside : M.tree.system.lower x < v ∧ v < M.tree.system.upper x := by
    simpa only [hc] using And.intro hl hu
  have hnew : Admissible k (Controller.applyMove M (makeMove M x v)) := by
    apply hM.applyMove (makeMove M x v) _ (makeMove_order M x v)
    simpa only [makeMove_item, hcoord] using hinside
  refine ⟨hcoord, hinside.1, hinside.2, hnew, ?_⟩
  rw [makeMove_gain M hgeom x v hcoord hinside hnew.toGeometric, hanchor]
  simpa only [hc] using ht

theorem anchor_move_ready (M : Memory n) (k : ℕ) (hk : 64 ≤ k)
    (hM : Ready k M) (x : Fin n) :
    Ready k (Controller.applyMove M (makeMove M x (ArbitraryLabels.chooseAnchor M.tree.system k x))) := by
  have hs := anchor_move_spec M k hk hM.admissible x
  apply hM.applyMove _ _ (makeMove_order M x _)
  simpa only [makeMove_item, hs.1] using And.intro hs.2.1 hs.2.2.1

theorem anchor_move_valid_degree (M : Memory n) (k : ℕ) (hk : 64 ≤ k)
    (hM : Admissible k M) (x : Fin n) (F : Frame n) (hF : M.Represents F)
    (hd : k ≤ (ArcBudget.incident M.tree.system.toReal x).card) :
    (Action.degree (makeMove M x (ArbitraryLabels.chooseAnchor M.tree.system k x))).Valid k F := by
  have hs := anchor_move_spec M k hk hM x
  change (stopMass k * (makeMove M x _).anchor.1 - 4 ≤ (makeMove M x _).gain F.state) ∧ _
  rw [← hF.1]
  exact ⟨hs.2.2.2.2.le, hd⟩

end SortingAdversary.Continuous.Controller
