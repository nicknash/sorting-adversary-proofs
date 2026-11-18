import SortingAdversary.Continuous.PolylogSelection
import SortingAdversary.Continuous.PolylogAnchor
import SortingAdversary.Continuous.ControllerLocal
import SortingAdversary.Continuous.ControllerSupport

/-!
# Rounded selection and refinement at the controller interface

The three tests use a fixed fractional precision determined by the stage.
An unsuccessful test reads the exact walls of just the chosen label.
The fallback reference expression agrees with the bounded bit search on
every legal machine grid by `PolylogAnchor.fallback_eq_reference`.
-/

namespace SortingAdversary.Continuous.PolylogOracle

open Controller TreeState FiniteAveraging Certificates OrderRegion Density MeasureTheory Set
open ArbitraryLabels (pathHeight widthThreshold widthThreshold_pos)
open EnclosureParameters (alphabet neighborhoodBound neighborhoodBound_pos)
open CertificateSuccess (accuracy)
open TraceAccounting (Move)

variable {n : ℕ}

abbrev cutoff (k : ℕ) := widthThreshold k (pathHeight k)
abbrev comparable (k : ℕ) := neighborhoodBound k (pathHeight k)
def grid (k : ℕ) := PolylogEnclosure.gridBits (accuracy k (comparable k) (cutoff k))

private theorem mesh_bound {k : ℕ} (hk : 0 < k) :
    PolylogEnclosure.mesh (grid k) ≤ accuracy k (comparable k) (cutoff k) / 4 :=
  PolylogEnclosure.mesh_gridBits_le (CertificateSuccess.accuracy_pos hk _ (widthThreshold_pos ..))

def pairTest (M : Memory n) (k : ℕ) (x y : Fin n) : Option Answer :=
  if hk : 0 < k then selectAnswer k (PolylogSelection.twoIntervals M.tree.system (grid k) k
    (pathHeight k) hk (cutoff k) (widthThreshold_pos ..) x y) else none

def thresholdTest (M : Memory n) (k : ℕ) (x : Fin n) (c : ℚ) : Option Answer :=
  if hk : 0 < k then selectAnswer k (PolylogSelection.thresholdIntervals M.tree.system (grid k) k
    (pathHeight k) hk (cutoff k) (widthThreshold_pos ..) x c) else none

def centralTest (M : Memory n) (k : ℕ) (x : Fin n) : Option Interval :=
  if hk : 0 < k then centralInterval (PolylogSelection.oneIntervals M.tree.system (grid k) k
    (pathHeight k) hk (cutoff k) (widthThreshold_pos ..) x) else none

def prefixAnchor (M : Memory n) (x : Fin n) : ℚ :=
  let l := M.tree.system.lower x
  let r := M.tree.system.upper x
  PolylogAnchor.fallback (PolylogAnchor.referenceBits l r) l r

def respond (M : Memory n) (x : Fin n) : Option Answer → LocalSelection.Result n
  | some a => .answer a
  | none => .refine x (prefixAnchor M x)

/-- Route between free coordinates or stored anchors before enumerating the local test. -/
def attempt (M : Memory n) (k : ℕ) (q : Query n) : LocalSelection.Result n :=
  match route (M.tree.location q.left) (M.tree.location q.right) with
  | .coordinates => respond M (min q.left q.right) (pairTest M k q.left q.right)
  | .leftFree c => respond M q.left (thresholdTest M k q.left c)
  | .rightFree c => reverseResult (respond M q.right (thresholdTest M k q.right c))
  | .anchors c d => .answer (if c < d then .less else .greater)

/-- Anchor used in a degree or path repair. -/
def anchor (M : Memory n) (k : ℕ) (x : Fin n) : ℚ :=
  match centralTest M k x with
  | none => prefixAnchor M x
  | some J => roundUp J

private theorem width_unit (M : Memory n) (hM : Geometric M) (x : Fin n) :
    M.tree.system.upper x - M.tree.system.lower x ≤ 1 := by
  have hb := hM.rationalBounds x
  linarith

private theorem count_le (M : Memory n) (k : ℕ) (hM : Admissible k M) (x : Fin n) :
    ComparableDensity.comparableCount M.tree.system.toReal x ≤ comparable k := by
  obtain ⟨rank, hr, hh⟩ := hM.rank
  exact ComparableBound.comparableCount_toReal_le _ rank _ _ hr hh hM.degree x

private theorem pair_small (M : Memory n) (k : ℕ) (hk : 0 < k)
    (hM : Admissible k M) (x y : Fin n) (hne : x ≠ y) (ht : pairTest M k x y = none) :
    let z := min x y
    M.tree.system.upper z - M.tree.system.lower z < cutoff k := by
  simp only [pairTest, dif_pos hk] at ht
  let z := min x y
  change M.tree.system.upper z - M.tree.system.lower z < cutoff k
  by_contra! hwide
  obtain ⟨rank, hr, hh⟩ := hM.rank
  have hwide' : cutoff k ≤ M.tree.system.upper x - M.tree.system.lower x ∨
      cutoff k ≤ M.tree.system.upper y - M.tree.system.lower y := by
    rcases le_total x y with h | h
    · exact Or.inl (by simpa only [z, min_eq_left h] using hwide)
    · exact Or.inr (by simpa only [z, min_eq_right h] using hwide)
  obtain ⟨a, ha⟩ := PolylogSelection.two_test_succeeds M.tree.system (grid k) k (pathHeight k)
    hk (cutoff k) (widthThreshold_pos ..) hM.normalized hM.positive
    (fun v => (hM.widths v).le) (width_unit M hM.toGeometric) rank hr hh hM.degree
    (mesh_bound hk) x y hne (count_le M k hM x) (count_le M k hM y) hwide'
  rw [ht] at ha
  cases ha

private theorem threshold_small (M : Memory n) (k : ℕ) (hk : 0 < k)
    (hM : Admissible k M) (x : Fin n) (c : ℚ) (ht : thresholdTest M k x c = none) :
    M.tree.system.upper x - M.tree.system.lower x < cutoff k := by
  simp only [thresholdTest, dif_pos hk] at ht
  by_contra! hwide
  obtain ⟨rank, hr, hh⟩ := hM.rank
  obtain ⟨a, ha⟩ := PolylogSelection.threshold_test_succeeds M.tree.system (grid k) k (pathHeight k)
    hk (cutoff k) (widthThreshold_pos ..) hM.normalized hM.positive
    (fun v => (hM.widths v).le) (width_unit M hM.toGeometric) rank hr hh hM.degree
    (mesh_bound hk) x (count_le M k hM x) hwide c
  rw [ht] at ha
  cases ha

private theorem central_small (M : Memory n) (k : ℕ) (hk : 0 < k)
    (hM : Admissible k M) (x : Fin n) (ht : centralTest M k x = none) :
    M.tree.system.upper x - M.tree.system.lower x < cutoff k := by
  simp only [centralTest, dif_pos hk] at ht
  by_contra! hwide
  obtain ⟨rank, hr, hh⟩ := hM.rank
  have ha := PolylogSelection.central_test_succeeds M.tree.system (grid k) k (pathHeight k)
    hk (cutoff k) (widthThreshold_pos ..) hM.normalized hM.positive
    (fun v => (hM.widths v).le) (width_unit M hM.toGeometric) rank hr hh hM.degree
    (mesh_bound hk) x (count_le M k hM x) hwide
  dsimp only at ha
  rw [ht] at ha
  cases ha

private theorem prefix_spec (M : Memory n) (k : ℕ) (hk : 64 ≤ k) (hM : Admissible k M)
    (x : Fin n) (hsmall : M.tree.system.upper x - M.tree.system.lower x < cutoff k) :
    let v := prefixAnchor M x
    (makeMove M x v).anchor.coordinate = v ∧ M.tree.system.lower x < v ∧
      v < M.tree.system.upper x ∧ (k : ℝ) < log2 (density M.tree.system.toReal x (v : ℝ)) ∧
      stopMass k * (makeMove M x v).anchor.1 - 4 < log2 (density M.tree.system.toReal x (v : ℝ)) := by
  let l := M.tree.system.lower x
  let r := M.tree.system.upper x
  let F := PolylogAnchor.referenceBits l r
  have hw : l < r := hM.widths x
  have hb := hM.rationalBounds x
  have hcap := PolylogAnchor.referenceBits_spec hw
  obtain ⟨c, hc, hg, ht⟩ := PolylogAnchor.fallback_tariffs M.tree.system x F k (comparable k)
    hk (neighborhoodBound_pos ..) hM.normalized (count_le M k hM x) hM.positive hw hb hcap hsmall
  have hs := PolylogAnchor.widthSearch_of_bound hcap (width_unit M hM.toGeometric x)
  have hm := PolylogAnchor.atScale_middle hs.2.1 hs.2.2
  have hin : l < prefixAnchor M x ∧ prefixAnchor M x < r := middle_half_interior hw hm
  change c.coordinate = prefixAnchor M x at hc
  rw [hc] at hg ht
  dsimp only
  rw [makeMove_anchor M x _ c hc]
  exact ⟨hc, hin.1, hin.2, hg, ht⟩

private theorem pair_probability (M : Memory n) (k : ℕ) (hk : 0 < k) (hM : Geometric M)
    (x y : Fin n) (a : Answer) (h : pairTest M k x y = some a) :
    answerRetained k ≤ (uniformMeasure M.tree.system.toReal).real
      (LocalSelection.comparisonEvent x y a) := by
  simp only [pairTest, dif_pos hk, PolylogSelection.twoIntervals_full] at h
  exact PolylogEnclosure.roundedTwo_probability _ _ _ _ (EnclosureParameters.alphabet_pos ..)
    hM.noLoop hM.positive _ x y a h

private theorem threshold_probability (M : Memory n) (k : ℕ) (hk : 0 < k) (hM : Geometric M)
    (x : Fin n) (c : ℚ) (a : Answer) (h : thresholdTest M k x c = some a) :
    answerRetained k ≤ (uniformMeasure M.tree.system.toReal).real
      (LocalSelection.thresholdEvent x c a) := by
  simp only [thresholdTest, dif_pos hk, PolylogSelection.thresholdIntervals_full] at h
  exact PolylogEnclosure.roundedThreshold_probability _ _ _ _ (EnclosureParameters.alphabet_pos ..)
    hM.noLoop hM.positive _ x c a h

/-- A successful local test retains the required mass in the direction of
the routed query, including a reversed threshold query. -/
theorem attempt_answer_probability (M : Memory n) (k : ℕ) (hk : 0 < k)
    (hM : Geometric M) (q : Query n) (a : Answer) (h : attempt M k q = .answer a) :
    (route (M.tree.toReal.location q.left) (M.tree.toReal.location q.right)).AnchorAnswer a ∧
      answerRetained k ≤ (uniformMeasure M.tree.system.toReal).real
        {X | (route (M.tree.toReal.location q.left) (M.tree.toReal.location q.right)).Holds
          (X q.left) (X q.right) a} := by
  cases hr : route (M.tree.location q.left) (M.tree.location q.right) with
  | coordinates =>
    cases ht : pairTest M k q.left q.right with
    | none => simp [attempt, hr, ht, respond] at h
    | some b =>
      have hba : b = a := by simpa [attempt, hr, ht, respond] using h
      subst a
      rw [route_real, hr]
      refine ⟨trivial, ?_⟩
      have hp := pair_probability M k hk hM q.left q.right b ht
      cases b <;> exact hp
  | leftFree c =>
    cases ht : thresholdTest M k q.left c with
    | none => simp [attempt, hr, ht, respond] at h
    | some b =>
      have hba : b = a := by simpa [attempt, hr, ht, respond] using h
      subst a
      rw [route_real, hr]
      refine ⟨trivial, ?_⟩
      have hp := threshold_probability M k hk hM q.left c b ht
      cases b <;> exact hp
  | rightFree c =>
    cases ht : thresholdTest M k q.right c with
    | none => simp [attempt, hr, ht, respond, reverseResult] at h
    | some b =>
      have hba : reverseAnswer b = a := by simpa [attempt, hr, ht, respond, reverseResult] using h
      subst a
      rw [route_real, hr]
      refine ⟨trivial, ?_⟩
      have hp := threshold_probability M k hk hM q.right c b ht
      cases b <;> exact hp
  | anchors c d =>
    exact Controller.attempt_answer_probability M k hk hM q a
      (by simpa only [Controller.attempt, attempt, hr] using h)

/-- Each failed comparison chooses one of its two labels and pays both
required tariffs at the actual reduced level stored by the controller. -/
theorem attempt_refine_spec (M : Memory n) (k : ℕ) (hk : 64 ≤ k)
    (hM : Admissible k M) (q : Query n) (z : Fin n) (v : ℚ)
    (h : attempt M k q = .refine z v) :
    (z = q.left ∨ z = q.right) ∧ (makeMove M z v).anchor.coordinate = v ∧
      M.tree.system.lower z < v ∧ v < M.tree.system.upper z ∧
      (k : ℝ) < log2 (density M.tree.system.toReal z (v : ℝ)) ∧
      stopMass k * (makeMove M z v).anchor.1 - 4 <
        log2 (density M.tree.system.toReal z (v : ℝ)) := by
  have hk0 : 0 < k := by omega
  cases hr : route (M.tree.location q.left) (M.tree.location q.right) with
  | coordinates =>
    cases ht : pairTest M k q.left q.right with
    | some b => simp [attempt, hr, ht, respond] at h
    | none =>
      simp only [attempt, hr, ht, respond, LocalSelection.Result.refine.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨(min_cases ..).imp And.left And.left,
        prefix_spec M k hk hM _ (pair_small M k hk0 hM _ _ q.distinct ht)⟩
  | leftFree c =>
    cases ht : thresholdTest M k q.left c with
    | some b => simp [attempt, hr, ht, respond] at h
    | none =>
      simp only [attempt, hr, ht, respond, LocalSelection.Result.refine.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨Or.inl rfl, prefix_spec M k hk hM _ (threshold_small M k hk0 hM _ c ht)⟩
  | rightFree c =>
    cases ht : thresholdTest M k q.right c with
    | some b => simp [attempt, hr, ht, respond, reverseResult] at h
    | none =>
      simp only [attempt, hr, ht, respond, reverseResult, LocalSelection.Result.refine.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨Or.inr rfl, prefix_spec M k hk hM _ (threshold_small M k hk0 hM _ c ht)⟩
  | anchors c d => simp [attempt, hr] at h

/-- The refinement label property is syntactic and also holds outside the
reachable part of memory. -/
theorem attempt_refine_output (M : Memory n) (k : ℕ)
    (q : Query n) (z : Fin n) (v : ℚ) (h : attempt M k q = .refine z v) :
    (z = q.left ∨ z = q.right) ∧ v = prefixAnchor M z := by
  cases hr : route (M.tree.location q.left) (M.tree.location q.right) with
  | coordinates =>
    cases ht : pairTest M k q.left q.right with
    | some b => simp [attempt, hr, ht, respond] at h
    | none =>
      simp only [attempt, hr, ht, respond, LocalSelection.Result.refine.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨(min_cases ..).imp And.left And.left, rfl⟩
  | leftFree c =>
    cases ht : thresholdTest M k q.left c with
    | some b => simp [attempt, hr, ht, respond] at h
    | none =>
      simp only [attempt, hr, ht, respond, LocalSelection.Result.refine.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨Or.inl rfl, rfl⟩
  | rightFree c =>
    cases ht : thresholdTest M k q.right c with
    | some b => simp [attempt, hr, ht, respond, reverseResult] at h
    | none =>
      simp only [attempt, hr, ht, respond, reverseResult, LocalSelection.Result.refine.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨Or.inr rfl, rfl⟩
  | anchors c d => simp [attempt, hr] at h

theorem attempt_refine_label (M : Memory n) (k : ℕ) (_hk : 0 < k) (q : Query n)
    (z : Fin n) (v : ℚ) (h : attempt M k q = .refine z v) : z = q.left ∨ z = q.right :=
  (attempt_refine_output M k q z v h).1

private theorem central_spec (M : Memory n) (k : ℕ) (hk : 0 < k) (hM : Geometric M)
    (x : Fin n) (J : Interval) (h : centralTest M k x = some J) :
    ∃ c : DyadicAnchor, c.coordinate = roundUp J ∧
      M.tree.system.lower x < c.coordinate ∧ c.coordinate < M.tree.system.upper x ∧
      (c.1 : ℝ) - 4 < log2 (density M.tree.system.toReal x (c.coordinate : ℝ)) := by
  simp only [centralTest, dif_pos hk, PolylogSelection.oneIntervals_full, PolylogSelection.fullList] at h
  have hS := EnclosureParameters.alphabet_pos k (pathHeight k)
  have hp := PolylogEnclosure.roundedCentral_probabilities M.tree.system (grid k) _ hS
    hM.noLoop hM.positive _ x J h
  have he := ArbitraryLabels.weak_endpoints M.tree.system hM.normalized hM.widths
  have hi := PolylogEnclosure.roundedCentral_intervalInterior M.tree.system (grid k) _ _ x
    hM.widths he.1 he.2 h
  have hJ := (centralInterval_certificates h).1
  have hb := hM.rationalBounds x
  obtain ⟨c,hc,hlen⟩ := roundUp_anchor (hb.1.trans_lt hi.1) (hi.2.trans_le hb.2) hJ
  have hm := roundUp_mem hJ
  rw [← hc] at hm
  refine ⟨c,hc,hi.1.trans_le hm.1,hm.2.trans hi.2,?_⟩
  apply central_density_tariff (w := (J.2 : ℝ) - J.1)
  · exact_mod_cast sub_pos.mpr hJ
  · simpa using (Rat.cast_lt (K := ℝ)).mpr hlen
  · apply CentralQuantiles.central_interval_lower (density M.tree.system.toReal x)
      (density_integrable _ x) (density_nonneg _ x)
      (integral_density _ x (nodeVolume_pos _ hM.positive))
      (fun s c t hsc hct => SectionConcavity.density_two_point _ x hsc hct)
      (by exact_mod_cast hJ) ⟨by exact_mod_cast hm.1, by exact_mod_cast hm.2.le⟩
    · simpa only [← coordinate_probability_eq_integral _ x _ measurableSet_Iic, mem_Iic] using hp.1
    · simpa only [← coordinate_probability_eq_integral _ x _ measurableSet_Icc, mem_Icc] using hp.2.1
    · simpa only [← coordinate_probability_eq_integral _ x _ measurableSet_Ici, mem_Ici] using hp.2.2

/-- Both branches of repair yield an admissible interior move with its
tariff paid by the actual change in represented volume. -/
theorem anchor_move_spec (M : Memory n) (k : ℕ) (hk : 64 ≤ k)
    (hM : Admissible k M) (x : Fin n) :
    let v := anchor M k x
    let m := makeMove M x v
    m.anchor.coordinate = v ∧ M.tree.system.lower x < v ∧ v < M.tree.system.upper x ∧
      Admissible k (Controller.applyMove M m) ∧
      stopMass k * m.anchor.1 - 4 < m.gain M.tree.toReal := by
  let v := anchor M k x
  have hs : (makeMove M x v).anchor.coordinate = v ∧ M.tree.system.lower x < v ∧
      v < M.tree.system.upper x ∧ stopMass k * (makeMove M x v).anchor.1 - 4 <
      log2 (density M.tree.system.toReal x (v : ℝ)) := by
    cases ht : centralTest M k x with
    | none =>
      obtain ⟨hc, hl, hr, _, hg⟩ := prefix_spec M k hk hM x (central_small M k (by omega) hM x ht)
      exact (show v = prefixAnchor M x by simp [v, anchor, ht]) ▸ ⟨hc,hl,hr,hg⟩
    | some J =>
      obtain ⟨c,hc,hl,hr,hg⟩ := central_spec M k (by omega) hM.toGeometric x J ht
      have hv : c.coordinate = v := by simpa [v, anchor, ht] using hc
      have hc' := makeMove_anchor M x v c hv
      rw [hc']
      have hstop : stopMass k * (c.1 : ℝ) ≤ c.1 := by
        have hle : stopMass k ≤ 1 := by unfold stopMass; have := (show (0 : ℝ) ≤ 1/k by positivity); linarith
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg c.1)
      rw [hv] at hl hr hg
      exact ⟨hv, hl, hr, (sub_le_sub_right hstop 4).trans_lt hg⟩
  obtain ⟨hc,hl,hr,hg⟩ := hs
  have hn : Admissible k (Controller.applyMove M (makeMove M x v)) := by
    apply hM.applyMove _ _ (makeMove_order M x v)
    simpa only [makeMove_item, hc] using And.intro hl hr
  exact ⟨hc,hl,hr,hn, (makeMove_gain M hM.toGeometric x v hc ⟨hl,hr⟩ hn.toGeometric) ▸ hg⟩

/-- The rounded decisions supplied to the shared online controller. -/
@[instance_reducible] def choices (n : ℕ) : Controller.Choices n := ⟨attempt, anchor⟩

theorem choices_valid (n : ℕ) : Controller.ChoiceLaws (choices n) :=
  ⟨attempt_answer_probability, attempt_refine_spec, anchor_move_spec⟩

theorem choices_labels (n : ℕ) : Controller.ChoiceLabels (choices n) :=
  ⟨attempt_refine_label⟩

end SortingAdversary.Continuous.PolylogOracle
