import SortingAdversary.Continuous.ControllerSemantics
import SortingAdversary.Continuous.StateInvariants

/-!
# The executable controller touches only queried labels

During a call the pending query's two labels are added to the support. Every
selection refinement lies there. A nontrivial repair path and a vertex of
positive degree cannot contain an untouched isolated item. This proves that
all other coordinates stay isolated unit coordinates with empty anchor paths,
as required by the queried-label counting theorem.
-/

namespace SortingAdversary.Continuous

open FiniteAveraging OrderRegion TreeState TraceAccounting
open SortingAdversary.Optimal.GraphBalls

variable {n : ℕ}

namespace TraceAccounting

def Action.Supported (A : Finset (Fin n)) : Action n → Prop
  | .selection m | .degree m => m.item ∈ A
  | .path ms => ∀ m ∈ ms, m.item ∈ A
  | .answer q _ _ => q.left ∈ A ∧ q.right ∈ A

end TraceAccounting

namespace Controller

def Memory.SupportedBy (M : Memory n) (A : Finset (Fin n)) : Prop :=
  ∀ x ∉ A, IsolatedUnit M.tree.toReal.system x ∧ M.paths x = []

def Memory.Supported (M : Memory n) : Prop := M.SupportedBy (queriedLabels M.history)

theorem Memory.SupportedBy.mono (M : Memory n) {A B : Finset (Fin n)}
    (h : M.SupportedBy A) (hAB : A ⊆ B) : M.SupportedBy B :=
  fun x hx => h x (fun hxa => hx (hAB hxa))

theorem initial_supported (n : ℕ) : (initial n).Supported := by
  intro x hx
  exact ⟨by simpa only [initial, initial_toReal] using initial_isolatedUnit x, rfl⟩

theorem applyMove_supportedBy (M : Memory n) (A : Finset (Fin n))
    (hM : M.SupportedBy A) (m : Move n) (hm : m.item ∈ A) :
    (applyMove M m).SupportedBy A := by
  intro x hx
  obtain ⟨hunit, hpath⟩ := hM x hx
  have hxm : x ≠ m.item := by intro h; subst x; exact hx hm
  constructor
  · rw [applyMove_tree]
    exact normalize_isolatedUnit _ x
      (resetCoordinate_preserves_isolatedUnit M.tree.toReal.system x m.item
        (m.anchor.coordinate : ℝ) hunit) m.order
  · simpa only [applyMove, Function.update_of_ne hxm] using hpath

theorem applyMoves_supportedBy (M : Memory n) (A : Finset (Fin n))
    (hM : M.SupportedBy A) (ms : List (Move n)) (hm : ∀ m ∈ ms, m.item ∈ A) :
    (applyMoves M ms).SupportedBy A := by
  induction ms generalizing M with
  | nil => exact hM
  | cons m ms ih =>
    exact ih (applyMove M m) (applyMove_supportedBy M A hM m (hm m (by simp)))
      (fun m' hm' => hm m' (by simp [hm']))

theorem applyAction_supportedBy (M : Memory n) (A : Finset (Fin n))
    (hM : M.SupportedBy A) (a : Action n) (ha : a.Supported A) :
    (applyAction M a).SupportedBy A := by
  cases a with
  | selection m => exact applyMove_supportedBy M A hM m ha
  | degree m => exact applyMove_supportedBy M A hM m ha
  | path ms => exact applyMoves_supportedBy M A hM ms ha
  | answer q a order =>
    intro x hx
    obtain ⟨hunit, hpath⟩ := hM x hx
    have hxl : x ≠ q.left := by intro h; subst x; exact hx ha.1
    have hxr : x ≠ q.right := by intro h; subst x; exact hx ha.2
    constructor
    · rw [applyAction_tree]
      exact normalize_isolatedUnit _ x
        (record_preserves_isolatedUnit M.tree.toReal q a x hxl hxr hunit) order
    · exact hpath

theorem runActions_supportedBy (M : Memory n) (A : Finset (Fin n))
    (hM : M.SupportedBy A) (actions : List (Action n))
    (ha : ∀ a ∈ actions, a.Supported A) : (runActions M actions).SupportedBy A := by
  induction actions generalizing M with
  | nil => exact hM
  | cons a actions ih =>
    exact ih (applyAction M a) (applyAction_supportedBy M A hM a (ha a (by simp)))
      (fun a' ha' => ha a' (by simp [ha']))

theorem reverseResult_refine (r : LocalSelection.Result n) (x : Fin n) (c : ℚ) :
    reverseResult r = .refine x c ↔ r = .refine x c := by
  cases r <;> simp [reverseResult]

/-- Routing and reversal preserve the endpoint-only refinement rule. -/
theorem attempt_refine_label (M : Memory n) (k : ℕ) (hk : 0 < k)
    (q : Query n) (x : Fin n) (c : ℚ) (h : attempt M k q = .refine x c) :
    x = q.left ∨ x = q.right := by
  cases hr : route (M.tree.location q.left) (M.tree.location q.right) with
  | coordinates =>
    simp only [attempt, hr, ArbitraryLabels.select_pos _ _ hk] at h
    have hx := (ArbitraryLabels.selectTwo_refine_label M.tree.system k
      (ArbitraryLabels.pathHeight k) hk q.left q.right x c h).1
    rw [hx]
    exact (min_cases q.left q.right).imp And.left And.left
  | leftFree d =>
    simp only [attempt, hr, ArbitraryLabels.selectThreshold_pos _ _ hk] at h
    exact Or.inl (ArbitraryLabels.selectThreshold_refine_label M.tree.system k
      (ArbitraryLabels.pathHeight k) hk q.left x d c h).1
  | rightFree d =>
    simp only [attempt, hr, reverseResult_refine,
      ArbitraryLabels.selectThreshold_pos _ _ hk] at h
    exact Or.inr (ArbitraryLabels.selectThreshold_refine_label M.tree.system k
      (ArbitraryLabels.pathHeight k) hk q.right x d c h).1
  | anchors d e => simp [attempt, hr] at h

theorem selectLoop_supportedBy (k : ℕ) (hk : 0 < k) (q : Query n)
    (A : Finset (Fin n)) (hq : q.left ∈ A ∧ q.right ∈ A)
    (fuel : ℕ) (M : Memory n) (hM : M.SupportedBy A)
    (r : Result n) (h : selectLoop k q fuel M = some r) :
    r.memory.SupportedBy A ∧ ∀ a ∈ r.actions, a.Supported A := by
  induction fuel generalizing M r with
  | zero => simp [selectLoop] at h
  | succ fuel ih =>
    cases ha : attempt M k q with
    | answer a =>
      simp only [selectLoop, ha, Option.some.injEq] at h
      cases h
      exact ⟨hM, by simp⟩
    | refine x c =>
      have hx : x ∈ A := (attempt_refine_label M k hk q x c ha).elim
        (fun hx => hx ▸ hq.1) (fun hx => hx ▸ hq.2)
      have hM' := applyMove_supportedBy M A hM (makeMove M x c) hx
      cases hs : selectLoop k q fuel (applyMove M (makeMove M x c)) with
      | none => simp [selectLoop, ha, hs] at h
      | some s =>
        simp only [selectLoop, ha, hs, Option.map_some, Option.some.injEq] at h
        cases h
        obtain ⟨hstate, hactions⟩ := ih (applyMove M (makeMove M x c)) hM' s hs
        refine ⟨hstate, ?_⟩
        intro a ham
        rcases List.mem_cons.mp ham with rfl | ham
        · exact hx
        · exact hactions a ham

/-- Every vertex of a chain with at least two vertices has an incident arc,
so no isolated vertex can occur in that chain. -/
theorem chain_supported (E : Fin n → Fin n → Bool) (A : Finset (Fin n))
    (hi : ∀ x ∉ A, ∀ y, E x y = false ∧ E y x = false) :
    ∀ p : List (Fin n), p.IsChain (fun a b => E a b = true) →
      2 ≤ p.length → ∀ x ∈ p, x ∈ A := by
  intro p
  induction p with
  | nil => simp
  | cons a p ih =>
    intro hp hlen x hx
    cases p with
    | nil => simp at hlen
    | cons b p =>
      have he := List.isChain_cons_cons.mp hp
      have ha : a ∈ A := by
        by_contra hna
        have hf := (hi a hna b).1
        simp [hf] at he
      have hb : b ∈ A := by
        by_contra hnb
        have hf := (hi b hnb a).2
        simp [hf] at he
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · cases p with
        | nil => simpa using (List.mem_singleton.mp hx ▸ hb)
        | cons c p => exact ih he.2 (by simp) x hx

theorem pathBatch_supportedBy (k : ℕ) (M : Memory n) (A : Finset (Fin n))
    (hM : M.SupportedBy A) (xs : List (Fin n)) (hx : ∀ x ∈ xs, x ∈ A) :
    (pathBatch k M xs).1.SupportedBy A ∧
      ∀ m ∈ (pathBatch k M xs).2, m.item ∈ A := by
  have hm : ∀ m ∈ (pathBatch k M xs).2, m.item ∈ A := by
    intro m hm
    apply hx m.item
    rw [← pathBatch_labels k M xs]
    exact List.mem_map.mpr ⟨m, hm, rfl⟩
  refine ⟨?_, hm⟩
  rw [pathBatch_apply]
  exact applyMoves_supportedBy M A hM _ hm

theorem repair_supportedBy (k : ℕ) (hk : 0 < k) (M : Memory n)
    (A : Finset (Fin n)) (hM : M.SupportedBy A) :
    (repair k M).1.SupportedBy A ∧ ∀ a ∈ (repair k M).2, a.Supported A := by
  unfold repair
  split
  · rename_i xs hxs
    have hp := GraphPaths.firstPath_some M.tree.system.edge (2 ^ k) xs hxs
    have hlen : 2 ≤ xs.length := by
      rw [hp.1]
      have : 1 < 2 ^ k := one_lt_pow₀ (by decide) (by omega)
      omega
    have hlabels := chain_supported M.tree.system.edge A
      (fun x hx y => (hM x hx).1.2.2 y) xs hp.2.1 hlen
    obtain ⟨hs, hm⟩ := pathBatch_supportedBy k M A hM xs hlabels
    exact ⟨hs, by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hm⟩
  · split
    · exact ⟨hM, by simp⟩
    · rename_i x hx
      have hd := degreeChoice_some M k x hx
      have hxa : x ∈ A := by
        by_contra hxa
        have hi := (hM x hxa).1.2.2
        have he : neighbors M.tree.system.edge x = ∅ := by
          ext y
          have hxy : M.tree.system.edge x y = false := (hi y).1
          have hyx : M.tree.system.edge y x = false := (hi y).2
          simp [mem_neighbors, hxy, hyx]
        rw [he, Finset.card_empty] at hd
        omega
      refine ⟨applyMove_supportedBy M A hM _ hxa, ?_⟩
      intro a ha
      rcases List.mem_singleton.mp ha with rfl
      exact hxa

theorem compare_supportedBy (k : ℕ) (hk : 0 < k) (M : Memory n)
    (A : Finset (Fin n)) (hM : M.SupportedBy A) (q : Query n)
    (hq : q.left ∈ A ∧ q.right ∈ A) (r : Result n) (h : compare k M q = some r) :
    r.memory.SupportedBy A ∧ ∀ a ∈ r.actions, a.Supported A := by
  cases hs : selectLoop k q 3 M with
  | none => simp [compare, hs] at h
  | some s =>
    obtain ⟨hselect, hacts⟩ := selectLoop_supportedBy k hk q A hq 3 M hM s hs
    simp only [compare, hs, Option.map_some, Option.some.injEq] at h
    cases h
    let order := rankOrder (GraphOrder.graphRank (record s.memory.tree q s.answer).system)
    have hanswer := applyAction_supportedBy s.memory A hselect (.answer q s.answer order) hq
    obtain ⟨hrepair, hracts⟩ := repair_supportedBy k hk _ A hanswer
    refine ⟨hrepair, ?_⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact hacts a ha
      · rcases List.mem_singleton.mp ha with rfl
        exact hq
    · exact hracts a ha

/-- After the call completes, support is precisely the labels appearing in
the actual new transcript. The support argument is independent of its
probabilistic and volume certificates. -/
theorem compare_supported (k : ℕ) (hk : 0 < k) (M : Memory n) (hM : M.Supported)
    (q : Query n) (r : Result n) (h : compare k M q = some r) : r.memory.Supported := by
  have hA : M.SupportedBy (insert q.left (insert q.right (queriedLabels M.history))) :=
    hM.mono M (by intro x hx; simp [hx])
  have hresult := (compare_supportedBy k hk M _ hA q (by simp) r h).1
  change r.memory.SupportedBy (queriedLabels r.memory.history)
  rw [compare_history k M q r h]
  exact hresult

end Controller
end SortingAdversary.Continuous
