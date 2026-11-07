import SortingAdversary.Optimal.BallSchedule

/-!
# The exact law of the induced ball system

The auxiliary coupling uses the old label carrier, with outside labels left as
independent unary factors. This file proves that its restriction is precisely
the uniform feasible law counted by `LocalChoice.induced`. Thus no assumption
identifying a marginal with the uniform induced law is hidden in the coupling.
-/

namespace SortingAdversary.Optimal.TruncatedLaw

open WeakMaps LocalChoice BallSchedule FiniteProbability
open scoped BigOperators

variable {n K : ℕ}

/-- Feasible subtype on an arbitrary finite label carrier. -/
abbrev Feasible {α : Type*} (S : WeakSystem α (K + 1)) :=
  {f : ColorMap α (K + 1) // S.Valid f}

/-- The independent original unary intervals outside the selected ball union. -/
def outsideSystem (S : WeakSystem (Fin n) (K + 1)) (B : Finset (Fin n)) :
    WeakSystem {v : Fin n // v ∉ B} (K + 1) where
  edge _ _ := false
  lower v := S.lower v.val
  upper v := S.upper v.val

/-- Split an actual truncated feasible map into its inside and outside factors. -/
def splitState (S : WeakSystem (Fin n) (K + 1)) (B : Finset (Fin n))
    (f : Feasible (truncate S B)) : Feasible (induced S B) × Feasible (outsideSystem S B) :=
  (⟨restrictMap B f.val, by
    refine ⟨fun v => f.property.1 v.val, ?_⟩
    intro u v huv
    apply f.property.2 u.val v.val
    simpa [truncate, induced, u.property, v.property] using huv⟩,
   ⟨fun v => f.val v.val, by
    refine ⟨fun v => f.property.1 v.val, ?_⟩
    intro u v h
    simp [outsideSystem] at h⟩)

/-- Combine independently feasible inside and unary-only outside maps. -/
def joinState (S : WeakSystem (Fin n) (K + 1)) (B : Finset (Fin n))
    (p : Feasible (induced S B) × Feasible (outsideSystem S B)) : Feasible (truncate S B) :=
  ⟨fun v => if h : v ∈ B then p.1.val ⟨v, h⟩ else p.2.val ⟨v, h⟩, by
    constructor
    · intro v
      by_cases hv : v ∈ B
      · simpa [hv, truncate, induced] using p.1.property.1 ⟨v, hv⟩
      · simpa [hv, truncate, outsideSystem] using p.2.property.1 ⟨v, hv⟩
    · intro u v huv
      have hB : u ∈ B ∧ v ∈ B := by
        by_contra hn
        simp [truncate, hn] at huv
      have he : S.edge u v = true := by simpa [truncate, hB] using huv
      simpa [hB.1, hB.2] using p.1.property.2 ⟨u, hB.1⟩ ⟨v, hB.2⟩ he⟩

/-- The exact finite factorization behind the truncated marginal law. -/
def stateEquiv (S : WeakSystem (Fin n) (K + 1)) (B : Finset (Fin n)) :
    Feasible (truncate S B) ≃ Feasible (induced S B) × Feasible (outsideSystem S B) where
  toFun := splitState S B
  invFun := joinState S B
  left_inv f := by
    apply Subtype.ext
    funext v
    simp [splitState, joinState, restrictMap]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      funext v
      simp [splitState, joinState, restrictMap, v.property]
    · apply Subtype.ext
      funext v
      simp [splitState, joinState, v.property]

/-- The exact truncated count is the inside count times an independent unary
factor. It need not equal the inside count itself. -/
theorem count_truncate (S : WeakSystem (Fin n) (K + 1)) (B : Finset (Fin n)) :
    (truncate S B).count = (induced S B).count * (outsideSystem S B).count := by
  have hc := Fintype.card_congr (stateEquiv S B)
  simpa [Fintype.card_prod, Fintype.card_subtype, WeakSystem.count, WeakSystem.maps] using hc

/-- Every event depending only on the retained labels has the uniform induced
probability. This is proved by the explicit product equivalence. -/
theorem probability_truncate (S : WeakSystem (Fin n) (K + 1)) (B : Finset (Fin n))
    (hS : 0 < S.count) (P : ColorMap ↥B (K + 1) → Prop) [DecidablePred P] :
    probability (fun f : Feasible (truncate S B) => P (restrictMap B f.val)) =
      probability (fun f : Feasible (induced S B) => P f.val) := by
  obtain ⟨f, hf⟩ := S.count_pos_iff.mp hS
  let : Nonempty (Feasible (outsideSystem S B)) :=
    ⟨(splitState S B ⟨f, valid_truncate S B f hf⟩).2⟩
  change mean (fun f : Feasible (truncate S B) => indicator P (restrictMap B f.val)) =
    mean (fun f : Feasible (induced S B) => indicator P f.val)
  calc
    _ = mean (fun p : Feasible (induced S B) × Feasible (outsideSystem S B) =>
        indicator P p.1.val) := mean_equiv (stateEquiv S B) (fun p => indicator P p.1.val)
    _ = _ := by rw [mean_product]; simp only [mean_const]

/-- Generic count/probability correspondence, also valid for the induced
subtype label carrier. -/
theorem weakProbability_eq_probability {α : Type*} [Fintype α] [DecidableEq α]
    (S : WeakSystem α (K + 1)) (x y : α) :
    weakProbability S x y = probability (fun f : Feasible S => f.val x ≤ f.val y) := by
  symm
  unfold probability mean
  change (∑ z : Feasible S, if z.val x ≤ z.val y then (1 : ℚ) else 0) /
    Fintype.card (Feasible S) = _
  rw [← Finset.sum_subtype S.maps (fun f => S.mem_maps f)
    (fun f => if f x ≤ f y then (1 : ℚ) else 0), Fintype.card_subtype]
  unfold weakProbability WeakSystem.count
  rw [WeakSystem.maps_addRow]
  simp [WeakSystem.maps]

/-- The comparison probability used in the common-carrier proof is exactly the
comparison probability computed on the small induced ball system. -/
theorem weakProbability_truncate (S : WeakSystem (Fin n) (K + 1)) (B : Finset (Fin n))
    (hS : 0 < S.count) (x y : ↥B) :
    weakProbability (truncate S B) x.val y.val = weakProbability (induced S B) x y := by
  rw [weakProbability_eq_probability, weakProbability_eq_probability]
  exact probability_truncate S B hS (fun f => f x ≤ f y)

/-- Any event probability is its actual relative finite count. -/
theorem probability_eq_count {α : Type*} [Fintype α] [DecidableEq α]
    (S : WeakSystem α (K + 1)) (P : ColorMap α (K + 1) → Prop) [DecidablePred P] :
    probability (fun f : Feasible S => P f.val) =
      ((S.maps.filter P).card : ℚ) / S.count := by
  unfold probability mean indicator
  rw [← Finset.sum_subtype S.maps (fun f => S.mem_maps f)
    (fun f => if P f then (1 : ℚ) else 0), Fintype.card_subtype]
  simp [WeakSystem.count, WeakSystem.maps]

/-- Equal represented map sets give equal event laws, even if the row and wall
representations differ. -/
theorem probability_congr_valid {α : Type*} [Fintype α] [DecidableEq α]
    {S T : WeakSystem α (K + 1)} (h : ∀ f, S.Valid f ↔ T.Valid f)
    (P : ColorMap α (K + 1) → Prop) [DecidablePred P] :
    probability (fun f : Feasible S => P f.val) = probability (fun f : Feasible T => P f.val) := by
  have hm : S.maps = T.maps := by ext f; simp [h f]
  rw [probability_eq_count, probability_eq_count]
  simp only [WeakSystem.count, hm]

theorem weakProbability_congr {α : Type*} [Fintype α] [DecidableEq α]
    {S T : WeakSystem α (K + 1)} (h : ∀ f, S.Valid f ↔ T.Valid f) (x y : α) :
    weakProbability S x y = weakProbability T x y := by
  rw [weakProbability_eq_probability, weakProbability_eq_probability]
  exact probability_congr_valid h (fun f => f x ≤ f y)

end SortingAdversary.Optimal.TruncatedLaw
