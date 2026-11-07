import SortingAdversary.Optimal.GraphBalls
import SortingAdversary.Optimal.FiniteInsertion
import SortingAdversary.Optimal.LocalParameters

/-!
# Sparse geometry of the numerical closure

Floyd closure is identified with actual finite raw-row paths. This bounds the
insertion comparable count using the sparse generating degree and height,
without including unrelated retired public comparisons. The insertion width
is exactly the original propagated unary width used by the coupling.
-/

namespace SortingAdversary.Optimal.NumericalGeometry

open WeakMaps WeakMaps.WeakSystem GraphBalls SparseClosure CouplingHistory

variable {α : Type*} {n K : ℕ}

/-- Every row introduced by an elimination step follows an original path. -/
theorem along_sound (E R : Rows α) (ks : List α)
    (hR : ∀ x y, R x y = true → Relation.ReflTransGen (fun u v => E u v = true) x y) :
    ∀ x y, along R ks x y = true → Relation.ReflTransGen (fun u v => E u v = true) x y := by
  induction ks generalizing R with
  | nil => exact hR
  | cons k ks ih =>
    apply ih (via R k)
    intro x y h
    rcases (via_true R k x y).mp h with h | ⟨hxk, hky⟩
    · exact hR x y h
    · exact (hR x k hxk).trans (hR k y hky)

/-- Computable Floyd closure is precisely reflexive transitive raw reachability. -/
theorem closure_iff_reach (E : Rows (Fin n)) (x y : Fin n) :
    closure E x y = true ↔ Relation.ReflTransGen (fun u v => E u v = true) x y := by
  constructor
  · apply along_sound E (reflexive E) (List.finRange n)
    intro u v h
    have h' : E u v = true ∨ u = v := by simpa [reflexive] using h
    rcases h' with h' | rfl
    · exact .single h'
    · exact .refl
  · intro h
    induction h with
    | refl => exact closure_refl E x
    | @tail u v _ huv ih => exact closure_trans E x u v ih (closure_old E huv)

/-- Reflexive rows do not affect proper directed paths. -/
theorem reach_iff_arcReach (E : α → α → Bool) (x y : α) :
    Relation.ReflTransGen (fun u v => E u v = true) x y ↔
      Relation.ReflTransGen (Arc E) x y := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail u v _ huv ih =>
      by_cases heq : u = v
      · subst v; exact ih
      · exact ih.tail ⟨heq, huv⟩
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ huv ih => exact ih.tail huv.2

/-- A proper raw path either stays at its initial vertex or increases rank. -/
theorem reach_rank (E : α → α → Bool) (rank : α → ℕ)
    (hstrict : ∀ x y, Arc E x y → rank x < rank y) {x y : α}
    (h : Relation.ReflTransGen (Arc E) x y) : x = y ∨ rank x < rank y := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail u v _ huv ih =>
    have h := hstrict u v huv
    rcases ih with rfl | ih
    · exact Or.inr h
    · exact Or.inr (ih.trans h)

theorem closure_antisymm (E : Rows (Fin n)) (rank : Fin n → ℕ)
    (hstrict : ∀ x y, Arc E x y → rank x < rank y) (x y : Fin n)
    (hxy : closure E x y = true) (hyx : closure E y x = true) : x = y := by
  have hxy' := reach_rank E rank hstrict ((reach_iff_arcReach E x y).mp
    ((closure_iff_reach E x y).mp hxy))
  have hyx' := reach_rank E rank hstrict ((reach_iff_arcReach E y x).mp
    ((closure_iff_reach E y x).mp hyx))
  rcases hxy' with h | h
  · exact h
  rcases hyx' with h' | h'
  · exact h'.symm
  · omega

/-- The actual numerical closure is an ordered system for insertion. -/
def orderedSystem (S : WeakSystem (Fin n) (K + 1)) (rank : Fin n → ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y) : FiniteInsertion.OrderedSystem n K where
  system := closeSystem S
  closed := closeSystem_closed S
  antisymm := by
    intro x y hxy hyx
    simp only [closeSystem, lookup_tableClosure] at hxy hyx
    exact closure_antisymm S.edge rank hstrict x y hxy hyx

/-- A numerical comparable vertex lies in the bounded raw undirected ball. -/
theorem comparable_mem_ball (E : Rows (Fin n)) (rank : Fin n → ℕ) (H : ℕ)
    (hstrict : ∀ x y, Arc E x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H) {x v : Fin n}
    (h : closure E x v = true ∨ closure E v x = true) : x ∈ ball E v (H - 1) := by
  rcases h with h | h
  · exact ancestor_mem_ball E rank H hstrict hheight
      ((reach_iff_arcReach E x v).mp ((closure_iff_reach E x v).mp h))
  · exact ball_symm E (ancestor_mem_ball E rank H hstrict hheight
      ((reach_iff_arcReach E v x).mp ((closure_iff_reach E v x).mp h)))

/-- Comparable count in the numerical closure is bounded using only raw degree
and directed height. This is stronger than the manuscript's `2M` allowance. -/
theorem comparableCount_le (S : WeakSystem (Fin n) (K + 1)) (rank : Fin n → ℕ) (H d : ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d) (v : Fin n) :
    FiniteInsertion.comparableCount (orderedSystem S rank hstrict) v ≤ (d + 1) ^ (H + 1) := by
  calc
    _ ≤ (ball S.edge v (H - 1)).card := by
      apply Finset.card_le_card
      intro x hx
      have hx' : x ≠ v ∧ (closure S.edge x v = true ∨ closure S.edge v x = true) := by
        simpa [FiniteInsertion.comparableCount, orderedSystem, closeSystem, lookup_tableClosure] using hx
      exact comparable_mem_ball S.edge rank H hstrict hheight hx'.2
    _ ≤ (d + 1) ^ (H - 1) := ball_card_le S.edge d hdegree v _
    _ ≤ (d + 1) ^ (H + 1) := Nat.pow_le_pow_right (by omega) (by omega)

/-- The insertion interval equals the old propagated interval used in the
sparse local model, including the inclusive endpoint correction. -/
theorem insertion_width_eq (S : WeakSystem (Fin n) (K + 1)) (rank : Fin n → ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y) (hS : 0 < S.count) (v : Fin n) :
    (FiniteInsertion.windowWidth (orderedSystem S rank hstrict) v : ℚ) =
      CouplingHistory.windowWidth (propagateSystem S) v := by
  obtain ⟨f, hf⟩ := S.count_pos_iff.mp hS
  have hw := (closeSystem S).valid_between_windows f ((closeSystem_valid S f).mpr hf) v
  have hle : ((closeSystem S).effectiveLower v).val ≤ ((closeSystem S).effectiveUpper v).val :=
    hw.1.trans hw.2
  change ((((closeSystem S).effectiveUpper v).val + 1 - ((closeSystem S).effectiveLower v).val : ℕ) : ℚ) = _
  rw [Nat.cast_sub (by omega : ((closeSystem S).effectiveLower v).val ≤
    ((closeSystem S).effectiveUpper v).val + 1), Nat.cast_add, Nat.cast_one]
  unfold CouplingHistory.windowWidth propagateSystem
  ring

/-- Propagation already supplies the extremal feasible lower map, so repeating
it cannot strengthen a lower endpoint. -/
theorem propagated_effectiveLower (S : WeakSystem (Fin n) (K + 1)) (hS : 0 < S.count) (v : Fin n) :
    (closeSystem (propagateSystem S)).effectiveLower v = (propagateSystem S).lower v := by
  have hc := closeSystem_closed S
  have hne : ∃ f, (closeSystem S).Valid f := by
    obtain ⟨f, hf⟩ := S.count_pos_iff.mp hS
    exact ⟨f, (closeSystem_valid S f).mpr hf⟩
  have hf := (closeSystem S).effectiveLower_valid hc ((closeSystem S).feasible_iff_windows hc |>.mp hne)
  have hsp : (propagateSystem S).Valid (closeSystem S).effectiveLower :=
    (propagateSystem_valid S _).mpr ((closeSystem_valid S _).mp hf)
  have hcp := (closeSystem_valid (propagateSystem S) _).mpr hsp
  apply le_antisymm
  · exact ((closeSystem (propagateSystem S)).valid_between_windows _ hcp v).1
  · exact (closeSystem (propagateSystem S)).lower_le_effectiveLower
      ((closeSystem_closed (propagateSystem S)).refl v)

/-- The upper endpoints are likewise unchanged by a second propagation. -/
theorem propagated_effectiveUpper (S : WeakSystem (Fin n) (K + 1)) (hS : 0 < S.count) (v : Fin n) :
    (closeSystem (propagateSystem S)).effectiveUpper v = (propagateSystem S).upper v := by
  have hc := closeSystem_closed S
  have hne : ∃ f, (closeSystem S).Valid f := by
    obtain ⟨f, hf⟩ := S.count_pos_iff.mp hS
    exact ⟨f, (closeSystem_valid S f).mpr hf⟩
  have hf := (closeSystem S).effectiveUpper_valid hc ((closeSystem S).feasible_iff_windows hc |>.mp hne)
  have hsp : (propagateSystem S).Valid (closeSystem S).effectiveUpper :=
    (propagateSystem_valid S _).mpr ((closeSystem_valid S _).mp hf)
  have hcp := (closeSystem_valid (propagateSystem S) _).mpr hsp
  apply le_antisymm
  · exact (closeSystem (propagateSystem S)).effectiveUpper_le_upper
      ((closeSystem_closed (propagateSystem S)).refl v)
  · exact ((closeSystem (propagateSystem S)).valid_between_windows _ hcp v).2

/-- The actual propagated sparse law satisfies the insertion bound with an
explicit constant depending only on sparse degree and height. -/
theorem near_bound_propagated (S : WeakSystem (Fin n) (K + 1)) (hS : 0 < S.count)
    (rank : Fin n → ℕ) (H d : ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d)
    {x y : Fin n} (hxy : y ≠ x) (z : ℚ) (hz : 0 ≤ z) :
    LocalError.nearProbability (propagateSystem S) x y z ≤
      (LocalParameters.insertionConstant ((d + 1) ^ (H + 1)) : ℚ) * (2 * z + 1) /
        CouplingHistory.windowWidth (propagateSystem S) x := by
  let C := orderedSystem S rank hstrict
  have hc : 0 < C.system.count := by simpa [C, orderedSystem] using hS
  have hnear := FiniteInsertion.near_probability_bound C hc hxy z hz
  have hcnum := comparableCount_le S rank H d hstrict hheight hdegree x
  have hfactor : (2 * 4 ^ FiniteInsertion.comparableCount C x : ℚ) ≤
      LocalParameters.insertionConstant ((d + 1) ^ (H + 1)) := by
    have hnat : 2 * 4 ^ FiniteInsertion.comparableCount C x ≤
        LocalParameters.insertionConstant ((d + 1) ^ (H + 1)) :=
      Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) (by
        change FiniteInsertion.comparableCount (orderedSystem S rank hstrict) x ≤ _
        omega))
    exact_mod_cast hnat
  have hw : 0 ≤ CouplingHistory.windowWidth (propagateSystem S) x := by
    obtain ⟨f, hf⟩ := S.count_pos_iff.mp hS
    exact (CouplingHistory.windowWidth_pos (propagateSystem S)
      ⟨f, (propagateSystem_valid S f).mpr hf⟩ x).le
  calc
    _ = LocalError.nearProbability C.system x y z :=
      (FiniteInsertion.nearProbability_propagate S x y z).trans
        (FiniteInsertion.nearProbability_close S x y z).symm
    _ ≤ _ := hnear
    _ = (2 * 4 ^ FiniteInsertion.comparableCount C x : ℚ) * (2 * z + 1) /
        CouplingHistory.windowWidth (propagateSystem S) x := by
      rw [insertion_width_eq S rank hstrict hS x]
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hfactor (by linarith)) hw

theorem nearProbability_symm (S : WeakSystem (Fin n) (K + 1)) (x y : Fin n) (z : ℚ) :
    LocalError.nearProbability S x y z = LocalError.nearProbability S y x z := by
  simp only [LocalError.nearProbability, abs_sub_comm]

/-- Use insertion at the wider of the two marked intervals, including queries
whose marks belong to components with unrelated width scales. -/
theorem near_bound_max_propagated (S : WeakSystem (Fin n) (K + 1)) (hS : 0 < S.count)
    (rank : Fin n → ℕ) (H d : ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d)
    {x y : Fin n} (hxy : y ≠ x) (z : ℚ) (hz : 0 ≤ z) :
    LocalError.nearProbability (propagateSystem S) x y z ≤
      (LocalParameters.insertionConstant ((d + 1) ^ (H + 1)) : ℚ) * (2 * z + 1) /
        max (CouplingHistory.windowWidth (propagateSystem S) x)
          (CouplingHistory.windowWidth (propagateSystem S) y) := by
  by_cases h : CouplingHistory.windowWidth (propagateSystem S) y ≤
      CouplingHistory.windowWidth (propagateSystem S) x
  · rw [max_eq_left h]
    exact near_bound_propagated S hS rank H d hstrict hheight hdegree hxy z hz
  · rw [max_eq_right (le_of_not_ge h), nearProbability_symm]
    exact near_bound_propagated S hS rank H d hstrict hheight hdegree hxy.symm z hz

/-- The insertion factor is controlled by sparse numerical comparability. -/
theorem insertionFactor_le (S : WeakSystem (Fin n) (K + 1)) (rank : Fin n → ℕ) (H d : ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d) (x : Fin n) :
    (2 * 4 ^ FiniteInsertion.comparableCount (orderedSystem S rank hstrict) x : ℚ) ≤
      LocalParameters.insertionConstant ((d + 1) ^ (H + 1)) := by
  have hc := comparableCount_le S rank H d hstrict hheight hdegree x
  have hnat : 2 * 4 ^ FiniteInsertion.comparableCount (orderedSystem S rank hstrict) x ≤
      LocalParameters.insertionConstant ((d + 1) ^ (H + 1)) :=
    Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) (by omega))
  exact_mod_cast hnat

theorem thresholdNearProbability_congr {S T : WeakSystem (Fin n) (K + 1)}
    (h : ∀ f, S.Valid f ↔ T.Valid f) (x : Fin n) (c : ℕ) (z : ℚ) :
    FiniteInsertion.thresholdNearProbability S x c z = FiniteInsertion.thresholdNearProbability T x c z := by
  have hm : S.maps = T.maps := by ext f; simp [h f]
  rw [FiniteInsertion.thresholdNearProbability_eq_count, FiniteInsertion.thresholdNearProbability_eq_count]
  simp only [count, hm]

/-- Fixed-threshold insertion estimate for the same propagated sparse model
used by the actual CDF coupling. -/
theorem threshold_near_bound_propagated (S : WeakSystem (Fin n) (K + 1)) (hS : 0 < S.count)
    (rank : Fin n → ℕ) (H d : ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d)
    (x : Fin n) (c : ℕ) (z : ℚ) (hz : 0 ≤ z) :
    FiniteInsertion.thresholdNearProbability (propagateSystem S) x c z ≤
      (LocalParameters.insertionConstant ((d + 1) ^ (H + 1)) : ℚ) * (2 * z + 1) /
        CouplingHistory.windowWidth (propagateSystem S) x := by
  let C := orderedSystem S rank hstrict
  have hc : 0 < C.system.count := by simpa [C, orderedSystem] using hS
  have hnear := FiniteInsertion.threshold_near_probability_bound C hc x c z hz
  have hfactor := insertionFactor_le S rank H d hstrict hheight hdegree x
  have hw : 0 ≤ CouplingHistory.windowWidth (propagateSystem S) x := by
    obtain ⟨f, hf⟩ := S.count_pos_iff.mp hS
    exact (CouplingHistory.windowWidth_pos (propagateSystem S)
      ⟨f, (propagateSystem_valid S f).mpr hf⟩ x).le
  calc
    _ = FiniteInsertion.thresholdNearProbability C.system x c z :=
      thresholdNearProbability_congr
        (fun f => (propagateSystem_valid S f).trans (closeSystem_valid S f).symm) x c z
    _ ≤ _ := hnear
    _ = (2 * 4 ^ FiniteInsertion.comparableCount C x : ℚ) * (2 * z + 1) /
        CouplingHistory.windowWidth (propagateSystem S) x := by
      rw [insertion_width_eq S rank hstrict hS x]
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hfactor (by linarith)) hw

end SortingAdversary.Optimal.NumericalGeometry
