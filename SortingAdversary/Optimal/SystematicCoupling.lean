import SortingAdversary.Optimal.ClockContraction

/-!
# Explicit systematic sweeps

Labels in this module are indexed by a supplied topological order. A sweep
refreshes coordinates `0,...,n-1`, with the exact finite common clock established
in `LocalCoupling`. The process is constructed, not supplied as a mixing premise.
-/

namespace SortingAdversary.Optimal.SystematicCoupling

open WeakMaps LocalCoupling ClockContraction FiniteProbability

variable {n K Q : ℕ}

/-- A state carries the proof that all original weak rows and lists hold. -/
abbrev State (S : WeakSystem (Fin n) (K + 1)) := {f : ColorMap (Fin n) (K + 1) // S.Valid f}

/-- Refresh one coordinate with the corresponding shared clock. -/
def update (S : WeakSystem (Fin n) (K + 1)) (r : Fin n → Fin Q) (v : Fin n)
    (z : State S) : State S :=
  ⟨Function.update z.val v (refreshColor S v z.val z.property (gridClock (r v)) (gridClock_mem _)),
    refresh_valid S v z.val z.property (gridClock (r v)) (gridClock_mem _)⟩

@[simp] theorem update_apply_ne (S : WeakSystem (Fin n) (K + 1))
    (r : Fin n → Fin Q) (v x : Fin n) (z : State S) (hx : x ≠ v) :
    (update S r v z).val x = z.val x := by simp [update, Function.update_of_ne hx]

@[simp] theorem update_apply_self (S : WeakSystem (Fin n) (K + 1))
    (r : Fin n → Fin Q) (v : Fin n) (z : State S) :
    (update S r v z).val v =
      refreshColor S v z.val z.property (gridClock (r v)) (gridClock_mem _) := by simp [update]

/-- After `t` updates. Times beyond the end of the sweep leave the state fixed. -/
def after (S : WeakSystem (Fin n) (K + 1)) (r : Fin n → Fin Q) (z : State S) : ℕ → State S
  | 0 => z
  | t + 1 => if h : t < n then update S r ⟨t, h⟩ (after S r z t) else after S r z t

/-- A full bottom-to-top conditional sweep. -/
def sweep (S : WeakSystem (Fin n) (K + 1)) (r : Fin n → Fin Q) (z : State S) : State S :=
  after S r z n

theorem after_succ_apply_ne (S : WeakSystem (Fin n) (K + 1)) (r : Fin n → Fin Q)
    (z : State S) (t : ℕ) (x : Fin n) (hx : x.val ≠ t) :
    (after S r z (t + 1)).val x = (after S r z t).val x := by
  conv_lhs => rw [after]
  split_ifs with ht
  · exact update_apply_ne S r ⟨t, ht⟩ x _ (fun h => hx (congrArg Fin.val h))
  · rfl

/-- A coordinate not yet refreshed still has its old value. -/
theorem after_apply_old (S : WeakSystem (Fin n) (K + 1)) (r : Fin n → Fin Q)
    (z : State S) (t : ℕ) (x : Fin n) (hx : t ≤ x.val) :
    (after S r z t).val x = z.val x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [after_succ_apply_ne S r z t x (by omega)]
    exact ih (by omega)

/-- Once its own update has passed, a coordinate is never changed again. -/
theorem after_apply_stable (S : WeakSystem (Fin n) (K + 1)) (r : Fin n → Fin Q)
    (z : State S) (t u : ℕ) (x : Fin n) (hx : x.val < t) (htu : t ≤ u) :
    (after S r z u).val x = (after S r z t).val x := by
  induction u, htu using Nat.le_induction with
  | base => rfl
  | succ u htu ih =>
    rw [after_succ_apply_ne S r z u x (by omega), ih]

/-- The final value is the value selected at this coordinate's own update. -/
theorem sweep_apply (S : WeakSystem (Fin n) (K + 1)) (r : Fin n → Fin Q)
    (z : State S) (v : Fin n) :
    (sweep S r z).val v =
      refreshColor S v (after S r z v.val).val (after S r z v.val).property
        (gridClock (r v)) (gridClock_mem _) := by
  unfold sweep
  rw [after_apply_stable S r z (v.val + 1) n v (by omega) (by omega)]
  simp only [after, dif_pos v.isLt]
  exact update_apply_self S r v _

/-- Conditional endpoints agree between two systems with identical rows and
walls at the coordinate under consideration. Other rows may be truncated. -/
theorem conditionalLower_eq_of_incident (S T : WeakSystem (Fin n) (K + 1)) (v : Fin n)
    (f : ColorMap (Fin n) (K + 1)) (hl : S.lower v = T.lower v)
    (he : ∀ x, S.edge x v = T.edge x v) :
    conditionalLower S v f = conditionalLower T v f := by
  simp only [conditionalLower, hl, he]

theorem conditionalUpper_eq_of_incident (S T : WeakSystem (Fin n) (K + 1)) (v : Fin n)
    (f : ColorMap (Fin n) (K + 1)) (hu : S.upper v = T.upper v)
    (he : ∀ x, S.edge v x = T.edge v x) :
    conditionalUpper S v f = conditionalUpper T v f := by
  simp only [conditionalUpper, hu, he]

/-- Shared-clock discrepancy between two different models. Only rows incident
to the refreshed coordinate, and its own two walls, must coincide. -/
theorem refresh_discrepancy_two_systems (S T : WeakSystem (Fin n) (K + 1)) (v : Fin n)
    (f : State S) (g : State T) (u : ℚ) (hu : 0 ≤ u ∧ u < 1)
    (hlower : S.lower v = T.lower v) (hupper : S.upper v = T.upper v)
    (hin : ∀ x, S.edge x v = T.edge x v) (hout : ∀ x, S.edge v x = T.edge v x)
    (P B : ℚ) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (hpred : ∀ x, x ≠ v → S.edge x v = true → |((f.val x).val : ℚ) - (g.val x).val| ≤ P)
    (hsucc : ∀ x, x ≠ v → S.edge v x = true → |((f.val x).val : ℚ) - (g.val x).val| ≤ B) :
    |((refreshColor S v f.val f.property u hu).val : ℚ) -
      (refreshColor T v g.val g.property u hu).val| ≤ 1 + (1 - u) * P + u * B := by
  have hlo := conditionalLower_discrepancy S v f.val g.val P hP hpred
  have hhi := conditionalUpper_discrepancy S v f.val g.val B hB hsucc
  have hq := quantile_discrepancy
    (a := (conditionalLower S v f.val).val) (b := (conditionalUpper S v f.val).val)
    (c := (conditionalLower T v g.val).val) (d := (conditionalUpper T v g.val).val) hu.1 hu.2.le
  have hvf := congrArg (fun x : ℤ => (x : ℚ)) (refreshColor_val S v f.val f.property u hu)
  have hvg := congrArg (fun x : ℤ => (x : ℚ)) (refreshColor_val T v g.val g.property u hu)
  rw [← hvf, ← hvg] at hq
  simp only [Int.cast_natCast] at hq
  rw [← conditionalLower_eq_of_incident S T v g.val hlower hin,
    ← conditionalUpper_eq_of_incident S T v g.val hupper hout] at hq
  nlinarith

/-- Absolute coordinate discrepancy between two feasible states. -/
def discrepancy {S T : WeakSystem (Fin n) (K + 1)} (f : State S) (g : State T)
    (v : Fin n) : ℚ := |((f.val v).val : ℚ) - (g.val v).val|

theorem discrepancy_nonneg {S T : WeakSystem (Fin n) (K + 1)}
    (f : State S) (g : State T) (v : Fin n) : 0 ≤ discrepancy f g v := abs_nonneg _

/-- An actual sweep obeys the predecessor-new/successor-old recurrence.
The topological indexing and equality of local incident rows are the complete
structural premises; no recurrence or locality estimate is assumed. -/
theorem sweep_recurrence (S T : WeakSystem (Fin n) (K + 1))
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (r : Fin n → Fin Q) (f : State S) (g : State T) (v : Fin n)
    (hlower : S.lower v = T.lower v) (hupper : S.upper v = T.upper v)
    (hin : ∀ x, S.edge x v = T.edge x v) (hout : ∀ x, S.edge v x = T.edge v x)
    (P B : ℚ) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (hpred : ∀ x, x ≠ v → S.edge x v = true → discrepancy (sweep S r f) (sweep T r g) x ≤ P)
    (hsucc : ∀ x, x ≠ v → S.edge v x = true → discrepancy f g x ≤ B) :
    discrepancy (sweep S r f) (sweep T r g) v ≤
      1 + (1 - gridClock (r v)) * P + gridClock (r v) * B := by
  unfold discrepancy
  rw [sweep_apply, sweep_apply]
  apply refresh_discrepancy_two_systems S T v (after S r f v.val) (after T r g v.val)
    (gridClock (r v)) (gridClock_mem _) hlower hupper hin hout P B hP hB
  · intro x hx he
    have hidx := horder x v hx he
    have hvalS : (after S r f v.val).val x = (sweep S r f).val x :=
      (after_apply_stable S r f v.val n x hidx (Nat.le_of_lt v.isLt)).symm
    have hvalT : (after T r g v.val).val x = (sweep T r g).val x :=
      (after_apply_stable T r g v.val n x hidx (Nat.le_of_lt v.isLt)).symm
    rw [hvalS, hvalT]
    exact hpred x hx he
  · intro x hx he
    have hidx := horder v x (Ne.symm hx) he
    rw [after_apply_old S r f v.val x hidx.le, after_apply_old T r g v.val x hidx.le]
    exact hsucc x hx he

/-- A predecessor-closed local region. The two models have identical walls and
incident rows at its ancestors; old-state dependencies are all listed explicitly.
These are finite graph conditions, not distributional or contraction premises. -/
structure Region (S T : WeakSystem (Fin n) (K + 1)) (v : Fin n) (H M : ℕ) where
  ancestors : Finset (Fin n)
  dependencies : Finset (Fin n)
  root_mem : v ∈ ancestors
  ancestors_card : ancestors.card ≤ M
  dependencies_card : dependencies.card ≤ M
  predecessor_closed : ∀ x ∈ ancestors, ∀ y, y ≠ x → S.edge y x = true → y ∈ ancestors
  successor_covered : ∀ x ∈ ancestors, ∀ y, y ≠ x → S.edge x y = true → y ∈ dependencies
  lower_eq : ∀ x ∈ ancestors, S.lower x = T.lower x
  upper_eq : ∀ x ∈ ancestors, S.upper x = T.upper x
  incoming_eq : ∀ x ∈ ancestors, ∀ y, S.edge y x = T.edge y x
  outgoing_eq : ∀ x ∈ ancestors, ∀ y, S.edge x y = T.edge x y
  rank : Fin n → ℕ
  rank_strict : ∀ x ∈ ancestors, ∀ y ∈ ancestors,
    x ≠ y → S.edge x y = true → rank x < rank y
  height : ∀ x ∈ ancestors, rank x + 1 ≤ H

/-- Contraction for the actual two systematic sweeps, with a random coefficient
computed from precisely the clocks in the local predecessor region. -/
theorem local_sweep_contraction (S T : WeakSystem (Fin n) (K + 1))
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (r : Fin n → Fin Q) (f : State S) (g : State T) (v : Fin n) (H M : ℕ)
    (region : Region S T v H M) (B : ℚ) (hB : 0 ≤ B)
    (hdep : ∀ x ∈ region.dependencies, discrepancy f g x ≤ B) :
    discrepancy (sweep S r f) (sweep T r g) v ≤
      H + (1 - minClock region.ancestors r ^ H) * B := by
  let R : region.ancestors → region.ancestors → Prop :=
    fun x y => x.val ≠ y.val ∧ S.edge x.val y.val = true
  have hrank : ∀ {x y : region.ancestors}, R x y → region.rank x.val < region.rank y.val := by
    intro x y h
    exact region.rank_strict x.val x.property y.val y.property h.1 h.2
  have hheight : ∀ x : region.ancestors, region.rank x.val + 1 ≤ H :=
    fun x => region.height x.val x.property
  have h := sweep_contraction_of_height R (fun x => region.rank x.val) H hrank hheight
    (fun x => 1 - gridClock (r x.val))
    (fun x => discrepancy (sweep S r f) (sweep T r g) x.val)
    (minClock region.ancestors r) B (minClock_nonneg _ _) (minClock_le_one _ _) hB
    (fun x => ⟨minClock_le_member _ _ x.property, by linarith [(gridClock_mem (r x.val)).1]⟩)
    (by
      intro x E hE hpred
      have hrec := sweep_recurrence S T horder r f g x.val
        (region.lower_eq _ x.property) (region.upper_eq _ x.property)
        (region.incoming_eq _ x.property) (region.outgoing_eq _ x.property) E B hE hB
        (by
          intro y hy he
          exact hpred ⟨y, region.predecessor_closed _ x.property y hy he⟩ ⟨hy, he⟩)
        (by
          intro y hy he
          exact hdep y (region.successor_covered _ x.property y hy he))
      convert hrec using 1; ring)
  exact h ⟨v, region.root_mem⟩

end SortingAdversary.Optimal.SystematicCoupling
