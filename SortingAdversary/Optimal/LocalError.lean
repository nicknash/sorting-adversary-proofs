import SortingAdversary.Optimal.CouplingHistory
import SortingAdversary.Optimal.ClockStationarity
import SortingAdversary.Optimal.LocalChoice

/-!
# Comparison error of the actual finite coupling

Both marginals are proved to be the uniform feasible weak-map laws. The
comparison error is bounded by the explicit geometric coupling tail and a
near-tie probability in the full system. No local-versus-full probability
approximation is assumed.
-/

namespace SortingAdversary.Optimal.LocalError

open WeakMaps LocalCoupling ClockContraction FiniteProbability SystematicCoupling
open LocalMoments CouplingHistory ClockStationarity
open scoped BigOperators

variable {n K Q : ℕ}

section Marginals
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] [NeZero Q]

/-- Repeated constructed sweeps preserve a supplied uniform initial marginal. -/
theorem trajectory_uniform (S : WeakSystem (Fin n) (K + 1)) (f : Ω → State S)
    (hf : UniformLaw S f) (hdiv : ∀ v (z : State S), conditionalWidth S v z.val ∣ Q)
    (t : ℕ) : UniformLaw S (trajectory (Q := Q) S f t) := by
  induction t with
  | zero => exact hf
  | succ t ih =>
    intro φ
    calc
      _ = mean (fun p : History Ω n Q t × (Fin n → Fin Q) =>
          φ (sweep S p.2 (trajectory S f t p.1)).val) := by
        apply mean_congr_fintype
        intro ω
        rfl
      _ = _ := sweep_uniform S (trajectory S f t) ih hdiv φ

end Marginals

/-- Independent initial uniform states give the correct first marginal. -/
theorem initial_uniform_left (S T : WeakSystem (Fin n) (K + 1))
    [Nonempty (State T)] : UniformLaw S (fun p : State S × State T => p.1) := by
  intro φ
  rw [mean_product]
  simp only [mean_const]

/-- Independent initial uniform states give the correct second marginal. -/
theorem initial_uniform_right (S T : WeakSystem (Fin n) (K + 1))
    [Nonempty (State S)] : UniformLaw T (fun p : State S × State T => p.2) := by
  intro φ
  rw [mean_product]
  simp only [mean_const]

/-- Every event has the correct probability under a proved uniform law. -/
theorem probability_uniform {Ω : Type*} [Fintype Ω]
    (S : WeakSystem (Fin n) (K + 1)) (f : Ω → State S) (hf : UniformLaw S f)
    (P : ColorMap (Fin n) (K + 1) → Prop) [DecidablePred P] :
    probability (fun ω => P (f ω).val) = probability (fun z : State S => P z.val) :=
  hf (fun g => indicator P g)

/-- The finite probability of a weak comparison is exactly its branch-count
ratio. Equality maps are included, as required by the adversary. -/
theorem weakProbability_eq_state_probability (S : WeakSystem (Fin n) (K + 1)) (x y : Fin n) :
    probability (fun z : State S => ((z.val x).val : ℚ) ≤ (z.val y).val) =
      LocalChoice.weakProbability S x y := by
  unfold probability mean
  change (∑ z : State S, if ((z.val x).val : ℚ) ≤ (z.val y).val then (1 : ℚ) else 0) /
    Fintype.card (State S) = _
  rw [sum_states S (fun f => if ((f x).val : ℚ) ≤ (f y).val then 1 else 0), card_states]
  simp only [Nat.cast_le]
  unfold LocalChoice.weakProbability WeakSystem.count
  rw [WeakSystem.maps_addRow]
  simp only [Fin.le_def]
  simp

/-- Near-tie probability in the exact uniform full weak-map model. -/
def nearProbability (S : WeakSystem (Fin n) (K + 1)) (x y : Fin n) (z : ℚ) : ℚ :=
  probability (fun f : State S => |((f.val x).val : ℚ) - (f.val y).val| ≤ z)

/-- A complete finite coupling comparison bound, with both marginals and all
clock expectations proved. The remaining near-tie term is a count property of
the full weak system; the insertion theorem bounds it separately. -/
theorem comparison_error_of_schedule (S T : WeakSystem (Fin n) (K + 1))
    (hS : 0 < S.count) (hT : 0 < T.count)
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (H M s : ℕ) (hs : 0 < s) (hM : 0 < M) (schedule : Schedule S T H M)
    (a : ℚ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hsmall : (M : ℚ) ^ 2 * a ≤ 1 / 8) (hlarge : 8 * (M : ℚ) ≤ s * a ^ H)
    (t : ℕ) (x y : Fin n) (hx : x ∈ schedule.interior t) (hy : y ∈ schedule.interior t)
    (e : ℚ) (he : 0 < e) :
    |LocalChoice.weakProbability S x y - LocalChoice.weakProbability T x y| ≤
      2 * ((K : ℚ) / e) ^ s / 2 ^ t + nearProbability S x y (2 * ((H : ℚ) * t + e)) := by
  let Q := (K + 1).factorial
  let : NeZero Q := ⟨Nat.factorial_ne_zero _⟩
  let : Nonempty (State S) := by
    obtain ⟨f, hf⟩ := S.count_pos_iff.mp hS
    exact ⟨⟨f, hf⟩⟩
  let : Nonempty (State T) := by
    obtain ⟨f, hf⟩ := T.count_pos_iff.mp hT
    exact ⟨⟨f, hf⟩⟩
  let Ω := State S × State T
  let f : Ω → State S := Prod.fst
  let g : Ω → State T := Prod.snd
  let F := trajectory (Q := Q) S f t
  let G := trajectory (Q := Q) T g t
  have hF : UniformLaw S F := trajectory_uniform S f (initial_uniform_left S T)
    (fun v z => conditionalWidth_dvd_factorial S v z) t
  have hG : UniformLaw T G := trajectory_uniform T g (initial_uniform_right S T)
    (fun v z => conditionalWidth_dvd_factorial T v z) t
  have hxt := trajectory_tail (Q := Q) S T horder f g H M s hs hM schedule a
    ha0 ha1 hsmall hlarge t x hx e he
  have hyt := trajectory_tail (Q := Q) S T horder f g H M s hs hM schedule a
    ha0 ha1 hsmall hlarge t y hy e he
  let X : History Ω n Q t → ℚ := fun ω => ((F ω).val x).val
  let Y : History Ω n Q t → ℚ := fun ω => ((F ω).val y).val
  let X' : History Ω n Q t → ℚ := fun ω => ((G ω).val x).val
  let Y' : History Ω n Q t → ℚ := fun ω => ((G ω).val y).val
  have hcmp := comparison_probability_error X Y X' Y' ((H : ℚ) * t + e) ((H : ℚ) * t + e)
  have hleft : probability (fun ω => X ω ≤ Y ω) = LocalChoice.weakProbability S x y := by
    exact (probability_uniform S F hF (fun z => ((z x).val : ℚ) ≤ (z y).val)).trans
      (weakProbability_eq_state_probability S x y)
  have hright : probability (fun ω => X' ω ≤ Y' ω) = LocalChoice.weakProbability T x y := by
    exact (probability_uniform T G hG (fun z => ((z x).val : ℚ) ≤ (z y).val)).trans
      (weakProbability_eq_state_probability T x y)
  have hnear : probability (fun ω => |X ω - Y ω| ≤ ((H : ℚ) * t + e) + ((H : ℚ) * t + e)) =
      nearProbability S x y (2 * ((H : ℚ) * t + e)) := by
    simpa only [nearProbability, X, Y, two_mul] using probability_uniform S F hF
      (fun z => |((z x).val : ℚ) - (z y).val| ≤ 2 * ((H : ℚ) * t + e))
  rw [hleft, hright, hnear] at hcmp
  change probability (fun ω => (H : ℚ) * t + e < |X ω - X' ω|) ≤ _ at hxt
  change probability (fun ω => (H : ℚ) * t + e < |Y ω - Y' ω|) ≤ _ at hyt
  calc
    _ ≤ probability (fun ω => (H : ℚ) * t + e < |X ω - X' ω|) +
        probability (fun ω => (H : ℚ) * t + e < |Y ω - Y' ω|) +
        nearProbability S x y (2 * ((H : ℚ) * t + e)) := hcmp
    _ ≤ ((K : ℚ) / e) ^ s / 2 ^ t + ((K : ℚ) / e) ^ s / 2 ^ t +
        nearProbability S x y (2 * ((H : ℚ) * t + e)) :=
      add_le_add (add_le_add hxt hyt) le_rfl
    _ = _ := by ring

/-- Component-sensitive comparison bound. The two marks may have different
width scales and use distinct shrinking-interior schedules inside the same
actual common-clock coupling. Initial discrepancy bounds follow from the
retained unary walls, not from the global palette span. -/
theorem comparison_error_of_width_schedules (S T : WeakSystem (Fin n) (K + 1))
    (hS : 0 < S.count) (hT : 0 < T.count)
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (H M s : ℕ) (hs : 0 < s) (hM : 0 < M) (scheduleX scheduleY : Schedule S T H M)
    (a : ℚ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hsmall : (M : ℚ) ^ 2 * a ≤ 1 / 8) (hlarge : 8 * (M : ℚ) ≤ s * a ^ H)
    (Bx By : ℚ) (hBx : 0 ≤ Bx) (hBy : 0 ≤ By)
    (hl : ∀ v, S.lower v = T.lower v) (hu : ∀ v, S.upper v = T.upper v)
    (hwidthX : ∀ v ∈ scheduleX.interior 0, windowWidth S v ≤ Bx)
    (hwidthY : ∀ v ∈ scheduleY.interior 0, windowWidth S v ≤ By)
    (t : ℕ) (x y : Fin n) (hx : x ∈ scheduleX.interior t) (hy : y ∈ scheduleY.interior t)
    (ex ey : ℚ) (hex : 0 < ex) (hey : 0 < ey) :
    |LocalChoice.weakProbability S x y - LocalChoice.weakProbability T x y| ≤
      (Bx / ex) ^ s / 2 ^ t + (By / ey) ^ s / 2 ^ t +
        nearProbability S x y (((H : ℚ) * t + ex) + ((H : ℚ) * t + ey)) := by
  let Q := (K + 1).factorial
  let : NeZero Q := ⟨Nat.factorial_ne_zero _⟩
  let : Nonempty (State S) := by
    obtain ⟨f, hf⟩ := S.count_pos_iff.mp hS
    exact ⟨⟨f, hf⟩⟩
  let : Nonempty (State T) := by
    obtain ⟨f, hf⟩ := T.count_pos_iff.mp hT
    exact ⟨⟨f, hf⟩⟩
  let Ω := State S × State T
  let f : Ω → State S := Prod.fst
  let g : Ω → State T := Prod.snd
  let F := trajectory (Q := Q) S f t
  let G := trajectory (Q := Q) T g t
  have hF : UniformLaw S F := trajectory_uniform S f (initial_uniform_left S T)
    (fun v z => conditionalWidth_dvd_factorial S v z) t
  have hG : UniformLaw T G := trajectory_uniform T g (initial_uniform_right S T)
    (fun v z => conditionalWidth_dvd_factorial T v z) t
  have hxt := trajectory_tail_of_initial_bound (Q := Q) S T horder f g H M s hs hM scheduleX a
    ha0 ha1 hsmall hlarge Bx hBx (fun v hv ω =>
      (discrepancy_le_common_width S T (f ω) (g ω) v (hl v) (hu v)).trans (hwidthX v hv))
    t x hx ex hex
  have hyt := trajectory_tail_of_initial_bound (Q := Q) S T horder f g H M s hs hM scheduleY a
    ha0 ha1 hsmall hlarge By hBy (fun v hv ω =>
      (discrepancy_le_common_width S T (f ω) (g ω) v (hl v) (hu v)).trans (hwidthY v hv))
    t y hy ey hey
  let X : History Ω n Q t → ℚ := fun ω => ((F ω).val x).val
  let Y : History Ω n Q t → ℚ := fun ω => ((F ω).val y).val
  let X' : History Ω n Q t → ℚ := fun ω => ((G ω).val x).val
  let Y' : History Ω n Q t → ℚ := fun ω => ((G ω).val y).val
  have hcmp := comparison_probability_error X Y X' Y' ((H : ℚ) * t + ex) ((H : ℚ) * t + ey)
  have hleft : probability (fun ω => X ω ≤ Y ω) = LocalChoice.weakProbability S x y := by
    exact (probability_uniform S F hF (fun z => ((z x).val : ℚ) ≤ (z y).val)).trans
      (weakProbability_eq_state_probability S x y)
  have hright : probability (fun ω => X' ω ≤ Y' ω) = LocalChoice.weakProbability T x y := by
    exact (probability_uniform T G hG (fun z => ((z x).val : ℚ) ≤ (z y).val)).trans
      (weakProbability_eq_state_probability T x y)
  have hnear : probability (fun ω => |X ω - Y ω| ≤ ((H : ℚ) * t + ex) + ((H : ℚ) * t + ey)) =
      nearProbability S x y (((H : ℚ) * t + ex) + ((H : ℚ) * t + ey)) := by
    exact probability_uniform S F hF
      (fun z => |((z x).val : ℚ) - (z y).val| ≤ ((H : ℚ) * t + ex) + ((H : ℚ) * t + ey))
  rw [hleft, hright, hnear] at hcmp
  change probability (fun ω => (H : ℚ) * t + ex < |X ω - X' ω|) ≤ _ at hxt
  change probability (fun ω => (H : ℚ) * t + ey < |Y ω - Y' ω|) ≤ _ at hyt
  exact hcmp.trans (add_le_add (add_le_add hxt hyt) le_rfl)

end SortingAdversary.Optimal.LocalError
