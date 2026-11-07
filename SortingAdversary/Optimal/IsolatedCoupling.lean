import SortingAdversary.Optimal.TruncatedLaw

/-!
# Exact common-clock agreement at isolated labels

An isolated coordinate has only its old unary interval as its conditional law.
After one shared refresh the two chains agree at it exactly, regardless of its
width or palette location. No minimum-width condition or extra pin is needed.
-/

namespace SortingAdversary.Optimal.IsolatedCoupling

open WeakMaps LocalCoupling SystematicCoupling CouplingHistory BallSchedule
open FiniteProbability ClockStationarity LocalError TruncatedLaw GraphBalls

variable {n K Q : ℕ}

/-- No proper generating row is incident to this label. Reflexive rows have no
semantic effect and are deliberately permitted. -/
def Isolated (E : Fin n → Fin n → Bool) (v : Fin n) : Prop :=
  ∀ w, w ≠ v → E w v = false ∧ E v w = false

theorem isolated_iff_neighbors_empty (E : Fin n → Fin n → Bool) (v : Fin n) :
    Isolated E v ↔ neighbors E v = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hmem := (mem_neighbors E v w).mp hw
    have hh := h w hmem.1
    rcases hmem.2 with he | he <;> simp [hh.1, hh.2] at he
  · intro h w hw
    have hn : w ∉ neighbors E v := by simp [h]
    have hn' : ¬ (E v w = true ∨ E w v = true) := by
      intro he; exact hn ((mem_neighbors E v w).mpr ⟨hw, he⟩)
    exact ⟨Bool.eq_false_iff.mpr (fun he => hn' (Or.inr he)),
      Bool.eq_false_iff.mpr (fun he => hn' (Or.inl he))⟩

theorem isolated_truncate (S : WeakSystem (Fin n) (K + 1)) (B : Finset (Fin n))
    (v : Fin n) (h : Isolated S.edge v) : Isolated (truncate S B).edge v := by
  intro w hw
  have hh := h w hw
  simp [truncate, hh.1, hh.2]

theorem conditionalLower_isolated (S : WeakSystem (Fin n) (K + 1)) (v : Fin n)
    (h : Isolated S.edge v) (f : ColorMap (Fin n) (K + 1)) :
    conditionalLower S v f = S.lower v := by
  apply le_antisymm
  · apply (conditionalLower_le_iff S v f (S.lower v)).mpr
    refine ⟨le_rfl, ?_⟩
    intro w hw he
    simp [(h w hw).1] at he
  · exact ((conditionalLower_le_iff S v f _).mp le_rfl).1

theorem conditionalUpper_isolated (S : WeakSystem (Fin n) (K + 1)) (v : Fin n)
    (h : Isolated S.edge v) (f : ColorMap (Fin n) (K + 1)) :
    conditionalUpper S v f = S.upper v := by
  apply le_antisymm
  · exact ((le_conditionalUpper_iff S v f _).mp le_rfl).1
  · apply (le_conditionalUpper_iff S v f (S.upper v)).mpr
    refine ⟨le_rfl, ?_⟩
    intro w hw he
    simp [(h w hw).2] at he

/-- Shared clocks give exactly the same refreshed isolated color. -/
theorem refresh_isolated_eq (S T : WeakSystem (Fin n) (K + 1)) (v : Fin n)
    (hS : Isolated S.edge v) (hT : Isolated T.edge v)
    (hl : S.lower v = T.lower v) (hu : S.upper v = T.upper v)
    (f : State S) (g : State T) (u : ℚ) (hclock : 0 ≤ u ∧ u < 1) :
    refreshColor S v f.val f.property u hclock = refreshColor T v g.val g.property u hclock := by
  apply Fin.ext
  have heq : ((refreshColor S v f.val f.property u hclock).val : ℤ) =
      ((refreshColor T v g.val g.property u hclock).val : ℤ) := by
    calc
      _ = quantile (conditionalLower S v f.val).val (conditionalUpper S v f.val).val u :=
        refreshColor_val S v f.val f.property u hclock
      _ = quantile (conditionalLower T v g.val).val (conditionalUpper T v g.val).val u := by
        rw [conditionalLower_isolated S v hS, conditionalLower_isolated T v hT,
          conditionalUpper_isolated S v hS, conditionalUpper_isolated T v hT, hl, hu]
      _ = _ := (refreshColor_val T v g.val g.property u hclock).symm
  exact Int.natCast_inj.mp heq

/-- One systematic sweep agrees exactly at an isolated coordinate. -/
theorem sweep_isolated_eq (S T : WeakSystem (Fin n) (K + 1)) (v : Fin n)
    (hS : Isolated S.edge v) (hT : Isolated T.edge v)
    (hl : S.lower v = T.lower v) (hu : S.upper v = T.upper v)
    (f : State S) (g : State T) (r : Fin n → Fin Q) :
    (sweep S r f).val v = (sweep T r g).val v := by
  rw [sweep_apply, sweep_apply]
  exact refresh_isolated_eq S T v hS hT hl hu (after S r f v.val) (after T r g v.val)
    (gridClock (r v)) (gridClock_mem _)

/-- Every positive number of constructed sweeps gives exact isolated agreement,
independently of how the initial states were coupled. -/
theorem trajectory_isolated_eq {Ω : Type*}
    (S T : WeakSystem (Fin n) (K + 1)) (v : Fin n)
    (hS : Isolated S.edge v) (hT : Isolated T.edge v)
    (hl : S.lower v = T.lower v) (hu : S.upper v = T.upper v)
    (f : Ω → State S) (g : Ω → State T) (t : ℕ) (ht : 0 < t)
    (ω : History Ω n Q t) : (trajectory S f t ω).val v = (trajectory T g t ω).val v := by
  cases t with
  | zero => omega
  | succ t =>
      exact sweep_isolated_eq S T v hS hT hl hu
        (trajectory S f t ω.1) (trajectory T g t ω.1) ω.2

/-- A ball about an isolated vertex contains only that vertex, at every radius. -/
theorem ball_isolated (E : Fin n → Fin n → Bool) (v : Fin n) (h : Isolated E v) (r : ℕ) :
    ball E v r = {v} := by
  have hn := (isolated_iff_neighbors_empty E v).mp h
  induction r with
  | zero => rfl
  | succ r ih => simp [ball, closedNeighbors, hn, ih]

/-- Exact agreement at one coordinate leaves only the other coordinate's tail
and one near-tie event, for either orientation of the comparison. -/
theorem one_exact_comparison_error {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X Y X' Y' : Ω → ℚ) (hY : ∀ ω, Y ω = Y' ω) (a : ℚ) :
    (|probability (fun ω => X ω ≤ Y ω) - probability (fun ω => X' ω ≤ Y' ω)| ≤
      probability (fun ω => a < |X ω - X' ω|) + probability (fun ω => |X ω - Y ω| ≤ a)) ∧
    (|probability (fun ω => Y ω ≤ X ω) - probability (fun ω => Y' ω ≤ X' ω)| ≤
      probability (fun ω => a < |X ω - X' ω|) + probability (fun ω => |X ω - Y ω| ≤ a)) := by
  have hzero : probability (fun ω => 0 < |Y ω - Y' ω|) = 0 := by
    change mean (fun ω => if 0 < |Y ω - Y' ω| then 1 else 0) = 0
    simp only [hY, sub_self, abs_zero, lt_self_iff_false, if_false, mean_const]
  have hforward := comparison_probability_error X Y X' Y' a 0
  have hreverse := comparison_probability_error Y X Y' X' 0 a
  rw [hzero] at hforward hreverse
  constructor
  · simpa only [add_zero] using hforward
  · simpa only [zero_add, abs_sub_comm] using hreverse

/-- Arbitrarily narrow isolated labels couple exactly. Only the other mark's
component needs a width bound; both comparison orientations are certified. -/
theorem comparison_error_one_isolated (S T : WeakSystem (Fin n) (K + 1))
    (hS : 0 < S.count) (hT : 0 < T.count)
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (H M s : ℕ) (hs : 0 < s) (hM : 0 < M) (schedule : Schedule S T H M)
    (a : ℚ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hsmall : (M : ℚ) ^ 2 * a ≤ 1 / 8) (hlarge : 8 * (M : ℚ) ≤ s * a ^ H)
    (B : ℚ) (hB : 0 ≤ B)
    (hl : ∀ v, S.lower v = T.lower v) (hu : ∀ v, S.upper v = T.upper v)
    (hwidth : ∀ v ∈ schedule.interior 0, windowWidth S v ≤ B)
    (t : ℕ) (ht : 0 < t) (x y : Fin n) (hx : x ∈ schedule.interior t)
    (hisoS : Isolated S.edge y) (hisoT : Isolated T.edge y)
    (e : ℚ) (he : 0 < e) :
    (|LocalChoice.weakProbability S x y - LocalChoice.weakProbability T x y| ≤
      (B / e) ^ s / 2 ^ t + nearProbability S x y ((H : ℚ) * t + e)) ∧
    (|LocalChoice.weakProbability S y x - LocalChoice.weakProbability T y x| ≤
      (B / e) ^ s / 2 ^ t + nearProbability S x y ((H : ℚ) * t + e)) := by
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
  have hxt := trajectory_tail_of_initial_bound (Q := Q) S T horder f g H M s hs hM schedule a
    ha0 ha1 hsmall hlarge B hB (fun v hv ω =>
      (discrepancy_le_common_width S T (f ω) (g ω) v (hl v) (hu v)).trans (hwidth v hv))
    t x hx e he
  let X : History Ω n Q t → ℚ := fun ω => ((F ω).val x).val
  let Y : History Ω n Q t → ℚ := fun ω => ((F ω).val y).val
  let X' : History Ω n Q t → ℚ := fun ω => ((G ω).val x).val
  let Y' : History Ω n Q t → ℚ := fun ω => ((G ω).val y).val
  have hY : ∀ ω, Y ω = Y' ω := by
    intro ω
    exact congrArg (fun c : Fin (K + 1) => (c.val : ℚ))
      (trajectory_isolated_eq S T y hisoS hisoT (hl y) (hu y) f g t ht ω)
  have hcmp := one_exact_comparison_error X Y X' Y' hY ((H : ℚ) * t + e)
  have hSf : probability (fun ω => X ω ≤ Y ω) = LocalChoice.weakProbability S x y :=
    (probability_uniform S F hF (fun z => ((z x).val : ℚ) ≤ (z y).val)).trans
      (weakProbability_eq_state_probability S x y)
  have hTf : probability (fun ω => X' ω ≤ Y' ω) = LocalChoice.weakProbability T x y :=
    (probability_uniform T G hG (fun z => ((z x).val : ℚ) ≤ (z y).val)).trans
      (weakProbability_eq_state_probability T x y)
  have hSr : probability (fun ω => Y ω ≤ X ω) = LocalChoice.weakProbability S y x :=
    (probability_uniform S F hF (fun z => ((z y).val : ℚ) ≤ (z x).val)).trans
      (weakProbability_eq_state_probability S y x)
  have hTr : probability (fun ω => Y' ω ≤ X' ω) = LocalChoice.weakProbability T y x :=
    (probability_uniform T G hG (fun z => ((z y).val : ℚ) ≤ (z x).val)).trans
      (weakProbability_eq_state_probability T y x)
  have hnear : probability (fun ω => |X ω - Y ω| ≤ (H : ℚ) * t + e) =
      nearProbability S x y ((H : ℚ) * t + e) :=
    probability_uniform S F hF (fun z => |((z x).val : ℚ) - (z y).val| ≤ (H : ℚ) * t + e)
  rw [hSf, hTf, hSr, hTr, hnear] at hcmp
  change probability (fun ω => (H : ℚ) * t + e < |X ω - X' ω|) ≤ _ at hxt
  exact ⟨hcmp.1.trans (add_le_add hxt le_rfl), hcmp.2.trans (add_le_add hxt le_rfl)⟩

/-- Any event on two isolated labels has the same exact probability under two
systems with the same retained intervals at those labels. -/
theorem pair_event_eq (S T : WeakSystem (Fin n) (K + 1))
    (hS : 0 < S.count) (hT : 0 < T.count) (x y : Fin n)
    (hSx : Isolated S.edge x) (hTx : Isolated T.edge x)
    (hSy : Isolated S.edge y) (hTy : Isolated T.edge y)
    (hlx : S.lower x = T.lower x) (hux : S.upper x = T.upper x)
    (hly : S.lower y = T.lower y) (huy : S.upper y = T.upper y)
    (P : Fin (K + 1) → Fin (K + 1) → Prop) [DecidableRel P] :
    probability (fun f : State S => P (f.val x) (f.val y)) =
      probability (fun g : State T => P (g.val x) (g.val y)) := by
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
  let F := trajectory (Q := Q) S f 1
  let G := trajectory (Q := Q) T g 1
  have hF : UniformLaw S F := trajectory_uniform S f (initial_uniform_left S T)
    (fun v z => conditionalWidth_dvd_factorial S v z) 1
  have hG : UniformLaw T G := trajectory_uniform T g (initial_uniform_right S T)
    (fun v z => conditionalWidth_dvd_factorial T v z) 1
  have hleft := probability_uniform S F hF (fun z => P (z x) (z y))
  have hright := probability_uniform T G hG (fun z => P (z x) (z y))
  apply hleft.symm.trans
  apply Eq.trans _ hright
  apply mean_congr
  intro ω
  have hx := trajectory_isolated_eq S T x hSx hTx hlx hux f g 1 (by decide) ω
  have hy := trajectory_isolated_eq S T y hSy hTy hly huy f g 1 (by decide) ω
  change (if P ((F ω).val x) ((F ω).val y) then (1 : ℚ) else 0) =
    (if P ((G ω).val x) ((G ω).val y) then 1 else 0)
  rw [hx, hy]

end SortingAdversary.Optimal.IsolatedCoupling
