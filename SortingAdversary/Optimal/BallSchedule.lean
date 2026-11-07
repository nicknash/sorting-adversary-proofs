import SortingAdversary.Optimal.GraphBalls
import SortingAdversary.Optimal.LocalError

/-!
# Coupling schedules from actual truncated sparse balls

The truncated system retains every original unary wall and removes precisely
those raw rows with an endpoint outside the chosen ball union. For a mark, the
interior after `j` sweeps is the radius `H*(t-j)` ball. The schedule conditions
are proved here from the raw degree and a directed height witness.
-/

namespace SortingAdversary.Optimal.BallSchedule

open WeakMaps GraphBalls SystematicCoupling CouplingHistory

variable {n K : ℕ}

/-- Keep the old carrier and unary lists, but only rows internal to `B`. The
outside labels are independent factors and do not change the law inside `B`. -/
def truncate (S : WeakSystem (Fin n) (K + 1)) (B : Finset (Fin n)) :
    WeakSystem (Fin n) (K + 1) where
  edge x y := if x ∈ B ∧ y ∈ B then S.edge x y else false
  lower := S.lower
  upper := S.upper

theorem valid_truncate (S : WeakSystem (Fin n) (K + 1)) (B : Finset (Fin n))
    (f : ColorMap (Fin n) (K + 1)) (hf : S.Valid f) : (truncate S B).Valid f := by
  refine ⟨hf.1, ?_⟩
  intro x y h
  change (if x ∈ B ∧ y ∈ B then S.edge x y else false) = true at h
  split_ifs at h with hB
  exact hf.2 x y h

theorem truncate_count_pos (S : WeakSystem (Fin n) (K + 1)) (B : Finset (Fin n))
    (hS : 0 < S.count) : 0 < (truncate S B).count := by
  obtain ⟨f, hf⟩ := S.count_pos_iff.mp hS
  exact (truncate S B).count_pos_iff.mpr ⟨f, valid_truncate S B f hf⟩

/-- Actual directed ancestors, including the vertex itself. The set is used
only in the proof coupling; the ball itself is explicitly computable. -/
noncomputable def ancestors (E : Fin n → Fin n → Bool) (v : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun x => Relation.ReflTransGen (Arc E) x v)

@[simp] theorem mem_ancestors (E : Fin n → Fin n → Bool) (v x : Fin n) :
    x ∈ ancestors E v ↔ Relation.ReflTransGen (Arc E) x v := by
  classical
  simp [ancestors]

theorem ancestors_subset_ball (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (H : ℕ)
    (hstrict : ∀ x y, Arc E x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H) (v : Fin n) :
    ancestors E v ⊆ ball E v (H - 1) := by
  intro x hx
  exact ancestor_mem_ball E rank H hstrict hheight ((mem_ancestors E v x).mp hx)

/-- Every old-state dependency is a successor of a directed ancestor, hence
within distance `H` in the raw generating graph. -/
theorem ancestor_neighbor_mem_ball (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (H : ℕ)
    (hstrict : ∀ x y, Arc E x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H) (v x y : Fin n)
    (hx : x ∈ ancestors E v) (hy : y ∈ closedNeighbors E x) : y ∈ ball E v H := by
  have hxball := ancestors_subset_ball E rank H hstrict hheight v hx
  have hyball := (mem_ball_one E x y).mpr hy
  have h := mem_ball_add E hxball hyball
  have hH : H - 1 + 1 = H := by have := hheight v; omega
  simpa only [hH] using h

/-- The finite local predecessor region required by the actual sweep proof. -/
noncomputable def region (S : WeakSystem (Fin n) (K + 1)) (B : Finset (Fin n))
    (rank : Fin n → ℕ) (H d : ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d)
    (v : Fin n) (hB : ball S.edge v H ⊆ B) :
    Region S (truncate S B) v H ((d + 1) ^ (H + 1)) where
  ancestors := ancestors S.edge v
  dependencies := ball S.edge v H
  root_mem := (mem_ancestors S.edge v v).mpr .refl
  ancestors_card := by
    calc
      _ ≤ (ball S.edge v (H - 1)).card := Finset.card_le_card
        (ancestors_subset_ball S.edge rank H hstrict hheight v)
      _ ≤ (d + 1) ^ (H - 1) := ball_card_le S.edge d hdegree v _
      _ ≤ (d + 1) ^ (H + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  dependencies_card := (ball_card_le S.edge d hdegree v H).trans
    (Nat.pow_le_pow_right (by omega) (Nat.le_succ H))
  predecessor_closed := by
    intro x hx y hy he
    exact (mem_ancestors S.edge v y).mpr
      (Relation.ReflTransGen.head ⟨hy, he⟩ ((mem_ancestors S.edge v x).mp hx))
  successor_covered := by
    intro x hx y _ he
    exact ancestor_neighbor_mem_ball S.edge rank H hstrict hheight v x y hx
      ((mem_closedNeighbors S.edge x y).mpr (Or.inr (Or.inl he)))
  lower_eq := fun _ _ => rfl
  upper_eq := fun _ _ => rfl
  incoming_eq := by
    intro x hx y
    have hxB : x ∈ B := hB (ancestor_neighbor_mem_ball S.edge rank H hstrict hheight v x x hx (by simp))
    by_cases he : S.edge y x = true
    · have hyB : y ∈ B := hB (ancestor_neighbor_mem_ball S.edge rank H hstrict hheight v x y hx
        ((mem_closedNeighbors S.edge x y).mpr (Or.inr (Or.inr he))))
      simp [truncate, hxB, hyB]
    · have he' : S.edge y x = false := Bool.eq_false_iff.mpr he
      simp [truncate, he']
  outgoing_eq := by
    intro x hx y
    have hxB : x ∈ B := hB (ancestor_neighbor_mem_ball S.edge rank H hstrict hheight v x x hx (by simp))
    by_cases he : S.edge x y = true
    · have hyB : y ∈ B := hB (ancestor_neighbor_mem_ball S.edge rank H hstrict hheight v x y hx
        ((mem_closedNeighbors S.edge x y).mpr (Or.inr (Or.inl he))))
      simp [truncate, hxB, hyB]
    · have he' : S.edge x y = false := Bool.eq_false_iff.mpr he
      simp [truncate, he']
  rank := rank
  rank_strict := fun x _ y _ hxy he => hstrict x y ⟨hxy, he⟩
  height := fun x _ => hheight x

/-- The exact shrinking balls for a total of `t` sweeps. Later interiors are
empty, making the schedule a total function of time. -/
def interior (E : Fin n → Fin n → Bool) (mark : Fin n) (H t j : ℕ) : Finset (Fin n) :=
  if j ≤ t then ball E mark (H * (t - j)) else ∅

theorem interior_subset (E : Fin n → Fin n → Bool) (mark : Fin n) (H t j : ℕ) :
    interior E mark H t j ⊆ ball E mark (H * t) := by
  unfold interior
  split_ifs with h
  · exact ball_mono E mark (Nat.mul_le_mul_left H (Nat.sub_le _ _))
  · exact Finset.empty_subset _

/-- A radius-`H` dependency of a vertex in the next interior belongs to the
previous interior. This is the geometric input to the moment induction. -/
theorem dependency_inside (E : Fin n → Fin n → Bool) (mark : Fin n) (H t j : ℕ)
    (v : Fin n) (hv : v ∈ interior E mark H t (j + 1)) :
    ball E v H ⊆ interior E mark H t j := by
  have hj : j + 1 ≤ t := by
    by_contra hn
    simp [interior, hn] at hv
  have hv' : v ∈ ball E mark (H * (t - (j + 1))) := by simpa [interior, hj] using hv
  have hsub : t - j = (t - (j + 1)) + 1 := by omega
  intro w hw
  have h := mem_ball_add E hv' hw
  have hj' : j ≤ t := by omega
  simpa only [interior, if_pos hj', hsub, Nat.mul_add, Nat.mul_one] using h

/-- Assemble all schedule fields from the real raw graph and its ball union.
`B` may contain the balls for any number of marks. -/
noncomputable def schedule (S : WeakSystem (Fin n) (K + 1)) (B : Finset (Fin n))
    (rank : Fin n → ℕ) (H d : ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d)
    (mark : Fin n) (t : ℕ) (hB : ball S.edge mark (H * t) ⊆ B) :
    Schedule S (truncate S B) H ((d + 1) ^ (H + 1)) where
  interior := interior S.edge mark H t
  region j v hv := region S B rank H d hstrict hheight hdegree v
    ((dependency_inside S.edge mark H t j v hv).trans
      ((interior_subset S.edge mark H t j).trans hB))
  dependencies_inside j v hv := dependency_inside S.edge mark H t j v hv

@[simp] theorem schedule_initial (S : WeakSystem (Fin n) (K + 1)) (B : Finset (Fin n))
    (rank : Fin n → ℕ) (H d : ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d)
    (mark : Fin n) (t : ℕ) (hB : ball S.edge mark (H * t) ⊆ B) :
    (schedule S B rank H d hstrict hheight hdegree mark t hB).interior 0 =
      ball S.edge mark (H * t) := by simp [schedule, interior]

@[simp] theorem mark_mem_schedule (S : WeakSystem (Fin n) (K + 1)) (B : Finset (Fin n))
    (rank : Fin n → ℕ) (H d : ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d)
    (mark : Fin n) (t : ℕ) (hB : ball S.edge mark (H * t) ⊆ B) :
    mark ∈ (schedule S B rank H d hstrict hheight hdegree mark t hB).interior t := by
  simp [schedule, interior]

/-- Every initial coordinate used by this mark lies in its original component,
so its width bound depends on that component alone. -/
theorem initial_width_bound (S : WeakSystem (Fin n) (K + 1)) (mark : Fin n)
    (H t : ℕ) (R : ℚ)
    (hwidth : ∀ v, Connected S.edge mark v → windowWidth S v ≤ R * windowWidth S mark) :
    ∀ v ∈ interior S.edge mark H t 0, windowWidth S v ≤ R * windowWidth S mark := by
  intro v hv
  have hv' : v ∈ ball S.edge mark (H * t) := by simpa [interior] using hv
  exact hwidth v (connected_of_mem_ball S.edge hv')

/-- The actual two-mark ball union. -/
def twoBalls (E : Fin n → Fin n → Bool) (x y : Fin n) (r : ℕ) : Finset (Fin n) :=
  ball E x r ∪ ball E y r

theorem twoBalls_card_le (E : Fin n → Fin n → Bool) (d : ℕ)
    (hdegree : ∀ v, (neighbors E v).card ≤ d) (x y : Fin n) (r : ℕ) :
    (twoBalls E x y r).card ≤ 2 * (d + 1) ^ r := by
  exact (Finset.card_union_le _ _).trans (by
    have hx := ball_card_le E d hdegree x r
    have hy := ball_card_le E d hdegree y r
    omega)

/-- Actual comparison locality for the computed two-ball truncation. The only
remaining probability term is the full-law near-tie count. Width ratios are
assumed separately in the two original components. -/
theorem comparison_error_twoBalls (S : WeakSystem (Fin n) (K + 1))
    (hS : 0 < S.count)
    (horder : ∀ x y, x ≠ y → S.edge x y = true → x.val < y.val)
    (rank : Fin n → ℕ) (H d : ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d)
    (s : ℕ) (hs : 0 < s) (a : ℚ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hsmall : (((d + 1) ^ (H + 1) : ℕ) : ℚ) ^ 2 * a ≤ 1 / 8)
    (hlarge : 8 * (((d + 1) ^ (H + 1) : ℕ) : ℚ) ≤ s * a ^ H)
    (t : ℕ) (x y : Fin n) (R : ℚ) (hR : 0 ≤ R)
    (hwidthX : ∀ v, Connected S.edge x v → windowWidth S v ≤ R * windowWidth S x)
    (hwidthY : ∀ v, Connected S.edge y v → windowWidth S v ≤ R * windowWidth S y)
    (ex ey : ℚ) (hex : 0 < ex) (hey : 0 < ey) :
    |LocalChoice.weakProbability S x y -
        LocalChoice.weakProbability (truncate S (twoBalls S.edge x y (H * t))) x y| ≤
      (R * windowWidth S x / ex) ^ s / 2 ^ t +
        (R * windowWidth S y / ey) ^ s / 2 ^ t +
        LocalError.nearProbability S x y (((H : ℚ) * t + ex) + ((H : ℚ) * t + ey)) := by
  let B := twoBalls S.edge x y (H * t)
  have hxB : ball S.edge x (H * t) ⊆ B := Finset.subset_union_left
  have hyB : ball S.edge y (H * t) ⊆ B := Finset.subset_union_right
  obtain ⟨f, hf⟩ := S.count_pos_iff.mp hS
  let z : State S := ⟨f, hf⟩
  exact LocalError.comparison_error_of_width_schedules S (truncate S B) hS
    (truncate_count_pos S B hS) horder H ((d + 1) ^ (H + 1)) s hs
    (pow_pos (Nat.succ_pos d) _)
    (schedule S B rank H d hstrict hheight hdegree x t hxB)
    (schedule S B rank H d hstrict hheight hdegree y t hyB)
    a ha0 ha1 hsmall hlarge (R * windowWidth S x) (R * windowWidth S y)
    (mul_nonneg hR (windowWidth_pos S z x).le)
    (mul_nonneg hR (windowWidth_pos S z y).le)
    (fun _ => rfl) (fun _ => rfl)
    (initial_width_bound S x H t R hwidthX)
    (initial_width_bound S y H t R hwidthY)
    t x y (mark_mem_schedule S B rank H d hstrict hheight hdegree x t hxB)
    (mark_mem_schedule S B rank H d hstrict hheight hdegree y t hyB) ex ey hex hey

end SortingAdversary.Optimal.BallSchedule
