import SortingAdversary.Continuous.LocalEnclosure
import SortingAdversary.Optimal.GraphBalls

/-!
# Finite dependence of topological affine sweeps

The full calculation and the calculation with a frozen exterior agree at a
query after `t` sweeps whenever every vertex in the radius-`H*t` ball is
updated. The proof follows actual update dependencies: predecessors have new
values and successors have old values. The graph-ball facts reused from the
older development are purely finite graph lemmas.
-/

namespace SortingAdversary.Continuous.FiniteAveraging

open SortingAdversary.Optimal.GraphBalls

section MaskedSweep

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {n S : ℕ}

theorem maskedStep_other (D : System (Fin n) K) (F : Finset (Fin n))
    (digits : Fin n → Fin S) (v w : Fin n) (Y : Fin n → K) (hw : w ≠ v) :
    maskedStep D S F (v, digits v) Y w = Y w := by
  unfold maskedStep
  split_ifs
  · exact update_other D S (digits v) v w Y hw
  · rfl

def orderedMaskedAfter (D : System (Fin n) K) (F : Finset (Fin n))
    (digits : Fin n → Fin S) (Y : Fin n → K) : ℕ → Fin n → K
  | 0 => Y
  | t + 1 => if h : t < n then maskedStep D S F (⟨t, h⟩, digits ⟨t, h⟩)
      (orderedMaskedAfter D F digits Y t) else orderedMaskedAfter D F digits Y t

def orderedMaskedSweep (D : System (Fin n) K) (F : Finset (Fin n))
    (digits : Fin n → Fin S) (Y : Fin n → K) : Fin n → K :=
  orderedMaskedAfter D F digits Y n

theorem orderedMaskedAfter_succ_other (D : System (Fin n) K) (F : Finset (Fin n))
    (digits : Fin n → Fin S) (Y : Fin n → K) (t : ℕ) (x : Fin n) (hx : x.val ≠ t) :
    orderedMaskedAfter D F digits Y (t + 1) x = orderedMaskedAfter D F digits Y t x := by
  conv_lhs => rw [orderedMaskedAfter]
  split_ifs with ht
  · exact maskedStep_other D F digits ⟨t, ht⟩ x _ (fun h => hx (congrArg Fin.val h))
  · rfl

theorem orderedMaskedAfter_old (D : System (Fin n) K) (F : Finset (Fin n))
    (digits : Fin n → Fin S) (Y : Fin n → K) (t : ℕ) (x : Fin n) (hx : t ≤ x.val) :
    orderedMaskedAfter D F digits Y t x = Y x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [orderedMaskedAfter_succ_other D F digits Y t x (by omega)]
    exact ih (by omega)

theorem orderedMaskedAfter_stable (D : System (Fin n) K) (F : Finset (Fin n))
    (digits : Fin n → Fin S) (Y : Fin n → K) (t u : ℕ) (x : Fin n)
    (hx : x.val < t) (htu : t ≤ u) :
    orderedMaskedAfter D F digits Y u x = orderedMaskedAfter D F digits Y t x := by
  induction u, htu using Nat.le_induction with
  | base => rfl
  | succ u htu ih =>
    rw [orderedMaskedAfter_succ_other D F digits Y u x (by omega), ih]

theorem orderedMaskedSweep_apply (D : System (Fin n) K) (F : Finset (Fin n))
    (digits : Fin n → Fin S) (Y : Fin n → K) (v : Fin n) (hv : v ∈ F) :
    orderedMaskedSweep D F digits Y v =
      update D S (digits v) v (orderedMaskedAfter D F digits Y v.val) v := by
  unfold orderedMaskedSweep
  rw [orderedMaskedAfter_stable D F digits Y (v.val + 1) n v (by omega) (by omega)]
  simp only [orderedMaskedAfter, dif_pos v.isLt, maskedStep, if_pos hv]

def prefixSteps (digits : Fin n → Fin S) (t : ℕ) (ht : t ≤ n) : List (Fin n × Fin S) :=
  List.ofFn fun i : Fin t =>
    let v : Fin n := ⟨i.val, lt_of_lt_of_le i.isLt ht⟩
    (v, digits v)

theorem orderedMaskedAfter_eq_steps (D : System (Fin n) K) (F : Finset (Fin n))
    (digits : Fin n → Fin S) (Y : Fin n → K) (t : ℕ) (ht : t ≤ n) :
    orderedMaskedAfter D F digits Y t = maskedSteps D S F (prefixSteps digits t ht) Y := by
  induction t with
  | zero => simp [orderedMaskedAfter, prefixSteps, maskedSteps]
  | succ t ih =>
    have ht' : t < n := lt_of_lt_of_le (Nat.lt_succ_self t) ht
    have htle : t ≤ n := ht'.le
    have hpre : prefixSteps digits (t + 1) ht =
        (prefixSteps digits t htle) ++ [(⟨t, ht'⟩, digits ⟨t, ht'⟩)] := by
      unfold prefixSteps
      rw [List.ofFn_succ_last]
      rfl
    rw [orderedMaskedAfter, dif_pos ht', hpre]
    simp only [maskedSteps, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih htle]
    rfl

theorem maskedSteps_eq_filter (D : System (Fin n) K) (F : Finset (Fin n))
    (steps : List (Fin n × Fin S)) (Y : Fin n → K) :
    maskedSteps D S F steps Y = fullSteps D S (steps.filter fun step => step.1 ∈ F) Y := by
  induction steps generalizing Y with
  | nil => rfl
  | cons step steps ih =>
    by_cases hv : step.1 ∈ F
    · simpa [maskedSteps, maskedStep, fullSteps, hv] using
        ih (update D S step.2 step.1 Y)
    · simpa [maskedSteps, maskedStep, fullSteps, hv] using ih Y

/-- The masked topological sweep is the executable fold over the retained
interior list. This connects the finite-dependence proof to `Enclose`. -/
theorem orderedMaskedSweep_eq_sweep (D : System (Fin n) K) (F : Finset (Fin n))
    (digits : Fin n → Fin S) (Y : Fin n → K) :
    orderedMaskedSweep D F digits Y =
      sweep D S digits ((List.finRange n).filter fun x => x ∈ F) Y := by
  rw [orderedMaskedSweep, orderedMaskedAfter_eq_steps D F digits Y n le_rfl,
    maskedSteps_eq_filter]
  have hprefix : prefixSteps digits n le_rfl =
      (List.finRange n).map (fun v => (v, digits v)) := by
    simp only [prefixSteps, List.finRange, List.map_ofFn]
    rfl
  rw [hprefix, List.filter_map]
  simp [fullSteps, sweep, List.foldl_map, Function.comp_def]

/-- Agreement on the ancestor digits and old dependencies suffices for exact
agreement of one full and one frozen-exterior sweep. -/
theorem orderedSweep_eq_masked_region (D : System (Fin n) K)
    (horder : ∀ x y, D.edge x y = true → x.val < y.val)
    (F : Finset (Fin n)) (digits localDigits : Fin n → Fin S)
    (A B : Fin n → K) (v : Fin n) (H : ℕ) (region : SweepRegion D v H)
    (hF : region.ancestors ⊆ F)
    (hdigits : ∀ x ∈ region.ancestors, digits x = localDigits x)
    (hdep : ∀ x ∈ region.dependencies, A x = B x) :
    orderedSweep D digits A v = orderedMaskedSweep D F localDigits B v := by
  have hall : ∀ w ∈ region.ancestors,
      orderedSweep D digits A w = orderedMaskedSweep D F localDigits B w := by
    intro w hw
    induction hn : w.val using Nat.strong_induction_on generalizing w with
    | h q ih =>
      rw [orderedSweep_apply, orderedMaskedSweep_apply D F localDigits B w (hF hw)]
      simp only [update_self]
      rw [hdigits w hw]
      congr 1
      · rw [orderedAfter_old D digits A w.val w le_rfl,
          orderedMaskedAfter_old D F localDigits B w.val w le_rfl]
        exact hdep w (region.self_covered w hw)
      · unfold conditionalLower
        apply Finset.fold_congr
        intro x hx
        have hedge : D.edge x w = true := by simpa using hx
        have hidx := horder x w hedge
        have hanc := region.predecessor_closed w hw x hedge
        have hknown := ih x.val (by omega) x hanc rfl
        have hfull := orderedAfter_stable D digits A w.val n x hidx w.isLt.le
        have hlocal := orderedMaskedAfter_stable D F localDigits B w.val n x hidx w.isLt.le
        simpa only [orderedSweep, orderedMaskedSweep, hfull, hlocal] using hknown
      · unfold conditionalUpper
        apply Finset.fold_congr
        intro x hx
        have hedge : D.edge w x = true := by simpa using hx
        have hidx := horder w x hedge
        rw [orderedAfter_old D digits A w.val x hidx.le,
          orderedMaskedAfter_old D F localDigits B w.val x hidx.le]
        exact hdep x (region.successor_covered w hw x hedge)
  exact hall v region.root_mem

end MaskedSweep

section GraphRegions

variable {K : Type*} {n : ℕ}

noncomputable def directedAncestors (E : Fin n → Fin n → Bool) (v : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun x => Relation.ReflTransGen (Arc E) x v

@[simp] theorem mem_directedAncestors (E : Fin n → Fin n → Bool) (v x : Fin n) :
    x ∈ directedAncestors E v ↔ Relation.ReflTransGen (Arc E) x v := by
  classical
  simp [directedAncestors]

theorem directedAncestors_subset_ball (E : Fin n → Fin n → Bool)
    (rank : Fin n → ℕ) (H : ℕ)
    (hrank : ∀ x y, E x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H) (v : Fin n) :
    directedAncestors E v ⊆ ball E v (H - 1) := by
  intro x hx
  exact ancestor_mem_ball E rank H (fun x y h => hrank x y h.2) hheight
    ((mem_directedAncestors E v x).mp hx)

theorem ancestor_successor_mem_ball (E : Fin n → Fin n → Bool)
    (rank : Fin n → ℕ) (H : ℕ)
    (hrank : ∀ x y, E x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H) (v x y : Fin n)
    (hx : x ∈ directedAncestors E v) (hy : y ∈ closedNeighbors E x) :
    y ∈ ball E v H := by
  have hxball := directedAncestors_subset_ball E rank H hrank hheight v hx
  have hyball := (mem_ball_one E x y).mpr hy
  have h := mem_ball_add E hxball hyball
  have hH : H - 1 + 1 = H := by have := hheight v; omega
  simpa only [hH] using h

/-- The region in the sweep theorem is constructed from the graph. Its old
dependencies are exactly the graph ball of radius `H`. -/
noncomputable def graphRegion (D : System (Fin n) K) (v : Fin n)
    (rank : Fin n → ℕ) (H : ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H) : SweepRegion D v H where
  ancestors := directedAncestors D.edge v
  dependencies := ball D.edge v H
  root_mem := (mem_directedAncestors D.edge v v).mpr .refl
  self_covered := by
    intro x hx
    exact ancestor_successor_mem_ball D.edge rank H hrank hheight v x x hx (by simp)
  predecessor_closed := by
    intro x hx y hy
    apply (mem_directedAncestors D.edge v y).mpr
    apply Relation.ReflTransGen.head ⟨?_, hy⟩ ((mem_directedAncestors D.edge v x).mp hx)
    intro heq
    subst y
    exact Nat.lt_irrefl _ (hrank x x hy)
  successor_covered := by
    intro x hx y hy
    exact ancestor_successor_mem_ball D.edge rank H hrank hheight v x y hx
      ((mem_closedNeighbors D.edge x y).mpr (Or.inr (Or.inl hy)))
  rank := rank
  rank_strict := fun x _ y _ h => hrank x y h
  height := fun x _ => hheight x

theorem graphRegion_ancestors_card (D : System (Fin n) K) (v : Fin n)
    (rank : Fin n → ℕ) (H d : ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (neighbors D.edge x).card ≤ d) :
    (graphRegion D v rank H hrank hheight).ancestors.card ≤ (d + 1) ^ (H + 1) := by
  calc
    _ ≤ (ball D.edge v (H - 1)).card := Finset.card_le_card
      (directedAncestors_subset_ball D.edge rank H hrank hheight v)
    _ ≤ (d + 1) ^ (H - 1) := ball_card_le D.edge d hdegree v _
    _ ≤ (d + 1) ^ (H + 1) := Nat.pow_le_pow_right (by omega) (by omega)

theorem graphRegion_dependencies_card (D : System (Fin n) K) (v : Fin n)
    (rank : Fin n → ℕ) (H d : ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (neighbors D.edge x).card ≤ d) :
    (graphRegion D v rank H hrank hheight).dependencies.card ≤ (d + 1) ^ (H + 1) :=
  (ball_card_le D.edge d hdegree v H).trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ H))

end GraphRegions

section Locality

variable {n S : ℕ}

theorem orderedSweep_eq_masked_ball (D : System (Fin n) ℚ)
    (horder : ∀ x y, D.edge x y = true → x.val < y.val)
    (rank : Fin n → ℕ) (H : ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (F : Finset (Fin n)) (digits localDigits : Fin n → Fin S)
    (A B : Fin n → ℚ) (v : Fin n) (hF : ball D.edge v H ⊆ F)
    (hdigits : ∀ x ∈ ball D.edge v H, digits x = localDigits x)
    (hdep : ∀ x ∈ ball D.edge v H, A x = B x) :
    orderedSweep D digits A v = orderedMaskedSweep D F localDigits B v := by
  let region := graphRegion D v rank H hrank hheight
  apply orderedSweep_eq_masked_region D horder F digits localDigits A B v H region
  · intro x hx
    exact hF (region.self_covered x hx)
  · intro x hx
    exact hdigits x (region.self_covered x hx)
  · exact hdep

variable [NeZero S]

def iterateMaskedSweep (D : System (Fin n) ℚ) (F : Finset (Fin n)) (initial : Fin n → ℚ) :
    (t : ℕ) → SweepHistory n S t → Fin n → ℚ
  | 0 => fun _ => initial
  | t + 1 => fun history => orderedMaskedSweep D F history.2
      (iterateMaskedSweep D F initial t history.1)

/-- Exact finite dependence: freezing everything outside the radius-`H*t`
interior cannot change a queried endpoint after `t` topological sweeps. -/
theorem iterateSweep_eq_masked (D : System (Fin n) ℚ)
    (horder : ∀ x y, D.edge x y = true → x.val < y.val)
    (rank : Fin n → ℕ) (H : ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (F : Finset (Fin n)) (initial : Fin n → ℚ) (t : ℕ) :
    ∀ (history : SweepHistory n S t) (v : Fin n), ball D.edge v (H * t) ⊆ F →
      iterateSweep D initial t history v = iterateMaskedSweep D F initial t history v := by
  induction t with
  | zero => intros; rfl
  | succ t ih =>
    intro history v hF
    apply orderedSweep_eq_masked_ball D horder rank H hrank hheight F history.2 history.2 _ _ v
    · have hle : H ≤ H * (t + 1) := by
        calc
          H = H * 1 := by simp
          _ ≤ H * (t + 1) := Nat.mul_le_mul_left H (Nat.succ_le_succ (Nat.zero_le t))
      exact (ball_mono D.edge v hle).trans hF
    · intros; rfl
    · intro x hx
      apply ih history.1 x
      intro y hy
      have hh := mem_ball_add D.edge hx hy
      apply hF
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm] using hh

end Locality

end SortingAdversary.Continuous.FiniteAveraging
