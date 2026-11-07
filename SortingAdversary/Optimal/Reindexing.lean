import SortingAdversary.Optimal.IsolatedAccuracy
import SortingAdversary.Optimal.PublicOrder

/-!
# Equivariance and proof-only topological reindexing

The local algorithm keeps the original labels. Only the auxiliary coupling is
reindexed into a topological order. This file transports actual finite maps,
counts, sparse balls and propagated intervals through an explicit equivalence,
so the final guarantees apply to the unchanged original query definitions.
-/

namespace SortingAdversary.Optimal.Reindexing

open WeakMaps LocalChoice FiniteProbability GraphBalls SparseClosure CouplingHistory
open TruncatedLaw CDFCoupling IsolatedCoupling IsolatedAccuracy LocalAccuracy

variable {α β : Type*} {K : ℕ}

/-- Rename the label carrier, preserving every raw row and unary endpoint. -/
def relabel (S : WeakSystem α K) (e : α ≃ β) : WeakSystem β K where
  edge x y := S.edge (e.symm x) (e.symm y)
  lower x := S.lower (e.symm x)
  upper x := S.upper (e.symm x)

theorem system_ext {S T : WeakSystem α K}
    (he : S.edge = T.edge) (hl : S.lower = T.lower) (hu : S.upper = T.upper) : S = T := by
  cases S
  cases T
  cases he
  cases hl
  cases hu
  rfl

/-- Reindexed validity is exactly validity after composing with the renaming. -/
theorem valid_relabel (S : WeakSystem α K) (e : α ≃ β) (g : ColorMap β K) :
    (relabel S e).Valid g ↔ S.Valid (fun x => g (e x)) := by
  constructor
  · intro h
    constructor
    · intro x
      simpa [relabel] using h.1 (e x)
    · intro x y hxy
      exact h.2 (e x) (e y) (by simpa [relabel] using hxy)
  · intro h
    constructor
    · intro x
      simpa [relabel] using h.1 (e.symm x)
    · intro x y hxy
      simpa using h.2 (e.symm x) (e.symm y) hxy

/-- Explicit bijection of the actual feasible finite map families. -/
def stateEquiv (S : WeakSystem α K) (e : α ≃ β) :
    {f : ColorMap α K // S.Valid f} ≃ {g : ColorMap β K // (relabel S e).Valid g} where
  toFun f := ⟨fun x => f.val (e.symm x), by
    apply (valid_relabel S e _).mpr
    simpa using f.property⟩
  invFun g := ⟨fun x => g.val (e x), (valid_relabel S e g.val).mp g.property⟩
  left_inv f := by apply Subtype.ext; funext x; simp
  right_inv g := by apply Subtype.ext; funext x; simp

section Finite
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem count_relabel (S : WeakSystem α K) (e : α ≃ β) : (relabel S e).count = S.count := by
  have hc := Fintype.card_congr (stateEquiv S e)
  simpa [Fintype.card_subtype, WeakSystem.count, WeakSystem.maps] using hc.symm

omit [Fintype α] [Fintype β] in
/-- Label renaming commutes with the actual weak comparison branch. -/
theorem addRow_relabel (S : WeakSystem α K) (e : α ≃ β) (x y : α) :
    relabel (S.addRow x y) e = (relabel S e).addRow (e x) (e y) := by
  apply system_ext
  · funext u v
    simp [relabel, WeakSystem.addRow, Equiv.symm_apply_eq]
  · rfl
  · rfl

theorem weakProbability_relabel (S : WeakSystem α K) (e : α ≃ β) (x y : α) :
    weakProbability (relabel S e) (e x) (e y) = weakProbability S x y := by
  unfold weakProbability
  rw [← addRow_relabel, count_relabel, count_relabel]

/-- Exact event probabilities are preserved, not merely unnormalized counts. -/
theorem event_relabel (S : WeakSystem α K) (e : α ≃ β)
    (P : ColorMap α K → Prop) [DecidablePred P] :
    probability (fun g : {g : ColorMap β K // (relabel S e).Valid g} => P (fun x => g.val (e x))) =
      probability (fun f : {f : ColorMap α K // S.Valid f} => P f.val) := by
  exact mean_equiv (stateEquiv S e).symm (fun f => indicator P f.val)

theorem cdf_relabel (S : WeakSystem α (K + 1)) (e : α ≃ β) (x : α) (cut : ℕ) :
    MarginalCalibration.cdf (relabel S e) (e x) cut = MarginalCalibration.cdf S x cut := by
  rw [cdf_eq_probability, cdf_eq_probability]
  exact event_relabel S e (fun f => (f x).val < cut)

/-- The induced subcarrier equivalence is explicitly the same label renaming. -/
def subsetEquiv (e : α ≃ β) (A : Finset α) (B : Finset β)
    (h : ∀ x, e x ∈ B ↔ x ∈ A) : ↥A ≃ ↥B where
  toFun x := ⟨e x.val, (h x.val).mpr x.property⟩
  invFun y := ⟨e.symm y.val, (h (e.symm y.val)).mp (by simp)⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; simp

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- Renaming commutes with restriction to the actual selected vertex set. -/
theorem induced_relabel (S : WeakSystem α K) (e : α ≃ β) (A : Finset α) (B : Finset β)
    (h : ∀ x, e x ∈ B ↔ x ∈ A) :
    relabel (induced S A) (subsetEquiv e A B h) = induced (relabel S e) B := rfl

omit [DecidableEq α] [DecidableEq β] in
/-- Supremum propagation commutes with the label bijection. -/
theorem effectiveLower_relabel (S : WeakSystem α (K + 1)) (e : α ≃ β) (v : α) :
    (relabel S e).effectiveLower (e v) = S.effectiveLower v := by
  apply le_antisymm
  · change (Finset.univ.sup (fun u : β => if S.edge (e.symm u) (e.symm (e v)) = true then S.lower (e.symm u) else ⊥)) ≤ _
    simp only [Equiv.symm_apply_apply]
    apply Finset.sup_le
    intro u _
    split_ifs with h
    · exact S.lower_le_effectiveLower h
    · exact bot_le
  · change (Finset.univ.sup (fun u : α => if S.edge u v = true then S.lower u else ⊥)) ≤ _
    apply Finset.sup_le
    intro u _
    split_ifs with h
    · have he : (relabel S e).edge (e u) (e v) = true := by simpa [relabel] using h
      simpa [relabel] using (relabel S e).lower_le_effectiveLower he
    · exact bot_le

omit [DecidableEq α] [DecidableEq β] in
/-- Infimum propagation commutes with the same label bijection. -/
theorem effectiveUpper_relabel (S : WeakSystem α (K + 1)) (e : α ≃ β) (v : α) :
    (relabel S e).effectiveUpper (e v) = S.effectiveUpper v := by
  apply le_antisymm
  · change _ ≤ (Finset.univ.inf (fun u : α => if S.edge v u = true then S.upper u else ⊤))
    apply Finset.le_inf
    intro u _
    split_ifs with h
    · have he : (relabel S e).edge (e v) (e u) = true := by simpa [relabel] using h
      simpa [relabel] using (relabel S e).effectiveUpper_le_upper he
    · exact le_top
  · change _ ≤ (Finset.univ.inf (fun u : β => if S.edge (e.symm (e v)) (e.symm u) = true then S.upper (e.symm u) else ⊤))
    simp only [Equiv.symm_apply_apply]
    apply Finset.le_inf
    intro u _
    split_ifs with h
    · exact S.effectiveUpper_le_upper h
    · exact le_top

/-- Proper sparse neighbors correspond under exactly the same bijection. -/
theorem mem_neighbors_relabel (E : α → α → Bool) (e : α ≃ β) (x y : α) :
    e y ∈ neighbors (fun u v => E (e.symm u) (e.symm v)) (e x) ↔ y ∈ neighbors E x := by
  simp

theorem mem_closedNeighbors_relabel (E : α → α → Bool) (e : α ≃ β) (x y : α) :
    e y ∈ closedNeighbors (fun u v => E (e.symm u) (e.symm v)) (e x) ↔
      y ∈ closedNeighbors E x := by
  simp

/-- The breadth-first balls used by the executable oracle are equivariant. -/
theorem mem_ball_relabel (E : α → α → Bool) (e : α ≃ β) (x y : α) (r : ℕ) :
    e y ∈ ball (fun u v => E (e.symm u) (e.symm v)) (e x) r ↔ y ∈ ball E x r := by
  induction r generalizing x y with
  | zero => simp
  | succ r ih =>
    simp only [mem_ball_succ]
    constructor
    · rintro ⟨z, hz, hy⟩
      refine ⟨e.symm z, ?_, ?_⟩
      · apply (mem_closedNeighbors_relabel E e x (e.symm z)).mp
        simpa using hz
      · apply (ih (e.symm z) y).mp
        simpa using hy
    · rintro ⟨z, hz, hy⟩
      exact ⟨e z, (mem_closedNeighbors_relabel E e x z).mpr hz, (ih z y).mpr hy⟩

theorem connected_relabel (E : α → α → Bool) (e : α ≃ β) (x y : α) :
    Connected (fun u v => E (e.symm u) (e.symm v)) (e x) (e y) ↔ Connected E x y := by
  simp only [Connected, mem_ball_relabel]

/-- Sparse degree, rather than transitive-closure degree, is preserved. -/
theorem neighbors_card_relabel (E : α → α → Bool) (e : α ≃ β) (x : α) :
    (neighbors (fun u v => E (e.symm u) (e.symm v)) (e x)).card = (neighbors E x).card := by
  have hc := Fintype.card_congr (subsetEquiv e (neighbors E x)
    (neighbors (fun u v => E (e.symm u) (e.symm v)) (e x))
    (fun y => mem_neighbors_relabel E e x y))
  simpa only [Fintype.card_coe] using hc.symm

end Finite

/-- Raw reachability is unchanged by renaming; this also identifies the two
computed Floyd closures despite their different elimination order. -/
theorem reach_relabel (E : α → α → Bool) (e : α ≃ β) (x y : α) :
    Relation.ReflTransGen (fun u v => E (e.symm u) (e.symm v) = true) (e x) (e y) ↔
      Relation.ReflTransGen (fun u v => E u v = true) x y := by
  constructor
  · intro h
    have h' := Relation.ReflTransGen.lift e.symm
      (p := fun u v => E u v = true) (fun _ _ hstep => hstep) (e x) (e y) h
    simpa only [Function.onFun, Equiv.symm_apply_apply] using h'
  · intro h
    exact Relation.ReflTransGen.lift e
      (p := fun u v => E (e.symm u) (e.symm v) = true)
      (by intro u v hstep; simpa only [Function.onFun, Equiv.symm_apply_apply] using hstep) x y h

section Fin
variable {n : ℕ}

theorem isolated_relabel (E : Fin n → Fin n → Bool) (e : Equiv.Perm (Fin n)) (x : Fin n) :
    Isolated (fun u v => E (e.symm u) (e.symm v)) (e x) ↔ Isolated E x := by
  constructor
  · intro h y hy
    simpa using h (e y) ((Equiv.injective e).ne hy)
  · intro h y hy
    have hne : e.symm y ≠ x := by
      intro heq
      apply hy
      simpa using congrArg e heq
    simpa using h (e.symm y) hne

theorem closure_relabel (E : Rows (Fin n)) (e : Equiv.Perm (Fin n)) (x y : Fin n) :
    closure (fun u v => E (e.symm u) (e.symm v)) (e x) (e y) = closure E x y := by
  apply Bool.eq_iff_iff.mpr
  rw [NumericalGeometry.closure_iff_reach, NumericalGeometry.closure_iff_reach]
  exact reach_relabel E e x y

theorem closeSystem_relabel (S : WeakSystem (Fin n) K) (e : Equiv.Perm (Fin n)) :
    closeSystem (relabel S e) = relabel (closeSystem S) e := by
  apply system_ext
  · funext x y
    simpa only [closeSystem, lookup_tableClosure, relabel, Equiv.apply_symm_apply] using
      closure_relabel S.edge e (e.symm x) (e.symm y)
  · rfl
  · rfl

/-- The actual propagated unary intervals commute with the proof permutation. -/
theorem propagateSystem_relabel (S : WeakSystem (Fin n) (K + 1)) (e : Equiv.Perm (Fin n)) :
    propagateSystem (relabel S e) = relabel (propagateSystem S) e := by
  apply system_ext
  · rfl
  · funext x
    change (closeSystem (relabel S e)).effectiveLower x = (closeSystem S).effectiveLower (e.symm x)
    rw [closeSystem_relabel]
    simpa only [Equiv.apply_symm_apply] using effectiveLower_relabel (closeSystem S) e (e.symm x)
  · funext x
    change (closeSystem (relabel S e)).effectiveUpper x = (closeSystem S).effectiveUpper (e.symm x)
    rw [closeSystem_relabel]
    simpa only [Equiv.apply_symm_apply] using effectiveUpper_relabel (closeSystem S) e (e.symm x)

theorem windowWidth_relabel (S : WeakSystem (Fin n) (K + 1)) (e : Equiv.Perm (Fin n)) (x : Fin n) :
    windowWidth (relabel S e) (e x) = windowWidth S x := by
  simp [windowWidth, relabel]

theorem propagatedWidth_relabel (S : WeakSystem (Fin n) (K + 1)) (e : Equiv.Perm (Fin n))
    (x : Fin n) :
    windowWidth (propagateSystem (relabel S e)) (e x) = windowWidth (propagateSystem S) x := by
  rw [propagateSystem_relabel, windowWidth_relabel]

theorem queryBall_mem_relabel (S : WeakSystem (Fin n) (K + 1)) (e : Equiv.Perm (Fin n))
    (H d : ℕ) (R ε : ℚ) (x y v : Fin n) :
    e v ∈ LocalAccuracy.queryBall (relabel S e) H d R ε (e x) (e y) ↔
      v ∈ LocalAccuracy.queryBall S H d R ε x y := by
  simp only [LocalAccuracy.queryBall, BallSchedule.twoBalls, Finset.mem_union, relabel,
    mem_ball_relabel]

theorem cdfBall_mem_relabel (S : WeakSystem (Fin n) (K + 1)) (e : Equiv.Perm (Fin n))
    (H d : ℕ) (R ε : ℚ) (x v : Fin n) :
    e v ∈ CDFAccuracy.queryBall (relabel S e) H d R ε (e x) ↔
      v ∈ CDFAccuracy.queryBall S H d R ε x :=
  mem_ball_relabel S.edge e x v _

/-- The induced local comparison itself is identical, before any accuracy
theorem is invoked. The production query never renames its labels. -/
theorem localWeakProbability_relabel (S : WeakSystem (Fin n) (K + 1))
    (e : Equiv.Perm (Fin n)) (H d : ℕ) (R ε : ℚ) (x y : Fin n) :
    localWeakProbability (relabel S e) H d R ε (e x) (e y) =
      localWeakProbability S H d R ε x y := by
  let A := LocalAccuracy.queryBall S H d R ε x y
  let B := LocalAccuracy.queryBall (relabel S e) H d R ε (e x) (e y)
  let q := subsetEquiv e A B (queryBall_mem_relabel S e H d R ε x y)
  have hsys : induced (propagateSystem (relabel S e)) B =
      relabel (induced (propagateSystem S) A) q := by
    rw [propagateSystem_relabel]
    exact (induced_relabel (propagateSystem S) e A B
      (queryBall_mem_relabel S e H d R ε x y)).symm
  change weakProbability (induced (propagateSystem (relabel S e)) B) _ _ = _
  rw [hsys]
  exact weakProbability_relabel (induced (propagateSystem S) A) q
    ⟨x, left_mem_queryBall S H d R ε x y⟩ ⟨y, right_mem_queryBall S H d R ε x y⟩

/-- The exact same statement holds for every local cumulative query. -/
theorem localCDF_relabel (S : WeakSystem (Fin n) (K + 1))
    (e : Equiv.Perm (Fin n)) (H d : ℕ) (R ε : ℚ) (x : Fin n) (cut : ℕ) :
    CDFAccuracy.localCDF (relabel S e) H d R ε (e x) cut =
      CDFAccuracy.localCDF S H d R ε x cut := by
  let A := CDFAccuracy.queryBall S H d R ε x
  let B := CDFAccuracy.queryBall (relabel S e) H d R ε (e x)
  let q := subsetEquiv e A B (cdfBall_mem_relabel S e H d R ε x)
  have hsys : induced (propagateSystem (relabel S e)) B =
      relabel (induced (propagateSystem S) A) q := by
    rw [propagateSystem_relabel]
    exact (induced_relabel (propagateSystem S) e A B
      (cdfBall_mem_relabel S e H d R ε x)).symm
  change MarginalCalibration.cdf (induced (propagateSystem (relabel S e)) B) _ cut = _
  rw [hsys]
  exact cdf_relabel (induced (propagateSystem S) A) q
    ⟨x, CDFAccuracy.mark_mem_queryBall S H d R ε x⟩ cut

/-- Every width or isolation premise is transported from the actual graph. -/
theorem markCondition_relabel (S : WeakSystem (Fin n) (K + 1))
    (e : Equiv.Perm (Fin n)) (H d : ℕ) (R ε : ℚ) (x : Fin n)
    (hx : MarkCondition S H d R ε x) : MarkCondition (relabel S e) H d R ε (e x) := by
  rcases hx with hx | ⟨hratio, hmin⟩
  · exact Or.inl ((isolated_relabel S.edge e x).mpr hx)
  · refine Or.inr ⟨?_, ?_⟩
    · intro v hv
      have hc : Connected S.edge x (e.symm v) := by
        apply (connected_relabel S.edge e x (e.symm v)).mp
        simpa only [relabel, Equiv.apply_symm_apply] using hv
      have hw := hratio (e.symm v) hc
      have hvw : windowWidth (propagateSystem (relabel S e)) v =
          windowWidth (propagateSystem S) (e.symm v) := by
        simpa only [Equiv.apply_symm_apply] using propagatedWidth_relabel S e (e.symm v)
      rw [hvw, propagatedWidth_relabel]
      exact hw
    · simpa only [propagatedWidth_relabel] using hmin

/-- This permutation is used only by the semantic proof of the coupling.
The executable estimates above remain on the original label carrier. -/
noncomputable def topological (S : WeakSystem (Fin n) K) : Equiv.Perm (Fin n) :=
  PublicOrder.rankingExtension (closure S.edge)

theorem topological_strict (S : WeakSystem (Fin n) K) (rank : Fin n → ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y)
    (x y : Fin n) (hxy : Arc S.edge x y) : topological S x < topological S y := by
  have ho : PublicOrder.IsOrder (closure S.edge) :=
    ⟨closure_refl S.edge, closure_trans S.edge,
      NumericalGeometry.closure_antisymm S.edge rank hstrict⟩
  exact PublicOrder.extensionRank_strict ho (closure_old S.edge hxy.2) hxy.1

theorem topological_order (S : WeakSystem (Fin n) K) (rank : Fin n → ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y) :
    ∀ x y, x ≠ y → (relabel S (topological S)).edge x y = true → x.val < y.val := by
  intro x y hne hrow
  have hne' := (topological S).symm.injective.ne hne
  have hs := topological_strict S rank hstrict ((topological S).symm x)
    ((topological S).symm y) ⟨hne', hrow⟩
  simpa only [Equiv.apply_symm_apply, Fin.lt_def] using hs

theorem rank_relabel (S : WeakSystem (Fin n) K) (e : Equiv.Perm (Fin n))
    (rank : Fin n → ℕ) (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y) :
    ∀ x y, Arc (relabel S e).edge x y → rank (e.symm x) < rank (e.symm y) := by
  intro x y hxy
  exact hstrict _ _ ⟨e.symm.injective.ne hxy.1, hxy.2⟩

theorem degree_relabel (S : WeakSystem (Fin n) K) (e : Equiv.Perm (Fin n)) (d : ℕ)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d) :
    ∀ v, (neighbors (relabel S e).edge v).card ≤ d := by
  intro v
  have hc := neighbors_card_relabel S.edge e (e.symm v)
  simpa only [relabel, Equiv.apply_symm_apply] using hc.trans_le (hdegree (e.symm v))

/-- Final comparison accuracy on arbitrary original labels. All premises are
actual sparse-graph and interval invariants; no label-index order is assumed. -/
theorem comparison_accuracy (S : WeakSystem (Fin n) (K + 1)) (hS : 0 < S.count)
    (rank : Fin n → ℕ) (H d : ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d)
    (R ε : ℚ) (hR : 0 ≤ R) (hε : 0 < ε) (x y : Fin n) (hxy : y ≠ x)
    (hx : MarkCondition S H d R ε x) (hy : MarkCondition S H d R ε y) :
    |localWeakProbability S H d R ε x y - weakProbability S x y| ≤ ε := by
  let e := topological S
  have hT : 0 < (relabel S e).count := by rw [count_relabel]; exact hS
  have h := IsolatedAccuracy.comparison_accuracy_with_isolated (relabel S e) hT
    (topological_order S rank hstrict) (fun v => rank (e.symm v)) H d
    (rank_relabel S e rank hstrict) (fun v => hheight (e.symm v))
    (degree_relabel S e d hdegree) R ε hR hε (e x) (e y) (e.injective.ne hxy)
    (markCondition_relabel S e H d R ε x hx) (markCondition_relabel S e H d R ε y hy)
  simpa only [localWeakProbability_relabel, weakProbability_relabel] using h

/-- Final CDF accuracy on the original executable query, including isolated
coordinates of any width and every natural threshold. -/
theorem cdf_accuracy (S : WeakSystem (Fin n) (K + 1)) (hS : 0 < S.count)
    (rank : Fin n → ℕ) (H d : ℕ)
    (hstrict : ∀ x y, Arc S.edge x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ v, (neighbors S.edge v).card ≤ d)
    (R ε : ℚ) (hR : 0 ≤ R) (hε : 0 < ε) (x : Fin n)
    (hx : MarkCondition S H d R ε x) (cut : ℕ) :
    |CDFAccuracy.localCDF S H d R ε x cut - MarginalCalibration.cdf S x cut| ≤ ε := by
  let e := topological S
  have hT : 0 < (relabel S e).count := by rw [count_relabel]; exact hS
  have h := IsolatedAccuracy.cdf_accuracy_with_isolated (relabel S e) hT
    (topological_order S rank hstrict) (fun v => rank (e.symm v)) H d
    (rank_relabel S e rank hstrict) (fun v => hheight (e.symm v))
    (degree_relabel S e d hdegree) R ε hR hε (e x)
    (markCondition_relabel S e H d R ε x hx) cut
  simpa only [localCDF_relabel, cdf_relabel] using h

end Fin

end SortingAdversary.Optimal.Reindexing
