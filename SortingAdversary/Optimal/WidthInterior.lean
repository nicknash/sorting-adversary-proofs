import SortingAdversary.Optimal.WidthScaleSelect

/-!
# Fixed-palette physical pins and reserved-window preservation

Scale hubs are strictly interior. This file exposes the corresponding branch
of the actual promotion routine with a definitionally unchanged palette, and
transfers numerical incomparability through the exact source-partition law.
-/

namespace SortingAdversary.Optimal.WidthRepair

open WeakMaps WeakMaps.WeakSystem FiniteInsertion NumericalRepresentation SparseClosure
open GraphBalls PoolState FiniteRefinement PinTransitions ControllerRouting SeparatedPins
open RefinementTransitions

variable {n : ℕ}

namespace State

def interiorResult (s : State n) (v : Fin n) (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v < c ∧ c < s.pool.system.effectiveUpper v) :
    Promotion.Result s.pool.system s.pool.pins v c where
  palette := s.pool.palette
  system := pinAt s.pool.system v c
  newPins := recordPin s.pool.pins v c
  embed := id
  destination := c
  embed_strict := fun _ _ h => h
  palette_bounds := ⟨le_rfl, Nat.le_succ _⟩
  invariant := interior_pin_invariant s.pool.invariant v c hc.1 hc.2
  pin_bounds := pin_bounds_preserved s.pool.invariant s.pool.pin_bounds v c hc.1.le hc.2.le
  edges := rfl
  pins_eq := by
    have heq : mapPins id s.pool.pins = s.pool.pins := by
      funext x
      unfold mapPins
      cases s.pool.pins x <;> rfl
    rw [heq]
  retains_fiber := by simp only [count, maps_pinAt]; exact le_rfl
  independent := by
    intro x d hd hdc
    change d = c at hdc
    subst d
    exact interior_birth_independent s.pool.invariant hd hc.1 hc.2

theorem interiorResult_actual (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v < c ∧ c < s.pool.system.effectiveUpper v) :
    s.interiorResult v c hc = Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds
      v hv c ⟨hc.1.le, hc.2.le⟩ := by
  unfold Promotion.promote
  rw [dif_neg (ne_of_lt hc.1), dif_neg (ne_of_gt hc.2)]
  rfl

def interiorUpdate (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v < c ∧ c < s.pool.system.effectiveUpper v)
    (hm : HasMate s.pool v) (charge : ℚ)
    (hcharge : (s.pool.system.count : ℚ) ≤ charge * (pinAt s.pool.system v c).count) : PinUpdate s where
  vertex := v
  free := hv
  colour := c
  supported := ⟨hc.1.le, hc.2.le⟩
  mate := hm
  result := s.interiorResult v c hc
  actual := s.interiorResult_actual v hv c hc
  data := ⟨s.rows.pin v c, rfl, SourcePartition.pin_active _ _ _, s.order, fun _ => rfl⟩
  charge := charge
  retained := hcharge

/-- The semantic equality of the numerical and primitive laws remains exact
after conditioning one coordinate. -/
theorem numerical_pin_valid (s : State n) (v : Fin n) (c : Fin (s.pool.palette + 1))
    (f : ColorMap (Fin n) (s.pool.palette + 1)) :
    (pinAt s.numerical.system v c).Valid f ↔ (pinAt s.pool.system v c).Valid f := by
  simp only [valid_pinAt, s.numerical_valid]

theorem numerical_windows (s : State n) (v : Fin n) :
    s.numerical.system.effectiveLower v = s.pool.system.effectiveLower v ∧
      s.numerical.system.effectiveUpper v = s.pool.system.effectiveUpper v :=
  s.rows.view_windows s.pool.pin_bounds s.pool.invariant.feasible v

/-- A public comparison retired from the numerical graph cannot create a
spurious influence on a reserved window: the equality follows from the
actual finite-law equivalence before and after the physical pin. -/
theorem pin_windows_unchanged (s : State n) (x y : Fin n) (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower x ≤ c ∧ c ≤ s.pool.system.effectiveUpper x)
    (hxy : s.numerical.system.edge x y = false) (hyx : s.numerical.system.edge y x = false) :
    (pinAt s.pool.system x c).effectiveLower y = s.pool.system.effectiveLower y ∧
      (pinAt s.pool.system x c).effectiveUpper y = s.pool.system.effectiveUpper y := by
  have hfeas : ∃ f, (pinAt s.pool.system x c).Valid f := by
    obtain ⟨f, hf, hfx⟩ := (s.pool.system.support_iff_window s.pool.invariant.closed
      s.pool.invariant.feasible x c).mpr hc
    exact ⟨f, (valid_pinAt _ _ _ _).mpr ⟨hf, hfx⟩⟩
  have heq := PinElimination.windows_eq_of_valid_iff (pinAt s.pool.system x c)
    (pinAt s.numerical.system x c)
    ⟨s.pool.invariant.closed.refl, s.pool.invariant.closed.trans⟩
    ⟨s.numerical.closed.refl, s.numerical.closed.trans⟩ hfeas (s.numerical_pin_valid x c) y
  have hlow : (pinAt s.numerical.system x c).effectiveLower y = s.numerical.system.effectiveLower y := by
    rw [pinAt_lower, hxy]
    rfl
  have hupp : (pinAt s.numerical.system x c).effectiveUpper y = s.numerical.system.effectiveUpper y := by
    rw [pinAt_upper, hyx]
    rfl
  exact ⟨heq.1.symm.trans (hlow.trans (s.numerical_windows y).1),
    heq.2.symm.trans (hupp.trans (s.numerical_windows y).2)⟩

end State

/-- Row deletion transfers every numerical comparison backwards, even if a
palette split changed its finite colour carrier. -/
theorem numerical_edge_mono {s t : State n}
    (hsub : ∀ x y, t.rows.active x y = true → s.rows.active x y = true)
    {u v : Fin n} (h : t.numerical.system.edge u v = true) :
    s.numerical.system.edge u v = true := by
  have hh : closure t.rows.active u v = true := by
    simpa only [State.numerical, closeSystem, SourcePartition.view, lookup_tableClosure] using h
  have hout := closure_subset_closed t.rows.active (closure s.rows.active)
    (closure_refl _) (closure_trans _) (fun x y hxy => closure_old _ (hsub x y hxy)) u v hh
  simpa only [State.numerical, closeSystem, SourcePartition.view, lookup_tableClosure] using hout

theorem numerical_incomparable_of_subset {s t : State n}
    (hsub : ∀ x y, t.rows.active x y = true → s.rows.active x y = true)
    {u v : Fin n} (huv : s.numerical.system.edge u v = false) :
    t.numerical.system.edge u v = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have ho := numerical_edge_mono hsub h
  rw [huv] at ho
  contradiction

theorem hasMate_of_same_public {s t : State n}
    (hmembers : t.pool.members = s.pool.members) (hedge : t.pool.system.edge = s.pool.system.edge)
    {v : Fin n} (h : HasMate s.pool v) : HasMate t.pool v := by
  obtain ⟨w, hw, hne, he⟩ := h
  refine ⟨w, hmembers.symm ▸ hw, hne, ?_⟩
  change t.pool.system.edge v w = true ∨ t.pool.system.edge w v = true
  rw [hedge]
  exact he

end SortingAdversary.Optimal.WidthRepair
