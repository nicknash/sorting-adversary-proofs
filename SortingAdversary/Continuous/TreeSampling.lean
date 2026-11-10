import SortingAdversary.Continuous.Sampling
import SortingAdversary.Continuous.TreeState

/-!
# The actual sampling experiment on a finite tree

One draw first chooses a node and then an independent uniform coordinate in
`(0,1)`. Its order is the lexicographic order of the node's anchor path followed
by that coordinate. The probability that all labels choose their assigned
nodes and their coordinates satisfy the global system is computed from the
product measure, rather than postulated as a packing premise.
-/

namespace SortingAdversary.Continuous.TreeSampling

open MeasureTheory Set FiniteAveraging OrderRegion
open scoped BigOperators

private theorem cons_lt_cons_iff {a b : ℝ} {p q : List ℝ} :
    a :: p < b :: q ↔ a < b ∨ a = b ∧ p < q := by
  constructor
  · intro h
    cases h with
    | rel h => exact Or.inl h
    | cons h => exact Or.inr ⟨rfl, h⟩
  · rintro (h | ⟨rfl, h⟩)
    · exact List.Lex.rel h
    · exact List.Lex.cons h

/-- For fixed finite paths, comparing two positions is a measurable predicate
of their two final real coordinates. -/
theorem measurable_fixed_path_comparison (p q : List ℝ) :
    MeasurableSet {z : ℝ × ℝ | p ++ [z.1] < q ++ [z.2]} := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil =>
      convert (show MeasurableSet {z : ℝ × ℝ | z.1 < z.2} from
        measurableSet_lt measurable_fst measurable_snd) using 1
      ext z
      exact List.lex_singleton_iff _ _
    | cons b q =>
      convert measurableSet_le measurable_fst (measurable_const (a := b)) using 1
      ext z
      change [z.1] < b :: (q ++ [z.2]) ↔ z.1 ≤ b
      rw [cons_lt_cons_iff]
      have hn : ([] : List ℝ) < q ++ [z.2] := by cases q <;> exact List.Lex.nil
      simp only [hn, and_true, le_iff_lt_or_eq]
  | cons a p ih =>
    cases q with
    | nil =>
      convert measurableSet_lt (measurable_const (a := a)) measurable_snd using 1
      ext z
      change a :: (p ++ [z.1]) < [z.2] ↔ a < z.2
      rw [cons_lt_cons_iff]
      have hn : ¬ p ++ [z.1] < ([] : List ℝ) := List.not_lex_nil
      simp only [hn, and_false, or_false]
    | cons b q =>
      convert (MeasurableSet.const (a < b)).union
        ((MeasurableSet.const (a = b)).inter (ih q)) using 1
      ext z
      exact cons_lt_cons_iff

variable {N : Type*} [Fintype N] [MeasurableSpace N] [MeasurableSingletonClass N]

/-- A node and its coordinate, equipped below with the tree's actual order. -/
def Position (path : N ↪ List ℝ) := N × ℝ

instance (path : N ↪ List ℝ) : MeasurableSpace (Position path) :=
  inferInstanceAs (MeasurableSpace (N × ℝ))

instance (path : N ↪ List ℝ) : MeasurableEq (Position path) :=
  inferInstanceAs (MeasurableEq (N × ℝ))

def Position.list (path : N ↪ List ℝ) (z : Position path) : List ℝ :=
  path z.1 ++ [z.2]

theorem Position.list_injective (path : N ↪ List ℝ) : Function.Injective (Position.list path) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  have h' : (path a).concat x = (path b).concat y := by
    simpa only [List.concat_eq_append, Position.list] using h
  obtain ⟨hp, hxy⟩ := List.concat_inj.mp h'
  exact Prod.ext (path.injective hp) hxy

noncomputable instance (path : N ↪ List ℝ) : LinearOrder (Position path) :=
  LinearOrder.lift' (Position.list path) (Position.list_injective path)

instance (path : N ↪ List ℝ) : MeasurableStrictOrder (Position path) where
  measurable_lt := by
    let S (a b : N) : Set (Position path × Position path) :=
      {z | z.1.1 = a ∧ z.2.1 = b ∧ path a ++ [z.1.2] < path b ++ [z.2.2]}
    have hS : ∀ a b, MeasurableSet (S a b) := by
      intro a b
      exact (measurableSet_eq_fun (measurable_fst.comp measurable_fst) measurable_const).inter
        ((measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const).inter
          ((measurable_fixed_path_comparison (path a) (path b)).preimage
            ((measurable_snd.comp measurable_fst).prodMk
              (measurable_snd.comp measurable_snd))))
    have heq : {z : Position path × Position path | z.1 < z.2} = ⋃ a, ⋃ b, S a b := by
      ext z
      change Position.list path z.1 < Position.list path z.2 ↔ _
      simp only [mem_iUnion, S, mem_ofPred_eq, Position.list]
      constructor
      · intro h
        exact ⟨z.1.1, z.2.1, rfl, rfl, h⟩
      · rintro ⟨a, b, ha, hb, h⟩
        simpa only [ha, hb] using h
    rw [heq]
    exact MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (hS a))

/-- Lebesgue probability measure on the open unit interval. -/
noncomputable def unitLaw : Measure ℝ := volume.restrict (Ioo 0 1)

instance : IsProbabilityMeasure unitLaw := by
  constructor
  simp [unitLaw]

instance : NullSingletonClass unitLaw := inferInstanceAs
  (NullSingletonClass (volume.restrict (Ioo (0 : ℝ) 1)))

/-- The common law used by every queried label. -/
noncomputable def law (path : N ↪ List ℝ) (μ : Measure N) : Measure (Position path) :=
  μ.prod unitLaw

instance (path : N ↪ List ℝ) (μ : Measure N) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (law path μ) := inferInstanceAs (IsProbabilityMeasure (μ.prod unitLaw))

instance (path : N ↪ List ℝ) (μ : Measure N) : NullSingletonClass (law path μ) :=
  inferInstanceAs (NullSingletonClass (μ.prod unitLaw))

/-- The finite uniform-coordinate law agrees with Lebesgue volume on a
system whose stored intervals lie in `(0,1)`. -/
theorem unitLaw_region {n : ℕ} (D : System (Fin n) ℝ)
    (hb : ∀ i, 0 ≤ D.lower i ∧ D.upper i ≤ 1) :
    (Measure.pi (fun _ : Fin n => unitLaw)) (region D) = volume (region D) := by
  have hsub : region D ⊆ Set.univ.pi (fun _ : Fin n => Ioo (0 : ℝ) 1) := by
    intro X hX i hi
    exact ⟨(hb i).1.trans_lt (hX.1 i).1, (hX.1 i).2.trans_le (hb i).2⟩
  rw [unitLaw, ← Measure.restrict_pi_pi, Measure.restrict_apply (region_open D).measurableSet,
    Set.inter_eq_left.mpr hsub]
  rfl

/-- The event before discarding the null set of ties. -/
def assignedRegion {n : ℕ} (path : N ↪ List ℝ) (nodeAt : Fin n → N)
    (D : System (Fin n) ℝ) : Set (Fin n → Position path) :=
  {X | (∀ i, (X i).1 = nodeAt i) ∧ D.StrictlyFeasible (fun i => (X i).2)}

theorem assignedRegion_measurable {n : ℕ} (path : N ↪ List ℝ) (nodeAt : Fin n → N)
    (D : System (Fin n) ℝ) : MeasurableSet (assignedRegion path nodeAt D) := by
  have hnodes : MeasurableSet {X : Fin n → N × ℝ | ∀ i, (X i).1 = nodeAt i} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_eq_fun
      (measurable_fst.comp (measurable_pi_apply i)) measurable_const)
  exact hnodes.inter
    ((region_open D).measurableSet.preimage (measurable_pi_lambda _
      (fun i => measurable_snd.comp (measurable_pi_apply i))))

/-- Exact factorization for actual independent tree draws and the actual
global region, obtained by separating the node and coordinate products. -/
theorem assignedRegion_mass {n : ℕ} (path : N ↪ List ℝ) (μ : Measure N)
    [IsProbabilityMeasure μ] (nodeAt : Fin n → N) (D : System (Fin n) ℝ)
    (hb : ∀ i, 0 ≤ D.lower i ∧ D.upper i ≤ 1) :
    (Measure.pi (fun _ : Fin n => law path μ)).real (assignedRegion path nodeAt D) =
      (∏ i, μ.real {nodeAt i}) * nodeVolume D := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow N ℝ (Fin n)
  have hpre : assignedRegion path nodeAt D = e ⁻¹' ({nodeAt} ×ˢ region D) := by
    ext X
    simp only [assignedRegion, mem_ofPred_eq, mem_preimage, mem_prod, mem_singleton_iff]
    change ((∀ i, (X i).1 = nodeAt i) ∧ _) ↔ (fun i => (X i).1) = nodeAt ∧ _
    rw [funext_iff]
    rfl
  have hmp := measurePreserving_arrowProdEquivProdArrow N ℝ (Fin n)
    (fun _ => μ) (fun _ => unitLaw)
  rw [hpre]
  change (Measure.pi (fun _ : Fin n => μ.prod unitLaw)).real
    ((MeasurableEquiv.arrowProdEquivProdArrow N ℝ (Fin n)) ⁻¹' ({nodeAt} ×ˢ region D)) = _
  rw [hmp.measureReal_preimage
    ((measurableSet_singleton nodeAt).prod (region_open D).measurableSet).nullMeasurableSet,
    measureReal_prod_prod]
  simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod, unitLaw_region D hb,
    nodeVolume]

/-- Discarding ties costs no mass in the concrete common law. -/
theorem assignedRegion_tie_free_mass {n : ℕ} (path : N ↪ List ℝ) (μ : Measure N)
    [IsProbabilityMeasure μ] (nodeAt : Fin n → N) (D : System (Fin n) ℝ) :
    (Measure.pi (fun _ : Fin n => law path μ)).real
        (assignedRegion path nodeAt D ∩ {X | Function.Injective X}) =
      (Measure.pi (fun _ : Fin n => law path μ)).real (assignedRegion path nodeAt D) := by
  apply measureReal_congr
  filter_upwards [atomless_iid_tie_free n (law path μ)] with X hX
  exact propext ⟨fun h => h.1, fun h => ⟨h, hX⟩⟩

/-- Every feasible sample with its assigned nodes induces a transcript-
compatible ranking. This uses the concrete tree's geometric invariant. -/
theorem assignedRegion_compatible {n : ℕ} (s : TreeState.State n ℝ) (h : History n)
    (hs : s.Consistent h) (path : N ↪ List ℝ) (nodeAt : Fin n → N)
    (hlocation : ∀ i, path (nodeAt i) = s.location i)
    (X : Fin n → Position path)
    (hX : X ∈ assignedRegion path nodeAt s.system ∩ {X | Function.Injective X}) :
    ∃ π, Compatible π h ∧ X ∈ orderCell π := by
  obtain ⟨π, hπ⟩ := exists_orderCell X hX.2
  refine ⟨π, ?_, hπ⟩
  apply List.forall_iff_forall_mem.mpr
  intro o ho
  have hold := hs (fun i => (X i).2) hX.1.2 o ho
  have hpos : ∀ i, Position.list path (X i) = s.position (fun i => (X i).2) i := by
    intro i
    simp only [Position.list, TreeState.State.position, hX.1.1 i, hlocation i]
  cases ha : o.answer with
  | less =>
    simp only [Observation.Holds, ha]
    change π o.query.left < π o.query.right
    apply (hπ o.query.left o.query.right).mpr
    change Position.list path (X o.query.left) < Position.list path (X o.query.right)
    rw [hpos, hpos]
    simpa only [TreeState.State.Holds, ha] using hold
  | greater =>
    simp only [Observation.Holds, ha]
    change π o.query.right < π o.query.left
    apply (hπ o.query.right o.query.left).mpr
    change Position.list path (X o.query.right) < Position.list path (X o.query.left)
    rw [hpos, hpos]
    simpa only [TreeState.State.Holds, ha] using hold

/-- Concrete packing for a consistent tree state. No probability of a
feasibility event or symmetry certificate is assumed. -/
theorem count_of_assignedRegion {n : ℕ} (s : TreeState.State n ℝ) (h : History n)
    (hs : s.Consistent h) (hb : ∀ i, 0 ≤ s.system.lower i ∧ s.system.upper i ≤ 1)
    (path : N ↪ List ℝ) (μ : Measure N) [IsProbabilityMeasure μ]
    (nodeAt : Fin n → N) (hlocation : ∀ i, path (nodeAt i) = s.location i) :
    (n.factorial : ℝ) * ((∏ i, μ.real {nodeAt i}) * nodeVolume s.system) ≤
      transcriptCount h := by
  have hcount := count_of_iid_event h (law path μ)
    (atomless_iid_tie_free n (law path μ))
    (assignedRegion path nodeAt s.system ∩ {X | Function.Injective X})
    (assignedRegion_compatible s h hs path nodeAt hlocation)
  rw [assignedRegion_tie_free_mass, assignedRegion_mass path μ nodeAt s.system hb] at hcount
  exact hcount

end SortingAdversary.Continuous.TreeSampling
