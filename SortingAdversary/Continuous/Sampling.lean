import SortingAdversary.Continuous.Counting
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Hom.Set

/-!
# Independent identical draws and uniform relative orders

The product measure is constructed here, not provided as a list of assumed
order probabilities. Permuting its coordinates preserves it. Once ties have
measure zero, its `n!` ordering cells therefore all have mass `1/n!`.

The tie-free property is proved for an atomless common law. The probability of
the tree-feasibility event remains a separate obligation: this module does not
identify an arbitrary numeric `Z` with a product of node volumes.
-/

namespace SortingAdversary.Continuous

open MeasureTheory Set Filter
open scoped BigOperators

/-- Measurability of strict comparison, separated from any choice of order
 topology. This accommodates the lexicographic positions of the tree. -/
class MeasurableStrictOrder (α : Type*) [LT α] [MeasurableSpace α] : Prop where
  measurable_lt : MeasurableSet {p : α × α | p.1 < p.2}

instance : MeasurableStrictOrder ℝ := ⟨measurableSet_lt'⟩

variable {α : Type*} [LinearOrder α] [MeasurableSpace α] [MeasurableEq α]
  [MeasurableStrictOrder α]

/-- The open chamber of ordered positions that induces a given ranking. -/
def orderCell {n : ℕ} (π : Ranking n) : Set (Item n → α) :=
  {x | ∀ i j, π i < π j ↔ x i < x j}

omit [MeasurableEq α] in
theorem orderCell_measurable {n : ℕ} (π : Ranking n) : MeasurableSet (orderCell (α := α) π) := by
  simp only [orderCell, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  have hlt : MeasurableSet {x : Item n → α | x i < x j} :=
    MeasurableStrictOrder.measurable_lt.preimage
      ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
  by_cases hij : π i < π j
  · convert hlt using 1
    ext x
    simp [hij]
  · convert hlt.compl using 1
    ext x
    simp [hij]

omit [MeasurableSpace α] [MeasurableEq α] [MeasurableStrictOrder α] in
theorem orderCell_injective {n : ℕ} {π : Ranking n} {x : Item n → α}
    (hx : x ∈ orderCell π) : Function.Injective x := by
  intro i j hij
  apply π.injective
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := (hx i j).mp hlt
    exact h.ne hij
  · have h := (hx j i).mp hgt
    exact h.ne hij.symm

omit [MeasurableSpace α] [MeasurableEq α] [MeasurableStrictOrder α] in
theorem exists_orderCell {n : ℕ} (x : Item n → α) (hx : Function.Injective x) :
    ∃ π : Ranking n, x ∈ orderCell π := by
  let : LE (ULift.{0} (Fin n)) := ⟨fun a b => x a.down ≤ x b.down⟩
  let : LT (ULift.{0} (Fin n)) := ⟨fun a b => x a.down < x b.down⟩
  let : LinearOrder (ULift.{0} (Fin n)) :=
    LinearOrder.lift' (fun u : ULift.{0} (Fin n) => x u.down)
      (fun a b hab => ULift.ext a b (hx hab))
  let e := Fintype.orderIsoFinOfCardEq (ULift.{0} (Fin n)) (k := n) (by
    rw [Fintype.card_ulift, Fintype.card_fin])
  let π : Ranking n := Equiv.ulift.symm.trans e.symm.toEquiv
  refine ⟨π, ?_⟩
  intro i j
  change e.symm (ULift.up i) < e.symm (ULift.up j) ↔ x i < x j
  rw [← not_le, ← not_le]
  exact not_congr e.symm.map_rel_iff'

omit [MeasurableSpace α] [MeasurableEq α] [MeasurableStrictOrder α] in
theorem orderCell_unique {n : ℕ} {π σ : Ranking n} {x : Item n → α}
    (hπ : x ∈ orderCell π) (hσ : x ∈ orderCell σ) : π = σ := by
  let e : Fin n ≃o Fin n :=
    { toEquiv := π.symm.trans σ
      map_rel_iff' := by
        intro i j
        change σ (π.symm i) ≤ σ (π.symm j) ↔ i ≤ j
        rw [← not_lt, ← not_lt]
        apply not_congr
        have h := (hσ (π.symm j) (π.symm i)).trans (hπ (π.symm j) (π.symm i)).symm
        simpa using h }
  have he : e = OrderIso.refl (Fin n) := Subsingleton.elim _ _
  apply Equiv.ext
  intro i
  have hi := congrArg (fun f : Fin n ≃o Fin n => f (π i)) he
  simpa [e] using hi.symm

omit [MeasurableSpace α] [MeasurableEq α] [MeasurableStrictOrder α] in
theorem orderCells_disjoint (n : ℕ) : Pairwise (fun π σ : Ranking n => Disjoint (orderCell (α := α) π) (orderCell σ)) := by
  intro π σ hne
  apply Set.disjoint_left.mpr
  intro x hπ hσ
  exact hne (orderCell_unique hπ hσ)

omit [MeasurableSpace α] [MeasurableEq α] [MeasurableStrictOrder α] in
theorem union_orderCells (n : ℕ) :
    (⋃ π : Ranking n, orderCell (α := α) π) = {x | Function.Injective x} := by
  ext x
  simp only [mem_iUnion, mem_ofPred_eq]
  exact ⟨fun ⟨π, hπ⟩ => orderCell_injective hπ, exists_orderCell x⟩

omit [MeasurableEq α] [MeasurableStrictOrder α] in
/-- Reindexing coordinates pulls an ordering cell back to the relabelled cell. -/
theorem preimage_orderCell {n : ℕ} (σ π : Ranking n) :
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => α) σ) ⁻¹' orderCell π =
      orderCell (σ.trans π) := by
  ext x
  constructor
  · intro h i j
    have hi := h (σ i) (σ j)
    simpa only [MeasurableEquiv.piCongrLeft_apply_apply, Equiv.trans_apply] using hi
  · intro h i j
    have hi := h (σ.symm i) (σ.symm j)
    simpa [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft] using hi

omit [LinearOrder α] [MeasurableStrictOrder α] in
/-- Two different coordinates of an atomless product law agree with
probability zero. Fubini reduces the event to singleton slices. -/
theorem iid_coordinates_ne {n : ℕ} (ν : Measure α) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (i j : Fin n) (hij : i ≠ j) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => ν), x i ≠ x j := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) i
    let A : Set (α × (Fin n → α)) := {p | p.1 = p.2 j'}
    have hA : MeasurableSet A :=
      measurableSet_eq_fun measurable_fst ((measurable_pi_apply j').comp measurable_snd)
    have hzero : (ν.prod (Measure.pi (fun _ : Fin n => ν))) A = 0 := by
      rw [Measure.prod_apply_symm hA]
      simp [A]
    have hpre : {x : Fin (n + 1) → α | x i = x (i.succAbove j')} = e ⁻¹' A := by
      ext x
      rfl
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) i
    apply compl_mem_ae_iff.mpr
    change (Measure.pi (fun _ : Fin (n + 1) => ν)) {x | x i = x (i.succAbove j')} = 0
    rw [hpre, hmp.measure_preimage hA.nullMeasurableSet]
    exact hzero

omit [LinearOrder α] [MeasurableStrictOrder α] in
theorem atomless_iid_tie_free (n : ℕ) (ν : Measure α) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => ν), Function.Injective x := by
  have hp : ∀ i j : Fin n,
      ∀ᵐ x ∂Measure.pi (fun _ : Fin n => ν), i ≠ j → x i ≠ x j := by
    intro i j
    by_cases h : i = j
    · exact Filter.Eventually.of_forall (fun _ hne => False.elim (hne h))
    · filter_upwards [iid_coordinates_ne ν i j h] with x hx
      exact fun _ => hx
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hp i))] with x hx
  intro i j heq
  by_contra hne
  exact hx i j hne heq

omit [MeasurableEq α] in
/-- Identical independent coordinates give every relative order the same mass.
The only probabilistic premise is that ties occur with probability zero. -/
theorem iid_orderCell_mass {n : ℕ} (ν : Measure α) [IsProbabilityMeasure ν]
    (hties : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => ν), Function.Injective x)
    (π : Ranking n) :
    (Measure.pi (fun _ : Fin n => ν)).real (orderCell π) = 1 / (n.factorial : ℝ) := by
  let μ := Measure.pi (fun _ : Fin n => ν)
  have hnormal : ∑ ρ : Ranking n, μ.real (orderCell ρ) = 1 := by
    rw [← measureReal_iUnion_fintype (orderCells_disjoint n) orderCell_measurable,
      union_orderCells]
    have heq : {x | Function.Injective x} =ᵐ[μ] Set.univ := by
      filter_upwards [hties] with x hx
      exact propext ⟨fun _ => trivial, fun _ => hx⟩
    rw [measureReal_congr heq]
    simp [μ]
  have hsym : ∀ σ ρ : Ranking n, μ.real (orderCell (σ.trans ρ)) = μ.real (orderCell ρ) := by
    intro σ ρ
    have hmp := measurePreserving_piCongrLeft (fun _ : Fin n => ν) σ
    rw [← preimage_orderCell σ ρ]
    exact hmp.measureReal_preimage (orderCell_measurable ρ).nullMeasurableSet
  exact symmetric_rank_mass _ hnormal hsym π

/-- Uniformity of all relative orders under genuinely independent identical
atomless draws, with no supplied symmetry or order-probability certificate. -/
theorem atomless_iid_orderCell_mass {n : ℕ} (ν : Measure α) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (π : Ranking n) :
    (Measure.pi (fun _ : Fin n => ν)).real (orderCell π) = 1 / (n.factorial : ℝ) :=
  iid_orderCell_mass ν (atomless_iid_tie_free n ν) π

omit [MeasurableEq α] in
/-- Every event all of whose outcomes give a compatible ranking supplies a
lower bound on the number of transcript-compatible orders. -/
theorem count_of_iid_event {n : ℕ} (h : History n) (ν : Measure α)
    [IsProbabilityMeasure ν]
    (hties : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => ν), Function.Injective x)
    (good : Set (Item n → α))
    (hgood : ∀ x ∈ good, ∃ π, Compatible π h ∧ x ∈ orderCell π) :
    (n.factorial : ℝ) * (Measure.pi (fun _ : Fin n => ν)).real good ≤ transcriptCount h := by
  classical
  let μ := Measure.pi (fun _ : Fin n => ν)
  have hsubset : good ⊆ ⋃ π : {π // π ∈ compatibleOrders h}, orderCell π.val := by
    intro x hx
    obtain ⟨π, hπ, hxπ⟩ := hgood x hx
    exact Set.mem_iUnion.mpr ⟨⟨π, (mem_compatibleOrders h π).mpr hπ⟩, hxπ⟩
  have hmono : μ.real good ≤ μ.real (⋃ π : {π // π ∈ compatibleOrders h}, orderCell π.val) :=
    measureReal_mono hsubset
  have hd : Pairwise (fun π σ : {π // π ∈ compatibleOrders h} => Disjoint (orderCell (α := α) π.val) (orderCell σ.val)) := by
    intro π σ hne
    exact orderCells_disjoint n (fun heq => hne (Subtype.ext heq))
  rw [measureReal_iUnion_fintype hd (fun π => orderCell_measurable π.val)] at hmono
  dsimp only [μ] at hmono
  simp_rw [iid_orderCell_mass ν hties] at hmono
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] at hmono
  have hn : (0 : ℝ) < n.factorial := by positivity
  have hm := mul_le_mul_of_nonneg_left hmono hn.le
  have heq : (n.factorial : ℝ) * ((compatibleOrders h).card * (1 / n.factorial)) =
      (compatibleOrders h).card := by field_simp
  rw [heq] at hm
  exact hm

end SortingAdversary.Continuous
