import SortingAdversary.Continuous.Reindex
import SortingAdversary.Continuous.RegionMeasure
import SortingAdversary.Continuous.ComparableBound
import SortingAdversary.Optimal.PublicOrder
import SortingAdversary.Optimal.RankWork

/-!
# Computable graph order and invariance under coordinate relabeling

The algorithm computes a topological permutation from the Boolean graph.
A strict rank is used only to verify acyclicity, not as executable input.
The underlying finite closure and predecessor-count ordering are generic
graph routines; no theorem about the earlier adversary is used.
-/

namespace SortingAdversary.Continuous.GraphOrder

open FiniteAveraging OrderRegion MeasureTheory Set
open SortingAdversary.Optimal.SparseClosure SortingAdversary.Optimal.PublicOrder
open SortingAdversary.Optimal.GraphBalls

variable {n : ℕ}

private def witnessKey (rank : Fin n → ℕ) (x : Fin n) : ℕ := rank x * n + x.val

private theorem witnessKey_injective (rank : Fin n → ℕ) : Function.Injective (witnessKey rank) := by
  intro x y hxy
  have h := congrArg (fun z => z % n) hxy
  simp [witnessKey, Nat.add_mod, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at h
  exact Fin.ext h

private theorem witnessKey_strict (rank : Fin n → ℕ) {x y : Fin n} (hxy : rank x < rank y) :
    witnessKey rank x < witnessKey rank y := by
  have hm := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hxy)
  calc
    _ < rank x * n + n := Nat.add_lt_add_left x.isLt _
    _ = (rank x + 1) * n := by simp [Nat.add_mul]
    _ ≤ rank y * n := hm
    _ ≤ witnessKey rank y := Nat.le_add_right _ _

theorem closure_isOrder {K : Type*} (D : System (Fin n) K) (rank : Fin n → ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y) : IsOrder (closure D.edge) := by
  have hres : Respects (closure D.edge) (witnessKey rank) :=
    (respects_closure D.edge (witnessKey rank)).mpr (fun x y h => (witnessKey_strict rank (hrank x y h)).le)
  exact ⟨closure_refl D.edge, closure_trans D.edge, fun x y hxy hyx =>
    witnessKey_injective rank (le_antisymm (hres x y hxy) (hres y x hyx))⟩

/-- A graph-derived strict topological rank. The transitive closure is
materialized once before the returned rank function is evaluated. -/
def graphRank {K : Type*} (D : System (Fin n) K) : Fin n → ℕ :=
  let table := tableClosure D.edge
  let ranks := (SortingAdversary.Optimal.RankWork.storedRanks table).value
  fun x => ranks[x].val

theorem graphRank_eq {K : Type*} (D : System (Fin n) K) (x : Fin n) :
    graphRank D x = (extensionRank (closure D.edge) x).val := by
  simp only [graphRank, SortingAdversary.Optimal.RankWork.storedRanks_value,
    lookup_tableClosure, Fin.getElem_fin, Vector.getElem_ofFn]

theorem graphRank_strict {K : Type*} (D : System (Fin n) K) (rank : Fin n → ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y) :
    ∀ x y, D.edge x y = true → graphRank D x < graphRank D y := by
  intro x y hxy
  have hne : x ≠ y := fun he => by
    subst y
    exact Nat.lt_irrefl _ (hrank x x hxy)
  simpa only [graphRank_eq, Fin.lt_def] using
    extensionRank_strict (closure_isOrder D rank hrank) (closure_old D.edge hxy) hne

/-- New increasing sweep indices are sent to original labels. -/
def orderEquiv {K : Type*} (D : System (Fin n) K) : Fin n ≃ Fin n := rankEquiv (graphRank D)

def indexed {K : Type*} (D : System (Fin n) K) : System (Fin n) K := D.reindex (orderEquiv D)

theorem indexed_order {K : Type*} (D : System (Fin n) K) (rank : Fin n → ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y) :
    ∀ x y, (indexed D).edge x y = true → x.val < y.val :=
  reindex_rankEquiv_order D (graphRank D) (graphRank_strict D rank hrank)

theorem neighbors_reindex_card {ι κ K : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (D : System ι K) (e : κ ≃ ι) (x : κ) :
    (neighbors (D.reindex e).edge x).card = (neighbors D.edge (e x)).card := by
  apply Finset.card_bij (fun y _ => e y)
  · intro y hy
    have h := (mem_neighbors _ _ _).mp hy
    exact (mem_neighbors _ _ _).mpr ⟨fun he => h.1 (e.injective he), h.2⟩
  · intro y _ z _ he
    exact e.injective he
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    simpa only [mem_neighbors, System.reindex, Equiv.apply_symm_apply,
      ne_eq, Equiv.symm_apply_eq] using hy

section Measures

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def assignmentEquiv (e : κ ≃ ι) : (κ → ℝ) ≃ᵐ (ι → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e

@[simp] theorem assignmentEquiv_apply (e : κ ≃ ι) (Y : κ → ℝ) (x : ι) :
    assignmentEquiv e Y x = Y (e.symm x) := by
  unfold assignmentEquiv
  simpa only [Equiv.apply_symm_apply] using
    MeasurableEquiv.piCongrLeft_apply_apply e (β := fun _ : ι => ℝ) Y (e.symm x)

theorem region_reindex (D : System ι ℝ) (e : κ ≃ ι) :
    region (D.reindex e) = assignmentEquiv e ⁻¹' region D := by
  ext Y
  change (D.reindex e).StrictlyFeasible Y ↔ D.StrictlyFeasible (assignmentEquiv e Y)
  rw [show assignmentEquiv e Y = (fun x => Y (e.symm x)) from funext (assignmentEquiv_apply e Y)]
  exact D.reindex_strictlyFeasible_iff e Y

theorem volume_reindex (D : System ι ℝ) (e : κ ≃ ι) :
    volume (region (D.reindex e)) = volume (region D) := by
  rw [region_reindex]
  exact (volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) e).measure_preimage
    (region_open D).measurableSet.nullMeasurableSet

theorem nodeVolume_reindex (D : System ι ℝ) (e : κ ≃ ι) :
    nodeVolume (D.reindex e) = nodeVolume D := congrArg ENNReal.toReal (volume_reindex D e)

theorem uniformMeasure_reindex (D : System ι ℝ) (e : κ ≃ ι)
    (E : Set (ι → ℝ)) (hE : MeasurableSet E) :
    uniformMeasure (D.reindex e) (assignmentEquiv e ⁻¹' E) = uniformMeasure D E := by
  rw [uniformMeasure_apply _ _ (hE.preimage (assignmentEquiv e).measurable),
    uniformMeasure_apply D E hE, volume_reindex, region_reindex,
    ← preimage_inter]
  unfold assignmentEquiv
  rw [(volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) e).measure_preimage
    (hE.inter (region_open D).measurableSet).nullMeasurableSet]

theorem uniformMeasure_reindex_real (D : System ι ℝ) (e : κ ≃ ι)
    (E : Set (ι → ℝ)) (hE : MeasurableSet E) :
    (uniformMeasure (D.reindex e)).real (assignmentEquiv e ⁻¹' E) = (uniformMeasure D).real E :=
  congrArg ENNReal.toReal (uniformMeasure_reindex D e E hE)

end Measures

end SortingAdversary.Continuous.GraphOrder
