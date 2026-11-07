import SortingAdversary.Optimal.ScaleGeometry
import SortingAdversary.Optimal.BatchWindows

/-!
# Actual scale-group hub selection cannot exhaust its windows

The total size of earlier selected blocks is controlled by the actual earlier
windows. The first-crossing scale bounds give a quarter-window veto budget.
Consequently the existing executable `selectGroup` completes all requested
steps; no success or admissibility conclusion is supplied as a hypothesis.
-/

namespace SortingAdversary.Optimal.ScaleHubs

open scoped BigOperators
open ScaleGeometry StableBatches HubSelector BatchWindows

/-- A block selected from a real palette interval cannot be larger than that
interval. This supplies the actual cost of each later veto. -/
theorem selected_size_le_window {births lower upper : ℕ}
    (order : Equiv.Perm (Fin births)) {veto : Finset Block} {chosen : Block}
    (hupper : upper ≤ births) (hchosen : selectWindow order lower upper veto = some chosen) :
    chosen.size ≤ upper - lower := by
  let lo := batchThreshold (paletteRank order) (paletteRank_injective order) lower
  let hi := batchThreshold (paletteRank order) (paletteRank_injective order) upper
  have hs := selected_spec hchosen
  have hb : chosen.batch ∈ batches births :=
    (mem_batches _ _).mpr ((mem_allBlocks _ _).mp hs.1).1
  have hlocal : chosen.size ≤ hi chosen.batch - lo chosen.batch := by
    have hw : lo chosen.batch ≤ chosen.start ∧ chosen.stop ≤ hi chosen.batch := hs.2.1
    have hstop : chosen.stop = chosen.start + chosen.size := by
      simp [Block.stop, Block.start, Nat.add_mul, Nat.add_comm]
    omega
  have hsum : hi chosen.batch - lo chosen.batch ≤ windowCount births lo hi :=
    Finset.single_le_sum (f := fun b => hi b - lo b) (fun _ _ => Nat.zero_le _) hb
  exact (hlocal.trans hsum).trans_eq (palette_batch_window_count order lower upper hupper)

/-- A quarter-window budget leaves a nonempty interval after trimming the two
endpoints, so the actual deterministic selector returns a block. -/
theorem trimmed_selection_exists {births lower upper : ℕ}
    (order : Equiv.Perm (Fin births)) (veto : Finset Block) (hupper : upper ≤ births)
    (hlarge : 8 ≤ upper - lower) (hbudget : 4 * vetoCost veto ≤ upper - lower) :
    ∃ chosen, selectWindow order (lower + 1) (upper - 1) veto = some chosen := by
  apply selectWindow_exists order veto (by omega)
  omega

/-- Earlier widths obeying the first-crossing envelopes have a small total
compared to the next scale. The constant is independent of the group length. -/
theorem geometric_prefix_bound (W : ℕ → ℕ) (A L w J : ℕ) (hA : 1 ≤ A)
    (hgap : 8 * J * L ≤ A)
    (hwidth : ∀ i, i < J → A ^ i * w ≤ W i ∧ W i ≤ L * (A ^ i * w))
    (j : ℕ) (hj : j < J) : 8 * (∑ i ∈ Finset.range j, W i) ≤ W j := by
  by_cases hjzero : j = 0
  · subst j; simp
  have hprev : ∀ i ∈ Finset.range j, W i ≤ L * (A ^ (j - 1) * w) := by
    intro i hi
    have hij : i < j := Finset.mem_range.mp hi
    have hu := (hwidth i (hij.trans hj)).2
    have hp : A ^ i ≤ A ^ (j - 1) := Nat.pow_le_pow_right hA (by omega)
    exact hu.trans (Nat.mul_le_mul_left L (Nat.mul_le_mul_right w hp))
  have hsum : (∑ i ∈ Finset.range j, W i) ≤ j * (L * (A ^ (j - 1) * w)) := by
    have h := Finset.sum_le_sum hprev
    simpa using h
  have hJ : j * (L * (A ^ (j - 1) * w)) ≤ J * (L * (A ^ (j - 1) * w)) :=
    Nat.mul_le_mul_right _ hj.le
  have hscale : 8 * (J * (L * (A ^ (j - 1) * w))) ≤ A ^ j * w := by
    calc
      _ = (8 * J * L) * (A ^ (j - 1) * w) := by ring
      _ ≤ A * (A ^ (j - 1) * w) := Nat.mul_le_mul_right _ hgap
      _ = A ^ j * w := by
        have hj' : j - 1 + 1 = j := by omega
        calc
          _ = A ^ (j - 1 + 1) * w := by rw [pow_succ]; ring
          _ = A ^ j * w := by rw [hj']
  exact (Nat.mul_le_mul_left 8 (hsum.trans hJ)).trans (hscale.trans (hwidth j hj).1)

/-- Central intervals have at least half their full width. Thus the previous
scale bound supplies exactly the budget required by the trimmed hub selector. -/
theorem central_prefix_budget (W lower upper : ℕ → ℕ) (A L w J : ℕ) (hA : 1 ≤ A)
    (hgap : 8 * J * L ≤ A)
    (hwidth : ∀ i, i < J → A ^ i * w ≤ W i ∧ W i ≤ L * (A ^ i * w))
    (hcentral : ∀ i, i < J → W i ≤ 2 * (upper i - lower i))
    (j : ℕ) (hj : j < J) : 4 * (∑ i ∈ Finset.range j, W i) ≤ upper j - lower j := by
  have hp := geometric_prefix_bound W A L w J hA hgap hwidth j hj
  have hc := hcentral j hj
  omega

/-- The manuscript's explicit `A` supplies the needed width gap. -/
theorem scaleBase_veto_gap (J L H : ℕ) : 8 * J * L ≤ scaleBase J L H := by
  have hp : L ≤ (L + 1) ^ (2 * H + 3) := by
    apply (Nat.le_succ L).trans
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (Nat.succ_pos L) (by omega : 1 ≤ 2 * H + 3))
  have hm := Nat.mul_le_mul_left (8 * J) hp
  unfold scaleBase
  nlinarith

/-- The existing group executor on the actual trimmed palette intervals. -/
def selectPaletteGroup {births : ℕ} (order : Equiv.Perm (Fin births))
    (lower upper : ℕ → ℕ) (J : ℕ) : List Block :=
  selectGroup births
    (fun j => batchThreshold (paletteRank order) (paletteRank_injective order) (lower j + 1))
    (fun j => batchThreshold (paletteRank order) (paletteRank_injective order) (upper j - 1))
    0 J ∅

/-- A quantitative invariant for the *actual* chronological selection loop.
It charges each selected block by its window, then proves that no step fails. -/
theorem group_length_eq_aux {births : ℕ} (order : Equiv.Perm (Fin births))
    (W lower upper : ℕ → ℕ) (J : ℕ)
    (hupper : ∀ j, j < J → upper j ≤ births)
    (hlarge : ∀ j, j < J → 8 ≤ upper j - lower j)
    (hsize : ∀ j, j < J → upper j - lower j ≤ W j)
    (hbudget : ∀ j, j < J → 4 * (∑ i ∈ Finset.range j, W i) ≤ upper j - lower j)
    (step count : ℕ) (veto : Finset Block) (hcap : step + count ≤ J)
    (hcost : vetoCost veto ≤ ∑ i ∈ Finset.range step, W i) :
    (selectGroup births
      (fun j => batchThreshold (paletteRank order) (paletteRank_injective order) (lower j + 1))
      (fun j => batchThreshold (paletteRank order) (paletteRank_injective order) (upper j - 1))
      step count veto).length = count := by
  induction count generalizing step veto with
  | zero => rfl
  | succ count ih =>
    have hstep : step < J := by omega
    have hveto : 4 * vetoCost veto ≤ upper step - lower step :=
      (Nat.mul_le_mul_left 4 hcost).trans (hbudget step hstep)
    obtain ⟨chosen, hchosen⟩ := trimmed_selection_exists order veto (hupper step hstep)
      (hlarge step hstep) hveto
    have hnot : chosen ∉ veto := (selected_spec hchosen).2.2
    have hsmall : chosen.size ≤ W step := by
      have hs := selected_size_le_window order (by have := hupper step hstep; omega) hchosen
      exact hs.trans ((by omega : upper step - 1 - (lower step + 1) ≤ upper step - lower step).trans
        (hsize step hstep))
    have hcost' : vetoCost (insert chosen veto) ≤ ∑ i ∈ Finset.range (step + 1), W i := by
      rw [Finset.sum_range_succ]
      simp only [vetoCost, Finset.sum_insert hnot]
      change chosen.size + vetoCost veto ≤ _
      omega
    have hrec := ih (step + 1) (insert chosen veto) (by omega) hcost'
    change selectBlock births _ _ veto = some chosen at hchosen
    simp only [selectGroup, hchosen, List.length_cons, hrec]

/-- The complete actual scale-group selector returns every requested choice,
using only the geometric scale envelopes and central-window lengths. -/
theorem selectPaletteGroup_length {births : ℕ} (order : Equiv.Perm (Fin births))
    (W lower upper : ℕ → ℕ) (A L w J : ℕ) (hA : 1 ≤ A) (hgap : 8 * J * L ≤ A)
    (hwidth : ∀ i, i < J → A ^ i * w ≤ W i ∧ W i ≤ L * (A ^ i * w))
    (hupper : ∀ j, j < J → upper j ≤ births)
    (hlarge : ∀ j, j < J → 8 ≤ upper j - lower j)
    (hsize : ∀ j, j < J → upper j - lower j ≤ W j)
    (hcentral : ∀ j, j < J → W j ≤ 2 * (upper j - lower j)) :
    (selectPaletteGroup order lower upper J).length = J := by
  exact group_length_eq_aux order W lower upper J hupper hlarge hsize
    (central_prefix_budget W lower upper A L w J hA hgap hwidth hcentral)
    0 J ∅ (by omega) (by simp [vetoCost])

theorem selectPaletteGroup_nodup {births : ℕ} (order : Equiv.Perm (Fin births))
    (lower upper : ℕ → ℕ) (J : ℕ) : (selectPaletteGroup order lower upper J).Nodup :=
  selectGroup_nodup _ _ _ _ _ _

/-- Every actual output position comes from the selector at that chronological
step, with the accumulated veto used by the executor. -/
theorem selectGroup_get_spec (births : ℕ) (lo hi : ℕ → Batch → ℕ)
    (step count : ℕ) (veto : Finset Block) (i : ℕ)
    (hi' : i < (selectGroup births lo hi step count veto).length) :
    ∃ prior, selectBlock births (lo (step + i)) (hi (step + i)) prior =
      some ((selectGroup births lo hi step count veto)[i]'hi') := by
  induction count generalizing step veto i with
  | zero => simp [selectGroup] at hi'
  | succ count ih =>
    cases hsel : selectBlock births (lo step) (hi step) veto with
    | none => simp [selectGroup, hsel] at hi'
    | some a =>
      cases i with
      | zero =>
        refine ⟨veto, ?_⟩
        simp [selectGroup, hsel]
      | succ i =>
        have hi'' : i < (selectGroup births lo hi (step + 1) count (insert a veto)).length := by
          simpa [selectGroup, hsel] using hi'
        obtain ⟨prior, hprior⟩ := ih (step + 1) (insert a veto) i hi''
        refine ⟨prior, ?_⟩
        simpa [selectGroup, hsel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hprior

/-- The selected color at each actual scale-group position is strictly inside
its untrimmed input interval. Thus scale choices need no endpoint split. -/
theorem selectPaletteGroup_get_interior {births : ℕ} (order : Equiv.Perm (Fin births))
    (lower upper : ℕ → ℕ) (J i : ℕ)
    (hi : i < (selectPaletteGroup order lower upper J).length) :
    lower i < paletteRank order
      (hubColour (paletteRank order) (paletteRank_injective order)
        ((selectPaletteGroup order lower upper J)[i]'hi)) ∧
    paletteRank order (hubColour (paletteRank order) (paletteRank_injective order)
      ((selectPaletteGroup order lower upper J)[i]'hi)) + 1 < upper i := by
  obtain ⟨prior, hprior⟩ := selectGroup_get_spec births
    (fun j => batchThreshold (paletteRank order) (paletteRank_injective order) (lower j + 1))
    (fun j => batchThreshold (paletteRank order) (paletteRank_injective order) (upper j - 1))
    0 J ∅ i hi
  have hsel : selectWindow order (lower i + 1) (upper i - 1) prior =
      some ((selectPaletteGroup order lower upper J)[i]'hi) := by
    convert hprior using 1 <;> simp only [selectWindow, selectPaletteGroup, Nat.zero_add]
    rfl
  have h := selected_hub_in_window order hsel
  omega

/-- Each child color receives at most two of the actual selected blocks, one
of each veto type. This uses the existing immutable dictionary proof. -/
theorem selectPaletteGroup_multiplicity {births : ℕ} (order : Equiv.Perm (Fin births))
    (lower upper : ℕ → ℕ) (J c : ℕ) :
    ((selectPaletteGroup order lower upper J).toFinset.filter (fun a =>
      hubColour (paletteRank order) (paletteRank_injective order) a = c)).card ≤ 2 := by
  apply selected_colour_multiplicity_le_two (paletteRank order) (paletteRank_injective order)
  intro a ha
  exact selectGroup_mem_allBlocks _ _ _ _ _ _ (List.mem_toFinset.mp ha)

end SortingAdversary.Optimal.ScaleHubs
