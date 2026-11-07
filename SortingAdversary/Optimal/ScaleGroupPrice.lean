import SortingAdversary.Optimal.WidthScaleSelect

/-!
# Prices for every actual chronological scale choice

The accumulated veto in the executable group loop is bounded by the sum of
previous actual window widths. This supplies the quarter-window budget at
each output position, and hence the dyadic size bound for that exact record.
-/

namespace SortingAdversary.Optimal.ScaleHubs

open scoped BigOperators
open StableBatches HubSelector BatchWindows

/-- The selector at an actual output position has precisely a reachable
chronological veto, whose cost is bounded by the preceding width envelope. -/
theorem group_get_budget_aux {births : ℕ} (order : Equiv.Perm (Fin births))
    (W lower upper : ℕ → ℕ) (J : ℕ)
    (hupper : ∀ j, j < J → upper j ≤ births)
    (hsize : ∀ j, j < J → upper j - lower j ≤ W j)
    (step count : ℕ) (veto : Finset Block) (hcap : step + count ≤ J)
    (hcost : vetoCost veto ≤ ∑ j ∈ Finset.range step, W j)
    (i : ℕ)
    (hi : i < (selectGroup births
      (fun j => batchThreshold (paletteRank order) (paletteRank_injective order) (lower j + 1))
      (fun j => batchThreshold (paletteRank order) (paletteRank_injective order) (upper j - 1))
      step count veto).length) :
    ∃ prior,
      selectWindow order (lower (step + i) + 1) (upper (step + i) - 1) prior =
        some ((selectGroup births
          (fun j => batchThreshold (paletteRank order) (paletteRank_injective order) (lower j + 1))
          (fun j => batchThreshold (paletteRank order) (paletteRank_injective order) (upper j - 1))
          step count veto)[i]'hi) ∧
      vetoCost prior ≤ ∑ j ∈ Finset.range (step + i), W j := by
  induction count generalizing step veto i with
  | zero => simp [selectGroup] at hi
  | succ count ih =>
    have hstep : step < J := by omega
    cases hsel : selectWindow order (lower step + 1) (upper step - 1) veto with
    | none =>
      change selectBlock births _ _ veto = none at hsel
      simp [selectGroup, hsel] at hi
    | some a =>
      have hnot : a ∉ veto := (selected_spec hsel).2.2
      have hsmall : a.size ≤ W step := by
        have hs := selected_size_le_window order (by have := hupper step hstep; omega) hsel
        exact hs.trans ((by omega : upper step - 1 - (lower step + 1) ≤ upper step - lower step).trans
          (hsize step hstep))
      have hcost' : vetoCost (insert a veto) ≤ ∑ j ∈ Finset.range (step + 1), W j := by
        rw [Finset.sum_range_succ]
        simp only [vetoCost, Finset.sum_insert hnot]
        change a.size + vetoCost veto ≤ _
        omega
      change selectBlock births _ _ veto = some a at hsel
      cases i with
      | zero =>
        refine ⟨veto, ?_, ?_⟩
        · simpa only [Nat.add_zero, selectWindow, selectGroup, hsel, List.getElem_cons_zero] using hsel
        · simpa only [Nat.add_zero] using hcost
      | succ i =>
        have hi' : i < (selectGroup births
            (fun j => batchThreshold (paletteRank order) (paletteRank_injective order) (lower j + 1))
            (fun j => batchThreshold (paletteRank order) (paletteRank_injective order) (upper j - 1))
            (step + 1) count (insert a veto)).length := by
          simpa only [selectGroup, hsel, List.length_cons, Nat.succ_lt_succ_iff] using hi
        obtain ⟨prior, hp, hc⟩ := ih (step + 1) (insert a veto) (by omega) hcost' i hi'
        refine ⟨prior, ?_, ?_⟩
        · simpa only [selectGroup, hsel, List.getElem_cons_succ, Nat.add_assoc,
            Nat.add_comm 1 i] using hp
        · simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hc

/-- The true prior veto at each computed scale position satisfies the
quarter-window condition required by the deterministic dyadic price lemma. -/
theorem selectPaletteGroup_get_budget {births : ℕ} (order : Equiv.Perm (Fin births))
    (W lower upper : ℕ → ℕ) (A L w J : ℕ) (hA : 1 ≤ A) (hgap : 8 * J * L ≤ A)
    (hwidth : ∀ i, i < J → A ^ i * w ≤ W i ∧ W i ≤ L * (A ^ i * w))
    (hupper : ∀ j, j < J → upper j ≤ births)
    (hsize : ∀ j, j < J → upper j - lower j ≤ W j)
    (hcentral : ∀ j, j < J → W j ≤ 2 * (upper j - lower j))
    (i : ℕ) (hi : i < (selectPaletteGroup order lower upper J).length) :
    ∃ prior,
      selectWindow order (lower i + 1) (upper i - 1) prior =
        some ((selectPaletteGroup order lower upper J)[i]'hi) ∧
      4 * vetoCost prior ≤ upper i - lower i := by
  obtain ⟨prior, hp, hc⟩ := group_get_budget_aux order W lower upper J hupper hsize
    0 J ∅ (by omega) (by simp [vetoCost]) i hi
  have hiJ : i < J := hi.trans_le (selectGroup_length_le _ _ _ _ _ _)
  refine ⟨prior, ?_, ?_⟩
  · convert hp using 1 <;> simp only [Nat.zero_add, selectPaletteGroup]
    rfl
  · simp only [Nat.zero_add] at hc
    exact (Nat.mul_le_mul_left 4 hc).trans
      (central_prefix_budget W lower upper A L w J hA hgap hwidth hcentral i hiJ)

/-- Quantitative price for the exact block at an actual group position. -/
theorem selectPaletteGroup_price {births M : ℕ} (order : Equiv.Perm (Fin births))
    (W lower upper : ℕ → ℕ) (A L w J : ℕ) (hA : 1 ≤ A) (hgap : 8 * J * L ≤ A)
    (hwidth : ∀ i, i < J → A ^ i * w ≤ W i ∧ W i ≤ L * (A ^ i * w))
    (hupper : ∀ j, j < J → upper j ≤ births)
    (hlarge : ∀ j, j < J → 8 ≤ upper j - lower j)
    (hsize : ∀ j, j < J → upper j - lower j ≤ W j)
    (hcentral : ∀ j, j < J → W j ≤ 2 * (upper j - lower j))
    (hcap : births ≤ 2 ^ M)
    (i : ℕ) (hi : i < (selectPaletteGroup order lower upper J).length) :
    upper i - lower i ≤
      8 * ((selectPaletteGroup order lower upper J)[i]'hi).size *
        (M - ((selectPaletteGroup order lower upper J)[i]'hi).level + 2) := by
  obtain ⟨prior, hp, hb⟩ := selectPaletteGroup_get_budget order W lower upper A L w J hA hgap
    hwidth hupper hsize hcentral i hi
  have hiJ : i < J := hi.trans_le (selectGroup_length_le _ _ _ _ _ _)
  exact selected_trimmed_window_bound order hcap (hupper i hiJ) (hlarge i hiJ) hb hp

end SortingAdversary.Optimal.ScaleHubs

namespace SortingAdversary.Optimal.WidthRepair.ScaleTrigger

open ScaleHubs ScaleMass StableBatches HubSelector BatchWindows

variable {n : ℕ} {s : State n} {p : ScaleParameters}

/-- The concrete first-crossing reservation's selected record pays for its
whole central insertion interval. -/
theorem block_price (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L)
    (M : ℕ) (hcap : s.pool.palette + 1 ≤ 2 ^ M) (i : Fin p.J) :
    trigger.upper i.val - trigger.lower i.val ≤
      8 * (trigger.block normal i).size * (M - (trigger.block normal i).level + 2) := by
  apply selectPaletteGroup_price s.order trigger.widths trigger.lower trigger.upper
    p.A p.width.L (s.width trigger.low) p.J p.one_le_A p.veto_gap
  · intro j hj
    simpa only [widths, dif_pos hj] using trigger.vertices_bounds normal ⟨j, hj⟩
  · intro j hj
    simp only [upper, dif_pos hj]
    exact interval_upper_le s.numerical s.numerical_feasible _
  · intro j hj
    simp only [upper, lower, dif_pos hj]
    apply interval_large s.numerical s.numerical_feasible
    rw [s.numerical_width]
    exact p.width.large.trans (normal.wide _ (trigger.vertices_incident normal ⟨j, hj⟩))
  · intro j hj
    simp only [upper, lower, widths, dif_pos hj]
    simpa only [s.numerical_width] using (interval_length s.numerical s.numerical_feasible _).2
  · intro j hj
    simp only [upper, lower, widths, dif_pos hj]
    simpa only [s.numerical_width] using (interval_length s.numerical s.numerical_feasible _).1
  · exact hcap

/-- The actual scale pin's rational count charge has the required block form. -/
theorem charge_price (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L)
    (M : ℕ) (hcap : s.pool.palette + 1 ≤ 2 ^ M) (i : Fin p.J) :
    (2 * 4 ^ p.width.B * (trigger.upper i.val - trigger.lower i.val) : ℕ) ≤
      16 * 4 ^ p.width.B * (trigger.block normal i).size *
        (M - (trigger.block normal i).level + 2) := by
  have h := Nat.mul_le_mul_left (2 * 4 ^ p.width.B) (trigger.block_price normal M hcap i)
  convert h using 1 <;> ring

end SortingAdversary.Optimal.WidthRepair.ScaleTrigger
