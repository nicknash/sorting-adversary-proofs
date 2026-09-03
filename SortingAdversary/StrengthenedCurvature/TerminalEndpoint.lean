import SortingAdversary.StrengthenedCurvature.Barrier
import SortingAdversary.StrengthenedCurvature.PathDeterminant
import SortingAdversary.StrengthenedCurvature.TerminalHistory
import SortingAdversary.AsymptoticStatement
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Order

/-!
# The terminal grounded path inside the full barrier

For every nonzero rank, choose one occurrence of its adjacent comparison from
the terminal transcript.  Mark the lower boundary row by `none` and comparison
rows by `some o`; this makes the selected rows visibly distinct even before
mapping them to matrices.  A sub-permutation argument then expresses the full
Hessian as the grounded path Hessian plus a positive-semidefinite remainder.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

/-- Finite AM--GM in the exact form needed for the first `n` path slacks. -/
theorem prod_le_inv_pow_of_sum_le_one {n : ℕ} (hn : 0 < n)
    (s : Fin n → ℝ) (hs : ∀ i, 0 < s i) (hsum : ∑ i, s i ≤ 1) :
    ∏ i, s i ≤ (1 / (n : ℝ)) ^ n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hamgm := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin n))
    (fun _ => (1 : ℝ)) s (by simp) (by simp [hnreal])
      (fun i _ => (hs i).le)
  have hroot : (∏ i, s i) ^ ((n : ℝ)⁻¹) ≤ 1 / (n : ℝ) := by
    calc
      (∏ i, s i) ^ ((n : ℝ)⁻¹) ≤ (∑ i, s i) / (n : ℝ) := by
        simpa [Real.rpow_one] using hamgm
      _ ≤ 1 / (n : ℝ) := (div_le_div_iff_of_pos_right hnreal).2 hsum
  have hprod0 : 0 ≤ ∏ i, s i := Finset.prod_nonneg fun i _ => (hs i).le
  have hinv0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have := (Real.rpow_inv_le_iff_of_pos hprod0 hinv0 hnreal).1 hroot
  simpa [Real.rpow_natCast] using this

/-- Squaring and inverting the AM--GM bound gives the grounded-path
determinant estimate. -/
theorem pow_two_mul_card_le_prod_inverse_sq {n : ℕ} (hn : 0 < n)
    (s : Fin n → ℝ) (hs : ∀ i, 0 < s i) (hsum : ∑ i, s i ≤ 1) :
    (n : ℝ) ^ (2 * n) ≤ ∏ i, 1 / s i ^ 2 := by
  have hprod := prod_le_inv_pow_of_sum_le_one hn s hs hsum
  have hprodpos : 0 < ∏ i, s i := Finset.prod_pos fun i _ => hs i
  have hboundpos : 0 < (1 / (n : ℝ)) ^ n := by positivity
  have hinv : (n : ℝ) ^ n ≤ ∏ i, 1 / s i := by
    have hrecip := one_div_le_one_div_of_le hprodpos hprod
    simpa [one_div, Finset.prod_inv_distrib, inv_pow] using hrecip
  have hsquare := mul_self_le_mul_self (by positivity : 0 ≤ (n : ℝ) ^ n) hinv
  calc
    (n : ℝ) ^ (2 * n) = ((n : ℝ) ^ n) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ (∏ i, 1 / s i) ^ 2 := by simpa [pow_two] using hsquare
    _ = ∏ i, 1 / s i ^ 2 := by
      rw [pow_two, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      ring

/-- Last rank of a nonempty finite order. -/
def lastRank {n : ℕ} (hn : 0 < n) : Fin n :=
  ⟨n - 1, Nat.sub_lt hn (by omega)⟩

/-- The first `n` grounded-path slacks telescope to the coordinate of the
largest-ranked item. -/
theorem sum_labelledPathSlack {n : ℕ} (hn : 0 < n)
    (π : Ranking n) (x : Placement n) :
    ∑ i, labelledPathSlack π x i = x (π.symm (lastRank hn)) := by
  cases n with
  | zero => omega
  | succ m =>
      let f : ℕ → ℝ := fun k =>
        if hk : k < m + 1 then x (π.symm ⟨k, hk⟩) else 0
      rw [Fin.sum_univ_succ]
      have hzero : labelledPathSlack π x (0 : Fin (m + 1)) = f 0 := by
        simp [labelledPathSlack, f]
      rw [hzero]
      have htail : (∑ i : Fin m, labelledPathSlack π x i.succ) =
          ∑ i : Fin m, (f (i.val + 1) - f i.val) := by
        apply Finset.sum_congr rfl
        intro i _
        simp [labelledPathSlack, f]
        apply congrArg x
        apply congrArg π.symm
        apply Fin.ext
        rfl
      rw [htail]
      change f 0 + ∑ i : Fin m,
        (fun k : ℕ => f (k + 1) - f k) i.val = _
      rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => f (k + 1) - f k) m,
        Finset.sum_range_sub]
      simp [f, lastRank]

private theorem subperm_map_any {α β : Type*} {xs ys : List α}
    (f : α → β) (h : xs.Subperm ys) : (xs.map f).Subperm (ys.map f) := by
  obtain ⟨middle, hperm, hsub⟩ := h
  exact ⟨middle.map f, hperm.map f, hsub.map f⟩

private theorem exists_sum_remainder {ι : Type*} [AddCommMonoid ι]
    {xs ys : List ι} (h : xs.Subperm ys) :
    ∃ rest : List ι, ys.sum = xs.sum + rest.sum ∧ rest ⊆ ys := by
  rw [List.subperm_iff] at h
  obtain ⟨middle, hperm, hsub⟩ := h
  obtain ⟨rest, happ⟩ := hsub.exists_perm_append
  refine ⟨rest, ?_, ?_⟩
  · rw [← hperm.sum_eq, happ.sum_eq, List.sum_append]
  · intro a ha
    apply hperm.mem_iff.mp
    apply happ.mem_iff.mpr
    simp [ha]

private theorem sum_posSemidef (rows : List (Matrix (Item n) (Item n) ℝ))
    (hrows : ∀ M ∈ rows, M.PosSemidef) : rows.sum.PosSemidef := by
  induction rows with
  | nil => simpa using (Matrix.PosSemidef.zero :
      (0 : Matrix (Item n) (Item n) ℝ).PosSemidef)
  | cons M rows ih =>
      simp only [List.sum_cons]
      exact (hrows M (by simp)).add (ih fun N hN => hrows N (by simp [hN]))

section History

variable (h : History n) (π : Ranking n)
  (hπ : Compatible π h)
  (hunique : ∀ τ : Ranking n, Compatible τ h → τ = π)
  (hn : 0 < n)

include h π hπ hunique hn

private noncomputable def terminalObservation (i : Fin n) (hi : i.val ≠ 0) :
    Observation n := by
  let pred : Fin n := ⟨i.val - 1,
    (Nat.sub_lt (Nat.zero_lt_of_ne_zero hi) (by omega)).trans i.isLt⟩
  let u : Item n := π.symm pred
  let v : Item n := π.symm i
  have hadj : (π u).val + 1 = (π v).val := by
    simp [u, v, pred]
    omega
  exact Classical.choose
    (exists_adjacent_observation_of_unique_compatible h π hπ hunique hadj)

private theorem terminalObservation_spec (i : Fin n) (hi : i.val ≠ 0) :
    terminalObservation h π hπ hunique i hi ∈ h ∧
      lower (terminalObservation h π hπ hunique i hi) =
        π.symm ⟨i.val - 1,
          (Nat.sub_lt (Nat.zero_lt_of_ne_zero hi) (by omega)).trans i.isLt⟩ ∧
      upper (terminalObservation h π hπ hunique i hi) = π.symm i := by
  exact Classical.choose_spec
    (exists_adjacent_observation_of_unique_compatible h π hπ hunique (by
      simp
      omega))

/-- One marker for every selected grounded-path row. -/
private noncomputable def terminalSelector (i : Fin n) : Option (Observation n) :=
  if hi : i.val = 0 then none
  else some (terminalObservation h π hπ hunique i hi)

private theorem terminalSelector_injective :
    Function.Injective (terminalSelector h π hπ hunique) := by
  intro i j hij
  by_cases hi : i.val = 0
  · by_cases hj : j.val = 0
    · exact Fin.ext (hi.trans hj.symm)
    · simp [terminalSelector, hi, hj] at hij
  · by_cases hj : j.val = 0
    · simp [terminalSelector, hi, hj] at hij
    · have hobs : terminalObservation h π hπ hunique i hi =
          terminalObservation h π hπ hunique j hj := by
        simpa [terminalSelector, hi, hj] using hij
      have hspeci := terminalObservation_spec h π hπ hunique hn i hi
      have hspecj := terminalObservation_spec h π hπ hunique hn j hj
      have hlower : π.symm ⟨i.val - 1,
            (Nat.sub_lt (Nat.zero_lt_of_ne_zero hi) (by omega)).trans i.isLt⟩ =
          π.symm ⟨j.val - 1,
            (Nat.sub_lt (Nat.zero_lt_of_ne_zero hj) (by omega)).trans j.isLt⟩ := by
        rw [← hspeci.2.1, ← hspecj.2.1, hobs]
      have hval := congrArg (fun u : Item n => (π u).val) hlower
      simp only [Equiv.apply_symm_apply] at hval
      apply Fin.ext
      omega

omit h hπ hunique

private noncomputable def selectorTerm (x : Placement n) :
    Option (Observation n) → Matrix (Item n) (Item n) ℝ
  | none => (BarrierRow.lowerBox (π.symm ⟨0, hn⟩)).hessianTerm x
  | some o => (BarrierRow.ofObservation o).hessianTerm x

@[simp] private theorem selectorTerm_none (x : Placement n) :
    selectorTerm π hn x none =
      (BarrierRow.lowerBox (π.symm ⟨0, hn⟩)).hessianTerm x := rfl

@[simp] private theorem selectorTerm_some (x : Placement n) (o : Observation n) :
    selectorTerm π hn x (some o) =
      (BarrierRow.ofObservation o).hessianTerm x := rfl

include h hπ hunique

private theorem selectorTerm_eq_pathTerm (x : Placement n) (i : Fin n) :
    selectorTerm π hn x (terminalSelector h π hπ hunique i) =
      labelledPathTerm π x i := by
  classical
  by_cases hi : i.val = 0
  · have hieq : i = ⟨0, hn⟩ := Fin.ext hi
    subst i
    ext u v
    simp [terminalSelector, selectorTerm, BarrierRow.hessianTerm,
      BarrierRow.lowerBox, BarrierRow.slack, labelledPathTerm,
      labelledPathSlack, pathIncidence_apply_rank_zero]
  · have hspec := terminalObservation_spec h π hπ hunique hn i hi
    ext u v
    simp only [terminalSelector, hi, ↓reduceDIte, selectorTerm,
      BarrierRow.hessianTerm, BarrierRow.ofObservation_normal_eq,
      BarrierRow.slack_ofObservation_eq, labelledPathTerm]
    rw [hspec.2.1, hspec.2.2]
    rw [pathIncidence_apply_rank_positive π i hi u,
      pathIncidence_apply_rank_positive π i hi v]
    simp [labelledPathSlack, hi]

private theorem selectedTerms_sum_eq (x : Placement n) :
    ((List.ofFn (terminalSelector h π hπ hunique)).map
      (selectorTerm π hn x)).sum =
        labelledPathHessian π (labelledPathSlack π x) := by
  classical
  ext u v
  rw [List.map_ofFn, List.sum_ofFn, Matrix.sum_apply,
    labelledPathHessian_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun M : Matrix (Item n) (Item n) ℝ => M u v)
    (selectorTerm_eq_pathTerm h π hπ hunique hn x i)

private theorem selectedMarkers_subperm :
    List.Subperm (List.ofFn (terminalSelector h π hπ hunique))
      (none :: h.map some) := by
  apply (List.nodup_ofFn.mpr
    (terminalSelector_injective h π hπ hunique hn)).subperm
  intro marker hmarker
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hmarker
  by_cases hi : i.val = 0
  · simp [terminalSelector, hi]
  · have hmem := (terminalObservation_spec h π hπ hunique hn i hi).1
    simp [terminalSelector, hi, hmem]

private theorem ambientTerms_subperm (x : Placement n) :
    List.Subperm
      ((none :: h.map some).map (selectorTerm π hn x))
      ((barrierRows h).map
        fun row => row.hessianTerm x) := by
  let lowerTerms := (List.ofFn fun v : Item n => BarrierRow.lowerBox v).map
    fun row => row.hessianTerm x
  let upperTerms := (List.ofFn fun v : Item n => BarrierRow.upperBox v).map
    fun row => row.hessianTerm x
  let observationTerms := h.map
    (fun o => (BarrierRow.ofObservation o).hessianTerm x)
  have hlowerMem : (BarrierRow.lowerBox (π.symm ⟨0, hn⟩)).hessianTerm x ∈
      lowerTerms := by
    simp [lowerTerms]
  have hlower : List.Subperm
      [(BarrierRow.lowerBox (π.symm ⟨0, hn⟩)).hessianTerm x] lowerTerms := by
    apply List.Nodup.subperm (by simp)
    intro M hM
    simp at hM
    subst M
    exact hlowerMem
  have hobs : List.Subperm observationTerms (upperTerms ++ observationTerms) :=
    (List.sublist_append_right upperTerms observationTerms).subperm
  have happ := hlower.append hobs
  simpa [selectorTerm, lowerTerms, upperTerms, observationTerms, barrierRows,
    boxRows, List.map_append, List.map_map, List.append_assoc,
    Function.comp_def] using happ

/-- The full terminal Hessian is the selected grounded path plus a
positive-semidefinite sum of all unselected rows. -/
theorem exists_terminal_hessian_remainder (x : Placement n) :
    ∃ R : Matrix (Item n) (Item n) ℝ,
      R.PosSemidef ∧
      barrierHessian h x =
        labelledPathHessian π (labelledPathSlack π x) + R := by
  let selected := (List.ofFn (terminalSelector h π hπ hunique)).map
    (selectorTerm π hn x)
  let full := ((barrierRows h).map
    fun row => row.hessianTerm x)
  have hselectedAmbient := subperm_map_any (selectorTerm π hn x)
    (selectedMarkers_subperm h π hπ hunique hn)
  have hsub : selected.Subperm full := hselectedAmbient.trans
    (ambientTerms_subperm h π hπ hunique hn x)
  obtain ⟨rest, hsum, hrest⟩ := exists_sum_remainder hsub
  refine ⟨rest.sum, ?_, ?_⟩
  · apply sum_posSemidef rest
    intro M hM
    have hMfull : M ∈ full := hrest hM
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hMfull
    exact row.hessianTerm_posSemidef x
  · rw [barrierHessian, ← selectedTerms_sum_eq h π hπ hunique hn x]
    exact hsum

theorem terminal_path_slack_pos (x : Placement n)
    (hx : InHistoryPolytope h x) :
    ∀ i, 0 < labelledPathSlack π x i := by
  intro i
  by_cases hi : i.val = 0
  · simp [labelledPathSlack, hi, (hx.1 (π.symm i)).1]
  · have hspec := terminalObservation_spec h π hπ hunique hn i hi
    have hrealizes := (List.forall_iff_forall_mem.1 hx.2)
      _ hspec.1
    have hslack := (BarrierRow.realizesPlacement_iff_slack_pos _ x).1 hrealizes
    rw [BarrierRow.slack_ofObservation_eq, hspec.2.1, hspec.2.2] at hslack
    simpa [labelledPathSlack, hi] using hslack

/-- Determinant dominance of the full terminal Hessian over the selected
grounded path. -/
theorem terminal_path_det_le (x : Placement n)
    (hx : InHistoryPolytope h x) :
    (labelledPathHessian π (labelledPathSlack π x)).det ≤
      (barrierHessian h x).det := by
  obtain ⟨R, hR, hEq⟩ :=
    exists_terminal_hessian_remainder h π hπ hunique hn x
  rw [hEq]
  exact det_le_det_add_of_posDef_of_posSemidef
    (labelledPathHessian_posDef π _
      (terminal_path_slack_pos h π hπ hunique hn x hx)) hR

theorem terminal_hessian_det_lower (x : Placement n)
    (hx : InHistoryPolytope h x) :
    (n : ℝ) ^ (2 * n) ≤
      (barrierHessian h x).det := by
  have hs := terminal_path_slack_pos h π hπ hunique hn x hx
  have hsum : ∑ i, labelledPathSlack π x i ≤ 1 := by
    rw [sum_labelledPathSlack hn π x]
    exact (hx.1 _).2.le
  calc
    (n : ℝ) ^ (2 * n) ≤
        ∏ i, 1 / labelledPathSlack π x i ^ 2 :=
      pow_two_mul_card_le_prod_inverse_sq hn _ hs hsum
    _ = (labelledPathHessian π (labelledPathSlack π x)).det := by
      rw [labelledPathHessian_det]
    _ ≤ (barrierHessian h x).det :=
      terminal_path_det_le h π hπ hunique hn x hx

/-- Every feasible placement at a completed correct run has terminal
volumetric value at least `n log₂ n`. -/
theorem terminal_volumetricValue₂_lower (x : Placement n)
    (hx : InHistoryPolytope h x) :
    nLog2n n ≤ volumetricValue₂ h x := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hdet := terminal_hessian_det_lower h π hπ hunique hn x hx
  have hpowpos : 0 < (n : ℝ) ^ (2 * n) := pow_pos hnreal _
  have hdetpos : 0 < (barrierHessian h x).det :=
    (barrierHessian_posDef hx).det_pos
  have hlog : Real.log ((n : ℝ) ^ (2 * n)) ≤
      Real.log (barrierHessian h x).det :=
    Real.strictMonoOn_log.monotoneOn hpowpos hdetpos hdet
  rw [Real.log_pow] at hlog
  have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by norm_num
  rw [hcast] at hlog
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [nLog2n, volumetricValue₂, volumetricValue]
  rw [show (n : ℝ) * (Real.log n / Real.log 2) =
      ((n : ℝ) * Real.log n) / Real.log 2 by ring]
  apply (div_le_div_iff_of_pos_right hlogtwo).2
  nlinarith

end History

end StrengthenedCurvature
end SortingAdversary
