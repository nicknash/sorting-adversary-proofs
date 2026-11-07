import SortingAdversary.Optimal.StageCompileWork
import SortingAdversary.Optimal.HubEnumerationWork

/-!
# Counted uniform initialization, including rejected stages

This is the actual capped scan and table materialization, preceded by a
counted binary logarithm and followed by measured table compilation. Its
decision equals the verified uniform selector exactly. Administrative field
searches and rational normalization are included in addition to the original
arithmetic-evaluator counters.
-/

namespace SortingAdversary.Optimal.UniformSelectionWork

open PrimitiveWork UniformStage StageParameters

structure Selected (n : ℕ) where
  decision : Decision (Parameters.logCap n)
  actual : decision = (UniformStage.choose n).decision
  peak : ℕ
  peak_actual : peak = max (n + 1) (UniformStage.choose n).arithmeticPeak

theorem admitted_decision (n j : ℕ) (hj : 0 < j) (hjcap : j ≤ Parameters.logCap n)
    (table : StageRecipe.Table) (hv : ∀ f, table.get f = StageParameters.value j f)
    (hfit : StageRecipe.all.need j ≤ Parameters.logCap n)
    (hjexact : j = UniformStage.selectedStage n)
    (ht : table = StageRecipe.materialize (Parameters.logCap n) j fields) :
    Decision.accepted j hj (compileTable (Parameters.logCap n) j hj hjcap table hv hfit) =
      (UniformStage.choose n).decision := by
  subst j table
  have hpos : 0 < (CappedStageScan.select StageRecipe.all n).stage := hj
  simp only [UniformStage.choose, dif_pos hpos]
  rfl

def choose (n : ℕ) : Result (Selected n) := by
  let cap := HubEnumerationWork.logTwo (n + 1)
  have hc : cap.value = Parameters.logCap n := HubEnumerationWork.logTwo_value (n + 1)
  let scan := CappedStageScan.scan StageRecipe.all cap.value 0 cap.value
  have hs : scan = CappedStageScan.select StageRecipe.all n := by
    simp only [scan, hc, CappedStageScan.select]
  if hj : 0 < scan.stage then
    let table := StageRecipe.materialize cap.value scan.stage fields
    have hjcap : scan.stage ≤ Parameters.logCap n := by rw [hs]; exact selectedStage_le n
    have hfit : StageRecipe.all.need scan.stage ≤ Parameters.logCap n := by
      rw [hs] at hj ⊢
      exact selectedStage_fits n hj
    have hv : ∀ f, table.get f = StageParameters.value scan.stage f := by
      intro f
      simpa only [table, hc] using StageRecipe.materialize_correct (Parameters.logCap n) scan.stage hfit f
    let compiled := StageCompileWork.compile (Parameters.logCap n) scan.stage hj hjcap table hv hfit
    let decision := Decision.accepted scan.stage hj compiled.value.value
    have hjs : 0 < (CappedStageScan.select StageRecipe.all n).stage := by simpa only [hs] using hj
    have hd : decision = (UniformStage.choose n).decision := by
      simp only [decision, compiled.value.actual]
      apply admitted_decision n scan.stage hj hjcap table hv hfit
      · exact congrArg CappedStageScan.Result.stage hs
      · simp only [table, hc]
    have hp : max (n + 1) (max scan.peak table.peak) =
        max (n + 1) (UniformStage.choose n).arithmeticPeak := by
      simp only [table, hc, hs, UniformStage.choose, dif_pos hjs]
    exact ⟨⟨decision, hd, max (n + 1) (max scan.peak table.peak), hp⟩,
      cap.work + scan.work + table.work + compiled.work + 6⟩
  else
    have hjs : ¬0 < (CappedStageScan.select StageRecipe.all n).stage := by simpa only [hs] using hj
    have hd : Decision.fallback = (UniformStage.choose n).decision := by
      simp only [UniformStage.choose, dif_neg hjs]
    have hp : max (n + 1) scan.peak = max (n + 1) (UniformStage.choose n).arithmeticPeak := by
      simp only [hs, UniformStage.choose, dif_neg hjs]
    exact ⟨⟨.fallback, hd, max (n + 1) scan.peak, hp⟩, cap.work + scan.work + 3⟩

theorem choose_actual (n : ℕ) : (choose n).value.decision = (UniformStage.choose n).decision :=
  (choose n).value.actual

def workBound (n : ℕ) : ℕ := UniformStage.arithmeticBudget (Parameters.logCap n) + 6 * n + 600

theorem choose_work (n : ℕ) : (choose n).work ≤ workBound n := by
  let cap := HubEnumerationWork.logTwo (n + 1)
  have hc : cap.value = Parameters.logCap n := HubEnumerationWork.logTwo_value (n + 1)
  let scan := CappedStageScan.scan StageRecipe.all cap.value 0 cap.value
  have hs : scan = CappedStageScan.select StageRecipe.all n := by
    simp only [scan, hc, CappedStageScan.select]
  have hl := HubEnumerationWork.logTwo_work_le (n + 1)
  have hcap := Parameters.logCap_le_input n
  have hreference := UniformStage.choose_work n
  unfold choose
  dsimp only
  split
  · rename_i hj
    change 0 < scan.stage at hj
    let table := StageRecipe.materialize cap.value scan.stage fields
    have hjcap : scan.stage ≤ Parameters.logCap n := by rw [hs]; exact selectedStage_le n
    have hfit : StageRecipe.all.need scan.stage ≤ Parameters.logCap n := by
      rw [hs] at hj ⊢
      exact selectedStage_fits n hj
    have hv : ∀ f, table.get f = StageParameters.value scan.stage f := by
      intro f
      simpa only [table, hc] using StageRecipe.materialize_correct (Parameters.logCap n) scan.stage hfit f
    have hcompiled := StageCompileWork.compile_work (Parameters.logCap n) scan.stage hj hjcap table hv hfit
    have hlen : table.values.length = 22 := by
      simp only [table, StageRecipe.materialize_values, List.length_map]
      rfl
    rw [hlen] at hcompiled
    have hjs : 0 < (CappedStageScan.select StageRecipe.all n).stage := by simpa only [hs] using hj
    simp only [UniformStage.choose, dif_pos hjs] at hreference
    have hsum : scan.work + table.work ≤ UniformStage.arithmeticBudget (Parameters.logCap n) := by
      simpa only [table, hc, hs] using hreference
    change cap.work + scan.work + table.work +
      (StageCompileWork.compile (Parameters.logCap n) scan.stage hj hjcap table hv hfit).work + 6 ≤ _
    change cap.work ≤ _ at hl
    unfold workBound
    omega
  · rename_i hj
    change ¬0 < scan.stage at hj
    have hjs : ¬0 < (CappedStageScan.select StageRecipe.all n).stage := by simpa only [hs] using hj
    simp only [UniformStage.choose, dif_neg hjs] at hreference
    have hscan : scan.work ≤ UniformStage.arithmeticBudget (Parameters.logCap n) := by
      simpa only [hs] using hreference
    change cap.work + scan.work + 3 ≤ _
    change cap.work ≤ _ at hl
    unfold workBound
    omega

def polynomial (n : ℕ) : ℕ :=
  (n + 22) * (UniformStage.recipeSize * (5 * (n + 1) + 2) + 1) + 6 * n + 600

theorem work_polynomial (n : ℕ) : (choose n).work ≤ polynomial n := by
  apply (choose_work n).trans
  unfold workBound polynomial UniformStage.arithmeticBudget
  have hlen : fields.length = 22 := rfl
  rw [hlen]
  have hcap := Parameters.logCap_le_input n
  gcongr

theorem peak_polynomial (n : ℕ) : (choose n).value.peak ≤ (n + 130) ^ 2 := by
  rw [(choose n).value.peak_actual]
  apply max_le
  · nlinarith
  · apply (UniformStage.choose_peak n).trans
    have hcap := Parameters.logCap_le_input n
    gcongr
    omega

end SortingAdversary.Optimal.UniformSelectionWork
