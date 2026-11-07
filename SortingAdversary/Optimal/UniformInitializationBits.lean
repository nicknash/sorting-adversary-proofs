import SortingAdversary.Optimal.UniformMachineWork
import SortingAdversary.Optimal.UniformBitResources

/-!
# Binary operand certificates for the concrete uniform initializer

The certificate below refers to the executed logarithm, capped evaluations
(including rejected stages), materialized field searches, actual accuracy
normalization, measured clock and initial finite state. It complements the
admitted-stage power certificates in `UniformBitResources`. Instrumentation
work counters remain ghost measurements, as in `PrimitiveWork`.
-/

namespace SortingAdversary.Optimal.UniformInitializationBits

open PrimitiveWork UniformStage StageParameters UniformBitResources

variable {n : ℕ}

theorem initialization_peak_le_bits (n : ℕ) : (n + 130) ^ 2 ≤ bits n := by
  have h : (n + 130) ^ 2 ≤ 16900 * (n + 1) ^ 2 := by
    calc
      (n + 130) ^ 2 ≤ (130 * (n + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 16900 * (n + 1) ^ 2 := by ring
  exact h.trans (small_polynomial_le n 16900 2 (by decide) (by decide))

theorem input_bits {value : ℕ} (h : value ≤ n + 1) : Nat.size value ≤ bits n := by
  apply (size_of_le h).trans
  have hsmall : n + 1 ≤ (n + 130) ^ 2 := by nlinarith
  exact hsmall.trans (initialization_peak_le_bits n)

theorem literal_bits {value : ℕ} (h : value ≤ 130) : Nat.size value ≤ bits n := by
  apply (size_of_le h).trans
  have hsmall : 130 ≤ (n + 130) ^ 2 := by
    have hp := Nat.pow_le_pow_left (show 130 ≤ n + 130 by omega) 2
    norm_num at hp
    omega
  exact hsmall.trans (initialization_peak_le_bits n)

theorem logarithm_bits (m : ℕ) (hm : m ≤ n + 1) :
    Nat.size (HubEnumerationWork.logTwo m).value ≤ bits n := by
  rw [HubEnumerationWork.logTwo_value]
  exact input_bits ((Nat.log_le_self 2 m).trans hm)

theorem selector_peak_bits (n : ℕ) :
    Nat.size (UniformSelectionWork.choose n).value.peak ≤ bits n :=
  (size_of_le (UniformSelectionWork.peak_polynomial n)).trans (initialization_peak_le_bits n)

theorem attempted_recipe_bits (j : ℕ) (hj : 0 < j) (hcap : j ≤ Parameters.logCap n) :
    Nat.size (StageRecipe.all.eval (Parameters.logCap n) j).peak ≤ bits n := by
  have h := StageRecipe.all.eval_peak (Parameters.logCap n) j 128
    (hj.trans_le hcap) hcap StageRecipe.all_literalMax
  apply (size_of_le h).trans
  apply le_trans _ (initialization_peak_le_bits n)
  have hc := Parameters.logCap_le_input n
  exact Nat.pow_le_pow_left (by omega) 2

theorem table_peak_bits (j : ℕ) (hj : 0 < j) (hcap : j ≤ Parameters.logCap n) (fs : List Field) :
    Nat.size (StageRecipe.materialize (Parameters.logCap n) j fs).peak ≤ bits n := by
  have h := StageRecipe.materialize_peak (Parameters.logCap n) j fs (hj.trans_le hcap) hcap
  apply (size_of_le h).trans
  apply le_trans _ (initialization_peak_le_bits n)
  have hc := Parameters.logCap_le_input n
  exact Nat.pow_le_pow_left (by omega) 2

theorem compiled_field_le (j : ℕ) (table : StageRecipe.Table)
    (hv : ∀ f, table.get f = StageParameters.value j f)
    (hfit : StageRecipe.all.need j ≤ Parameters.logCap n) (f : Field) :
    (StageRadiusWork.fieldGet f table.values).value ≤ Parameters.logCap n := by
  rw [StageRadiusWork.fieldGet_value]
  change table.get f ≤ Parameters.logCap n
  rw [hv f, ← StageRecipe.field_value]
  exact ((StageRecipe.field f).value_le_need j).trans ((StageRecipe.field_need_le j f).trans hfit)

theorem compiled_field_bits (j : ℕ) (table : StageRecipe.Table)
    (hv : ∀ f, table.get f = StageParameters.value j f)
    (hfit : StageRecipe.all.need j ≤ Parameters.logCap n) (f : Field) :
    Nat.size (StageRadiusWork.fieldGet f table.values).value ≤ bits n :=
  capped_scalar_bits (compiled_field_le j table hv hfit f)

theorem accuracy_den_pos (j : ℕ) (hj : 0 < j) (table : StageRecipe.Table)
    (hv : ∀ f, table.get f = StageParameters.value j f) :
    0 < (StageRadiusWork.fieldGet .accuracyDen table.values).value := by
  rw [StageRadiusWork.fieldGet_value]
  change 0 < table.get .accuracyDen
  rw [hv .accuracyDen]
  exact StageParameters.accuracyDen_pos hj

/-- These are the actual gcd/quotient normalization and reduced fields
used in the measured accepted compiler, not a rational-value specification. -/
theorem compiler_accuracy_bits (j : ℕ) (hj : 0 < j) (hcap : j ≤ Parameters.logCap n)
    (table : StageRecipe.Table) (hv : ∀ f, table.get f = StageParameters.value j f)
    (hfit : StageRecipe.all.need j ≤ Parameters.logCap n) :
    let denominator := (StageRadiusWork.fieldGet .accuracyDen table.values).value
    let compiled := (StageCompileWork.compile (Parameters.logCap n) j hj hcap table hv hfit).value.value
    Nat.size denominator ≤ bits n ∧
      Nat.size compiled.runtime.ε.num.natAbs ≤ bits n ∧
      Nat.size compiled.runtime.ε.den ≤ bits n ∧
      (RationalBitWork.ratio 1 denominator).bitWork ≤
        RationalBitWork.Model.charge (RationalBitWork.ratio 1 denominator).result.work (bits n) := by
  let denominator := (StageRadiusWork.fieldGet .accuracyDen table.values).value
  have hd : Nat.size denominator ≤ bits n := compiled_field_bits j table hv hfit .accuracyDen
  have h1 : Nat.size 1 ≤ bits n := literal_bits (by decide)
  have hp : denominator ≠ 0 := Nat.ne_of_gt (accuracy_den_pos j hj table hv)
  have hn := (RationalWork.ratio_num_size 1 denominator).trans h1
  have hden := (RationalWork.ratio_den_size_of_ne_zero 1 denominator hp).trans hd
  have hcost := RationalBitWork.ratio_bitWork_le 1 denominator (bits n) h1 hd
  exact ⟨hd, hn, hden, hcost⟩

theorem clock_operand_bits (n : ℕ) :
    Nat.size (2 * n) ≤ bits n ∧
      Nat.size ((HubEnumerationWork.logTwo (n + 1)).value + 1) ≤ bits n ∧
      Nat.size (UniformMachineWork.clock n).value ≤ bits n := by
  refine ⟨?_, ?_, ?_⟩
  · have h : 2 * n ≤ 2 * (n + 1) := by omega
    exact (size_of_le h).trans (by simpa using small_polynomial_le n 2 1 (by decide) (by decide))
  · rw [HubEnumerationWork.logTwo_value]
    have h := Parameters.logCap_le_input n
    exact input_bits (by change Parameters.logCap n + 1 ≤ n + 1; omega)
  · rw [UniformMachineWork.clock_value]
    exact (size_le_value _).trans (cutoff_le_bits n)

theorem initial_label_bits (n : ℕ) (v : Fin n) : Nat.size v.val ≤ bits n :=
  input_bits (by omega)

theorem initial_state_bits (p : RecursiveController.Parameters) (N : ℕ) :
    Nat.size (UniformInitialWork.active p N).value.state.counter ≤ bits (N + 2) ∧
      Nat.size (UniformInitialWork.active p N).value.state.tree.pool.palette ≤ bits (N + 2) ∧
      (∀ v : Fin (N + 2),
        Nat.size (((UniformInitialWork.active p N).value.access.root.lower v).value.val) ≤ bits (N + 2) ∧
        Nat.size (((UniformInitialWork.active p N).value.access.root.upper v).value.val) ≤ bits (N + 2)) ∧
      (∀ c : Fin (N + 1 + 1),
        Nat.size (((UniformInitialWork.initialAccess N).order c).value.val) ≤ bits (N + 2) ∧
        Nat.size (((UniformInitialWork.initialAccess N).inverse c).value.val) ≤ bits (N + 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Nat.size 1 ≤ _
    exact literal_bits (by decide)
  · change Nat.size (N + 1) ≤ _
    exact input_bits (by omega)
  · intro v
    change Nat.size 0 ≤ _ ∧ Nat.size (N + 1) ≤ _
    exact ⟨literal_bits (by decide), input_bits (by omega)⟩
  · intro c
    change Nat.size c.val ≤ _ ∧ Nat.size c.val ≤ _
    exact ⟨input_bits (by omega), input_bits (by omega)⟩

/-- Concrete operand coverage for initialization. The selected runtime's
internal radius powers are supplied by the separate admitted-stage scalar
certificates; both final prepared radii are also recorded here. -/
structure InitializationOperands (n : ℕ) : Prop where
  inputs : ∀ value, value ≤ n + 1 → Nat.size value ≤ bits n
  literals : ∀ value, value ≤ 130 → Nat.size value ≤ bits n
  logarithms : ∀ m, m ≤ n + 1 → Nat.size (HubEnumerationWork.logTwo m).value ≤ bits n
  selector : Nat.size (UniformSelectionWork.choose n).value.peak ≤ bits n
  attempts : ∀ j, 0 < j → j ≤ Parameters.logCap n →
    Nat.size (StageRecipe.all.eval (Parameters.logCap n) j).peak ≤ bits n
  tables : ∀ j, 0 < j → j ≤ Parameters.logCap n → ∀ fs,
    Nat.size (StageRecipe.materialize (Parameters.logCap n) j fs).peak ≤ bits n
  fields : ∀ j (table : StageRecipe.Table), (∀ f, table.get f = StageParameters.value j f) →
    StageRecipe.all.need j ≤ Parameters.logCap n → ∀ f,
      Nat.size (StageRadiusWork.fieldGet f table.values).value ≤ bits n
  accuracy : ∀ j (hj : 0 < j) (hcap : j ≤ Parameters.logCap n) (table : StageRecipe.Table)
    (hv : ∀ f, table.get f = StageParameters.value j f)
    (hfit : StageRecipe.all.need j ≤ Parameters.logCap n),
    let denominator := (StageRadiusWork.fieldGet .accuracyDen table.values).value
    let compiled := (StageCompileWork.compile (Parameters.logCap n) j hj hcap table hv hfit).value.value
    Nat.size denominator ≤ bits n ∧ Nat.size compiled.runtime.ε.num.natAbs ≤ bits n ∧
      Nat.size compiled.runtime.ε.den ≤ bits n ∧
      (RationalBitWork.ratio 1 denominator).bitWork ≤
        RationalBitWork.Model.charge (RationalBitWork.ratio 1 denominator).result.work (bits n)
  clock : Nat.size (2 * n) ≤ bits n ∧
    Nat.size ((HubEnumerationWork.logTwo (n + 1)).value + 1) ≤ bits n ∧
    Nat.size (UniformMachineWork.clock n).value ≤ bits n
  labels : ∀ v ∈ (UniformInitialWork.members n).value, Nat.size v.val ≤ bits n
  initial : ∀ N, N + 2 = n → ∀ p,
    Nat.size (UniformInitialWork.active p N).value.state.counter ≤ bits n ∧
      Nat.size (UniformInitialWork.active p N).value.state.tree.pool.palette ≤ bits n ∧
      (∀ v : Fin (N + 2),
        Nat.size (((UniformInitialWork.active p N).value.access.root.lower v).value.val) ≤ bits n ∧
        Nat.size (((UniformInitialWork.active p N).value.access.root.upper v).value.val) ≤ bits n) ∧
      (∀ c : Fin (N + 1 + 1),
        Nat.size (((UniformInitialWork.initialAccess N).order c).value.val) ≤ bits n ∧
        Nat.size (((UniformInitialWork.initialAccess N).inverse c).value.val) ≤ bits n)
  radii : ∀ j (a : Accepted (Parameters.logCap n) j),
    Nat.size (UniformPreparedWork.prepare a).value.repair.radius ≤ bits n ∧
      Nat.size (UniformPreparedWork.prepare a).value.comparisonRadius ≤ bits n

theorem initialization_operands (n : ℕ) : InitializationOperands n where
  inputs _ h := input_bits h
  literals _ h := literal_bits h
  logarithms := logarithm_bits
  selector := selector_peak_bits n
  attempts := attempted_recipe_bits
  tables := table_peak_bits
  fields := compiled_field_bits
  accuracy := compiler_accuracy_bits
  clock := clock_operand_bits n
  labels v _ := initial_label_bits n v
  initial N hn p := by subst n; exact initial_state_bits p N
  radii _ := prepared_radius_bits

end SortingAdversary.Optimal.UniformInitializationBits
