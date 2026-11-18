import SortingAdversary.Continuous.UniformAdversary

/-!
# A logarithmic budget for the rounded enclosure

Outward rounding calls the enclosure at half the target width. The integer
recipe below accounts for this smaller width *before* the stage is chosen.
It can also cap a fixed arithmetic expression for other stage-dependent work.
The scan stops at its first failed trial and includes the cost of that trial.

The comparison reduction only uses the prefix inequality before the horizon.
It applies to different deterministic choices at the certificate and repair
steps. The last theorem instantiates it for the existing continuous controller.
-/

namespace SortingAdversary.Continuous.PolylogSchedule

open Optimal Optimal.CappedArithmetic UniformStages ArbitraryLabels
open Filter
open scoped Topology

/-- Halving the target doubles its denominator. The failure probability is
unchanged. These expressions bound the entire enumeration at that accuracy. -/
def roundedSweeps : Expr :=
  .mul (.mul (.lit 2) Recipe.failure) (.pow (.mul (.lit 2) Recipe.accuracy) Recipe.moment)

def roundedRetained : Expr :=
  .mul (.lit 2) (.pow (.add Recipe.degree (.lit 1))
    (.add (.mul Recipe.height roundedSweeps) (.lit 2)))

def roundedEnumeration : Expr :=
  .pow Recipe.alphabet (.mul roundedRetained roundedSweeps)

theorem roundedEnumeration_value (j : ℕ) :
    roundedEnumeration.value j = ParameterBounds.enumerationEnvelope (degree j)
      (pathHeight (degree j)) (failureDen (degree j)) (2 * accuracyDen (degree j)) := rfl

/-- Stage zero retains the repository's inactive parameter 32. Positive
stages have degree at least 64. The extra expression is evaluated with the
same cap as the rounded enclosure; its full integer value is never needed
to reject a stage. -/
def shortPrecision : Expr := .add (.mul (.lit 4) Recipe.accuracy) roundedEnumeration

def recipe (extra : Expr) : Expr := .maximum (.maximum shortPrecision Recipe.budget) extra

def stage (extra : Expr) (n : ℕ) : ℕ := CappedStageScan.stage (recipe extra) n

def parameter (extra : Expr) (n : ℕ) : ℕ := degree (stage extra n)

theorem parameter_tendsto (extra : Expr) : Tendsto (parameter extra) atTop atTop := by
  apply Filter.tendsto_atTop_mono (fun n => ?_) (CappedStageScan.stage_tendsto (recipe extra))
  exact (Nat.le_add_right _ 5).trans Nat.lt_two_pow_self.le

theorem active_stage {extra : Expr} {n : ℕ} (hk : 64 ≤ parameter extra n) :
    0 < stage extra n := by
  by_contra! hz
  have he : stage extra n = 0 := by omega
  norm_num [parameter, he, degree] at hk

theorem admitted_costs {extra : Expr} {n : ℕ} (hk : 64 ≤ parameter extra n) :
    roundedEnumeration.value (stage extra n) ≤ Parameters.logCap n ∧
      extra.value (stage extra n) ≤ Parameters.logCap n := by
  have h := CappedStageScan.stage_need (recipe extra) n (active_stage hk)
  change max (max (shortPrecision.need (stage extra n)) (Recipe.budget.need (stage extra n)))
    (extra.need (stage extra n)) ≤ _ at h
  have hP := (shortPrecision.value_le_need _).trans (max_le_iff.mp (max_le_iff.mp h).1).1
  change 4 * accuracyDen (parameter extra n) + roundedEnumeration.value (stage extra n) ≤ _ at hP
  exact ⟨(Nat.le_add_left _ _).trans hP, (extra.value_le_need _).trans (max_le_iff.mp h).2⟩

/-- Number of digit words in the exact enclosure before widening by the
outward grid error. The width argument is exactly half the certificate's
target accuracy, expressed here by its reciprocal denominator. -/
theorem rounded_enumeration_le {extra : Expr} {n : ℕ} (hk : 64 ≤ parameter extra n) :
    let k := parameter extra n
    let D := 2 * accuracyDen k
    let A := failureDen k
    EnclosureParameters.enumerationBound k (pathHeight k) (1 / D) (1 / A)
      (one_div_pos.mpr (by
        exact_mod_cast (Nat.mul_pos (by decide : 0 < 2) (accuracyDen_pos (show 0 < k by omega)))))
      (one_div_pos.mpr (by exact_mod_cast (failureDen_pos (show 0 < k by omega))))
      ≤ Parameters.logCap n := by
  have hkp : 0 < parameter extra n := by omega
  exact (ParameterBounds.enumerationBound_le_envelope _ _ _ _
    (failureDen_pos hkp) (Nat.mul_pos (by decide) (accuracyDen_pos hkp)) _ _).trans
      ((roundedEnumeration_value (stage extra n)) ▸ (admitted_costs hk).1)

/-- A fixed number of nested logarithmic searches can multiply any
stage-local cost dominated by the extra expression. -/
theorem query_cost {extra : Expr} {n localWork c : ℕ} (hk : 64 ≤ parameter extra n)
    (hw : localWork ≤ extra.value (stage extra n) * (Parameters.logCap n + 1) ^ c) :
    localWork ≤ (Parameters.logCap n + 1) ^ (c + 1) := by
  rw [pow_succ _ c, Nat.mul_comm ((Parameters.logCap n + 1) ^ c)]
  exact hw.trans (Nat.mul_le_mul_right _ ((admitted_costs hk).2.trans (Nat.le_succ _)))

private theorem square_log_bound (l : ℕ) : l ^ 2 ≤ 4 * 2 ^ l := by
  induction l with
  | zero => decide
  | succ l ih =>
    by_cases hl : l < 3
    · interval_cases l <;> decide
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ l by omega)
    rw [pow_succ 2 (3 + a)]
    nlinarith [Nat.zero_le (a ^ 2)]

/-- Linear initialization allowance for the complete scan, including all
rejected trials. The cap is the repository's floor(log₂(n+1)). -/
theorem selection_work_linear (extra : Expr) (n : ℕ) :
    (CappedStageScan.select (recipe extra) n).work ≤
      (27 * (recipe extra).nodes + 1) * (n + 1) := by
  let l := Parameters.logCap n
  let m := (recipe extra).nodes
  have hl : l ≤ n + 1 := (Parameters.logCap_le_input n).trans (Nat.le_succ _)
  have hp : 2 ^ l ≤ n + 1 := Nat.pow_log_le_self 2 (Nat.succ_ne_zero n)
  have hs := (square_log_bound l).trans (Nat.mul_le_mul_left 4 hp)
  apply (CappedStageScan.selected_work (recipe extra) n).trans
  change l * (m * (5 * (l + 1) + 2) + 1) ≤ (27 * m + 1) * (n + 1)
  nlinarith [Nat.mul_le_mul_left m hs, Nat.mul_le_mul_left m hl]

/-- Even a rejected trial uses only logarithmically many bits per operand.
The largest literal is a constant of the fixed recipe. -/
theorem selection_peak_bits (extra : Expr) (n : ℕ) :
    (CappedStageScan.select (recipe extra) n).peak.size ≤
      (Parameters.logCap n + (recipe extra).literalMax + 1) * 2 := by
  let b := Parameters.logCap n + (recipe extra).literalMax + 1
  apply Nat.size_le.mpr
  calc
    (CappedStageScan.select (recipe extra) n).peak ≤ b ^ 2 :=
      CappedStageScan.selected_peak _ _ _ le_rfl
    _ < (2 ^ b) ^ 2 := Nat.pow_lt_pow_left Nat.lt_two_pow_self (by decide)
    _ = 2 ^ (b * 2) := (pow_mul _ _ _).symm

/-- The outward grid and the affine updates fit the common short precision.
Here S is the number of digits per update in bits, so (2^S)^steps is the
number of digit words enumerated for the schedule. -/
theorem precision_le {extra : Expr} {n S steps : ℕ} (hk : 64 ≤ parameter extra n)
    (hwords : (2 ^ S) ^ steps ≤ roundedEnumeration.value (stage extra n)) :
    Nat.clog 2 ⌈(4 : ℚ) / (1 / accuracyDen (parameter extra n))⌉₊ + steps * S ≤
      Parameters.logCap n := by
  let D := accuracyDen (parameter extra n)
  have hq : (4 : ℚ) / (1 / D) = ((4 * D : ℕ) : ℚ) := by
    push_cast
    simp [div_eq_mul_inv]
  have hgrid : Nat.clog 2 ⌈(4 : ℚ) / (1 / D)⌉₊ ≤ 4 * D := by
    rw [hq, Nat.ceil_natCast]
    exact Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hlen : steps * S ≤ (2 ^ S) ^ steps := by
    rw [← pow_mul, Nat.mul_comm steps S]
    exact Nat.lt_two_pow_self.le
  have h := CappedStageScan.stage_need (recipe extra) n (active_stage hk)
  change max (max (shortPrecision.need (stage extra n)) _) _ ≤ _ at h
  exact (Nat.add_le_add hgrid (hlen.trans hwords)).trans
    ((shortPrecision.value_le_need _).trans (max_le_iff.mp (max_le_iff.mp h).1).1)

theorem height_le {extra : Expr} {n : ℕ} (hk : 64 ≤ parameter extra n) :
    pathHeight (parameter extra n) ≤ Parameters.logCap n := by
  have h := CappedStageScan.stage_need (recipe extra) n (active_stage hk)
  change max (max _ (Recipe.budget.need (stage extra n))) _ ≤ _ at h
  exact (admitted_scalar_bounds _ _ (max_le_iff.mp (max_le_iff.mp h).1).2).2.1

theorem horizon_le (n : ℕ) :
    Controller.horizon n ≤ n * (Parameters.logCap n + 1) := by
  have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n + 1)
  exact Nat.mul_le_mul_left n (Nat.clog_le_of_le_pow (Nat.le_succ n |>.trans h.le))

/-- Precision capacity through the finite horizon. A refinement can add two
fractional bits and a comparison can refine at most H+2 labels. -/
def capacity (A H n : ℕ) : ℕ := A + 2 * (Controller.horizon n + 1) * (H + 2) + 8

theorem capacity_bits {extra : Expr} {n A : ℕ} (hk : 64 ≤ parameter extra n)
    (hA : A ≤ Parameters.logCap n) :
    (capacity A (pathHeight (parameter extra n)) n).size ≤
      5 + (Parameters.logCap n + 1) * 3 := by
  let H := pathHeight (parameter extra n)
  have hAn := hA.trans (Parameters.logCap_le_input n)
  have hHn : H ≤ n := (height_le hk).trans (Parameters.logCap_le_input n)
  have hQ : Controller.horizon n ≤ n ^ 2 := by
    simpa only [Controller.horizon, pow_two] using
      Nat.mul_le_mul_left n (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := n)).le)
  have hD : capacity A H n ≤ 16 * (n + 1) ^ 3 := by
    have hprod := Nat.mul_le_mul (Nat.add_le_add_right hQ 1) (Nat.add_le_add_right hHn 2)
    unfold capacity
    nlinarith [Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]
  have hp : n + 1 ≤ 2 ^ (Parameters.logCap n + 1) :=
    (Nat.lt_pow_succ_log_self (by decide) (n + 1)).le
  apply Nat.size_le.mpr
  calc
    capacity A H n ≤ 16 * ((2 ^ (Parameters.logCap n + 1)) ^ 3) :=
      hD.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hp 3))
    _ < 2 ^ (5 + (Parameters.logCap n + 1) * 3) := by
      rw [pow_add 2 5, pow_mul 2 (Parameters.logCap n + 1)]
      have hpos : 0 < (2 ^ (Parameters.logCap n + 1)) ^ 3 := by positivity
      omega

/-- With at most one allocation budget per pre-horizon call, the persistent
store has n·polylog(n) words, even for arbitrarily long continuations. -/
theorem space_through_horizon {n e q words : ℕ} (hq : q ≤ Controller.horizon n)
    (hw : words ≤ n + 1 + q * (Parameters.logCap n + 1) ^ e) :
    words ≤ 2 * (n + 1) * (Parameters.logCap n + 1) ^ (e + 1) := by
  let b := Parameters.logCap n + 1
  have hq' : q ≤ (n + 1) * b :=
    (hq.trans (horizon_le n)).trans (Nat.mul_le_mul_right _ (Nat.le_succ n))
  have hmul := Nat.mul_le_mul_right (b ^ e) hq'
  have hone : 1 ≤ b ^ (e + 1) := Nat.one_le_pow _ _ (by dsimp [b]; omega)
  have hn := Nat.mul_le_mul_left (n + 1) hone
  change words ≤ n + 1 + q * b ^ e at hw
  change words ≤ 2 * (n + 1) * b ^ (e + 1)
  rw [pow_succ] at hn ⊢
  nlinarith

/-- A block identifier in this store fits a constant number of RAM words
for every fixed exponent e. -/
theorem address_bits {n e i : ℕ}
    (hi : i < 2 * (n + 1) * (Parameters.logCap n + 1) ^ e) :
    i.size ≤ 1 + (Parameters.logCap n + 1) * (e + 1) := by
  let b := Parameters.logCap n + 1
  have hn : n + 1 ≤ 2 ^ b := (Nat.lt_pow_succ_log_self (by decide) (n + 1)).le
  have hb : b ≤ 2 ^ b := Nat.lt_two_pow_self.le
  apply Nat.size_le.mpr
  calc
    i < 2 * (n + 1) * b ^ e := hi
    _ ≤ (2 * 2 ^ b) * (2 ^ b) ^ e :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) (Nat.pow_le_pow_left hb e)
    _ = 2 ^ (1 + b * (e + 1)) := by rw [pow_add 2 1, pow_one, pow_mul 2 b, pow_succ (2 ^ b)]; ac_rfl

/-- For a legal run that reaches a correct leaf, the prefix estimate is
only required if the leaf is reached strictly before the horizon. -/
theorem terminal_of_short_prefix {n k : ℕ} (hk : 64 ≤ k) (s : Strategy n)
    (t : DecisionTree n) (ht : t.Correct)
    (hlegal : ∃ π : Ranking n, Compatible π (t.run s []).observations)
    (hprefix : ∀ h, Follows s h → h.length < Controller.horizon n →
      log2 (n.factorial : ℝ) - (1 + prefixOverhead k) * h.length ≤
        log2 (transcriptCount h : ℝ)) :
    log2 (n.factorial : ℝ) ≤ (1 + prefixOverhead k) * (t.run s []).comparisons := by
  by_cases hearly : (t.run s []).comparisons < Controller.horizon n
  · have hf := run_follows s t [] Follows.nil
    simp only [List.append_nil] at hf
    have hb := hprefix _ hf (by simpa only [List.length_reverse, t.run_observations_length] using hearly)
    rw [transcriptCount_reverse, transcriptCount_run_eq_one s t ht hlegal] at hb
    simp only [Nat.cast_one, log2_one, List.length_reverse, t.run_observations_length] at hb
    linarith
  · have hh : Controller.horizon n ≤ (t.run s []).comparisons := by omega
    have hh' : (Controller.horizon n : ℝ) ≤ (t.run s []).comparisons := by exact_mod_cast hh
    have hδ := prefixOverhead_nonneg (show (64 : ℝ) ≤ k by exact_mod_cast hk)
    have hf := (Controller.log_factorial_le_horizon n).trans hh'
    nlinarith [mul_nonneg hδ (Nat.cast_nonneg (α := ℝ) (t.run s []).comparisons)]

/-- The horizon reduction for any strategy using the chosen parameters.
Consistency includes the frozen continuation and the small-input fallback. -/
theorem optimal_of_short_prefix (extra : Expr) (s : ∀ n, Strategy n)
    (hlegal : ConsistentFamily s)
    (hprefix : ∀ n, 64 ≤ parameter extra n → ∀ h, Follows (s n) h →
      h.length < Controller.horizon n →
      log2 (n.factorial : ℝ) - (1 + prefixOverhead (parameter extra n)) * h.length ≤
        log2 (transcriptCount h : ℝ)) : AsymptoticallyOptimal s := by
  refine ⟨hlegal, ?_⟩
  intro ε hε
  have hp := parameter_tendsto extra
  have hhalf : 0 < ε / 2 := by linarith
  have hqual := (tendsto_atTop.1 hp) 64
  have hrate := (tendsto_order.1 (Continuous.selected_overhead_tendsto _ hp)).2 _ hhalf
  have hrem := (tendsto_order.1 linear_remainder_tendsto).2 _ hhalf
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hqual.and (hrate.and hrem))
  refine ⟨max 2 N, ?_⟩
  intro n hn t ht
  obtain ⟨hk, hδn, hr⟩ := hN n ((le_max_right _ _).trans hn)
  have hT := nLog2n_positive ((le_max_left _ _).trans hn)
  have hb := terminal_of_short_prefix hk (s n) t ht (hlegal n t) (hprefix n hk)
  apply relative_clock_bound hT.le (Nat.cast_nonneg _) hε.le _ hδn.le ((div_le_iff₀ hT).mp hr.le)
  linarith [log_factorial_lower n]

/-- Concrete comparison guarantee for the reference controller with the
rounded-accuracy schedule. This theorem concerns its answers. -/
theorem reference_optimal (extra : Expr) :
    AsymptoticallyOptimal (fun n => Controller.strategy (parameter extra n)) := by
  apply optimal_of_short_prefix extra
  · exact Controller.consistent_parameter_schedule _ (fun n hk => Controller.compareGuarantee n _ hk)
  · exact fun _ hk h hf _ => Controller.prefix_count _ hk h hf

end SortingAdversary.Continuous.PolylogSchedule
