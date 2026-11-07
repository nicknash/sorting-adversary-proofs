import SortingAdversary.Optimal.ControllerResources
import SortingAdversary.Optimal.LocalOracleBitBounds
import SortingAdversary.Optimal.UniformRoutingWork
import SortingAdversary.Optimal.UniformRepairPolynomial
import SortingAdversary.Optimal.TreeReservationEntropy

/-!
# Uniform binary resource certificates for the executed adversary

The word-cost implementation is paired with concrete operand certificates:
reachable counters and immutable IDs; the palettes along every real repair
trace from a stored node; actual local count pairs, rational fields, and
cross products; every partial DP sum; and the finite ranking keys. The
accepted stage supplies bounds for its arithmetic and every power prefix.

The final cost uses `RationalBitWork.Model`, the explicit bounded-operand
schoolbook charging model. It is a cost theorem for the same measured query
program, not a claim about elapsed time in Lean's native integer library.
-/

namespace SortingAdversary.Optimal.UniformBitResources

open PrimitiveWork RepresentationWork WidthRepair MeasuredOracleBounds
open ControllerResources UniformRepairWork LocalOracleBitBounds
open PoolTreeTraversal StoredEvolution

variable {n j : ℕ} {s t : WidthRepair.State n}

def bits (n : ℕ) : ℕ := 1000000 * (n + 1) ^ 8

theorem small_polynomial_le (n C d : ℕ) (hC : C ≤ 1000000) (hd : d ≤ 8) :
    C * (n + 1) ^ d ≤ bits n :=
  Nat.mul_le_mul hC (Nat.pow_le_pow_right (Nat.succ_pos _) hd)

theorem size_le_value (value : ℕ) : Nat.size value ≤ value :=
  Nat.size_le.mpr Nat.lt_two_pow_self

theorem size_of_le {value bound : ℕ} (h : value ≤ bound) : Nat.size value ≤ bound :=
  (size_le_value value).trans h

theorem logCap_le_bits (n : ℕ) : Parameters.logCap n ≤ bits n := by
  have h := Nat.log_le_self 2 (n + 1)
  exact h.trans (by simpa using small_polynomial_le n 1 1 (by decide) (by decide))

theorem localCap_le_bits (n : ℕ) : localCap n + 1 ≤ bits n := by
  have h : localCap n + 1 ≤ 4 * (n + 1) ^ 2 := by unfold localCap; nlinarith
  exact h.trans (small_polynomial_le n 4 2 (by decide) (by decide))

theorem countBits_le_bits (n : ℕ) : countBits n (localCap n + 1) ≤ bits n :=
  (local_countBits_le n).trans (small_polynomial_le n 30 4 (by decide) (by decide))

theorem twice_countBits_le_bits (n : ℕ) : 2 * countBits n (localCap n + 1) ≤ bits n := by
  have h := Nat.mul_le_mul_left 2 (local_countBits_le n)
  exact h.trans (by simpa only [← Nat.mul_assoc] using
    small_polynomial_le n 60 4 (by decide) (by decide))

theorem countBits_add_three_le_bits (n : ℕ) : countBits n (localCap n + 1) + 3 ≤ bits n := by
  have hp : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hc := local_countBits_le n
  apply le_trans (show countBits n (localCap n + 1) + 3 ≤ 33 * (n + 1) ^ 4 by omega)
  exact small_polynomial_le n 33 4 (by decide) (by decide)

theorem counterBound_le_bits (n : ℕ) : counterBound n ≤ bits n :=
  (counterBound_polynomial n).trans (small_polynomial_le n 20 4 (by decide) (by decide))

theorem cutoff_le_bits (n : ℕ) : UniformAdversary.cutoff n ≤ bits n := by
  apply (cutoff_le n).trans
  have h : 2 * n * (n + 2) ≤ 2 * (n + 1) ^ 2 := by nlinarith
  exact h.trans (small_polynomial_le n 2 2 (by decide) (by decide))

theorem transient_counter_le_bits (n : ℕ) : counterBound n + (n + n * n) + 1 ≤ bits n := by
  have h : counterBound n + (n + n * n) + 1 ≤ 30 * (n + 1) ^ 4 := by
    have hc := counterBound_polynomial n
    nlinarith [sq_nonneg (n : ℤ)]
  exact h.trans (small_polynomial_le n 30 4 (by decide) (by decide))

theorem trace_palette_cap (trace : Trace s t) (hp : s.pool.palette ≤ 2 * n + 1) :
    t.pool.palette ≤ localCap n := by
  have ht := (MeasuredRepairBounds.trace_size_le trace).trans (size_le_localCap hp)
  exact (Nat.le_add_right _ _).trans ht

theorem palette_count_cap (hp : s.pool.palette ≤ localCap n) (hn : 0 < n) :
    s.pool.palette + 1 ≤ (localCap n + 1) * n :=
  (Nat.add_le_add_right hp 1).trans (Nat.le_mul_of_pos_right _ hn)

/-- This certificate names the actual data and intermediate sums used by
the concrete counting programs. Its only carrier restriction is a subset
of the original `n` labels, as produced by their actual ball enumeration. -/
structure LocalOperands (s : WidthRepair.State n) : Prop where
  palette : s.pool.palette ≤ localCap n
  coordinates : ∀ colour : Fin (s.pool.palette + 1), Nat.size colour.val ≤ bits n
  permutations : ∀ identity : Fin (s.pool.palette + 1),
    Nat.size (s.order identity).val ≤ bits n ∧ Nat.size (s.order.symm identity).val ≤ bits n
  cdfThresholds : ∀ coordinate : Fin (s.pool.palette + 1), Nat.size (coordinate.val + 1) ≤ bits n
  branchIntegers : ∀ (access : LocalAccess s) (r : ℕ) (x y : Fin n),
    Nat.size (MeasuredLocalOracle.branchCounts (MeasuredLocalOracle.prepare access).value r x y).value.1 ≤ bits n ∧
      Nat.size (MeasuredLocalOracle.branchCounts (MeasuredLocalOracle.prepare access).value r x y).value.2 ≤ bits n
  cdfIntegers : ∀ (access : LocalAccess s) (r : ℕ) (x : Fin n) (cut : ℕ),
    Nat.size (MeasuredLocalOracle.cdfCounts (MeasuredLocalOracle.prepare access).value r x cut).value.1 ≤ bits n ∧
      Nat.size (MeasuredLocalOracle.cdfCounts (MeasuredLocalOracle.prepare access).value r x cut).value.2 ≤ bits n
  branchRationals : ∀ (access : LocalAccess s) (r : ℕ) (x y : Fin n),
    Nat.size (MeasuredLocalOracle.branch access r x y).value.num.natAbs ≤ bits n ∧
      Nat.size (MeasuredLocalOracle.branch access r x y).value.den ≤ bits n
  cdfRationals : ∀ (access : LocalAccess s) (r : ℕ) (x : Fin n) (cut : ℕ),
    Nat.size (MeasuredLocalOracle.cdf access r x cut).value.num.natAbs ≤ bits n ∧
      Nat.size (MeasuredLocalOracle.cdf access r x cut).value.den ≤ bits n
  crossProducts : ∀ (access : LocalAccess s) (r : ℕ) (x y : Fin n),
    Nat.size ((MeasuredLocalOracle.branch access r y x).value.num *
      ((MeasuredLocalOracle.branch access r x y).value.den : ℤ)).natAbs ≤ bits n ∧
      Nat.size ((MeasuredLocalOracle.branch access r x y).value.num *
        ((MeasuredLocalOracle.branch access r y x).value.den : ℤ)).natAbs ≤ bits n
  calibrationProducts : ∀ (access : LocalAccess s) (r : ℕ) (x : Fin n) (cut : ℕ),
    cut ≤ s.pool.palette + 1 → ∀ threshold ∈ ([1 / 4, 3 / 4] : List ℚ),
    Nat.size (threshold.num * ((MeasuredLocalOracle.cdf access r x cut).value.den : ℤ)).natAbs ≤ bits n ∧
      Nat.size ((MeasuredLocalOracle.cdf access r x cut).value.num * (threshold.den : ℤ)).natAbs ≤ bits n
  tableScans : ∀ b, b ≤ n → ∀ (data : LocalDPWork.Input b (s.pool.palette + 1)) k,
    k ≤ s.pool.palette + 1 → ∀ entries,
    entries.Sublist (LocalDPWork.table data (SubsetWork.enumerate b).value k).value →
    (∀ entry ∈ entries, Nat.size entry.2 ≤ bits n) ∧
      (∀ J, Nat.size (LocalDPWork.read J entries).value ≤ bits n) ∧
      (k + 1 ≤ s.pool.palette + 1 → ∀ J, Nat.size (LocalDPWork.stepSum data k J entries).value ≤ bits n)

theorem local_operands (hp : s.pool.palette ≤ localCap n) (hn : 0 < n) : LocalOperands s := by
  have hK := palette_count_cap hp hn
  have hbits := countBits_le_bits n
  have hcoord (c : Fin (s.pool.palette + 1)) : Nat.size c.val ≤ bits n :=
    (size_of_le (Nat.le_of_lt_succ c.isLt)).trans ((Nat.le_succ _).trans ((Nat.add_le_add_right hp 1).trans
      (localCap_le_bits n)))
  refine ⟨hp, hcoord, fun i => ⟨hcoord _, hcoord _⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (size_of_le (Nat.succ_le_succ (Nat.le_of_lt_succ i.isLt))).trans
      ((Nat.add_le_add_right hp 1).trans (localCap_le_bits n))
  · intro access r x y
    have h := branch_integer_bits access r x y (localCap n + 1) hK
    exact ⟨h.1.trans hbits, h.2.trans hbits⟩
  · intro access r x cut
    have h := cdf_integer_bits access r x cut (localCap n + 1) hK
    exact ⟨h.1.trans hbits, h.2.trans hbits⟩
  · intro access r x y
    have h := branch_sizes_polynomial access r x y (localCap n + 1) hK
    exact ⟨h.1.trans hbits, h.2.trans hbits⟩
  · intro access r x cut
    have h := cdf_sizes_polynomial access r x cut (localCap n + 1) hK
    exact ⟨h.1.trans hbits, h.2.trans hbits⟩
  · intro access r x y
    have h := stopping_cross_product_sizes access r x y (localCap n + 1) hK
    exact ⟨h.1.trans (twice_countBits_le_bits n), h.2.trans (twice_countBits_le_bits n)⟩
  · intro access r x cut _ threshold ht
    have hthreshold : Nat.size threshold.num.natAbs ≤ 3 ∧ Nat.size threshold.den ≤ 3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact quarter_sizes
      · exact three_quarter_sizes
    have h := cross_product_sizes threshold (MeasuredLocalOracle.cdf access r x cut).value 3
      (countBits n (localCap n + 1)) hthreshold (cdf_sizes_polynomial access r x cut (localCap n + 1) hK)
    have bound : 3 + countBits n (localCap n + 1) ≤ bits n := by
      simpa only [Nat.add_comm] using countBits_add_three_le_bits n
    exact ⟨h.1.trans bound, h.2.trans bound⟩
  · intro b hb data k hk entries he
    have h := table_scan_bits_polynomial data k hk entries he n (localCap n + 1)
      (by omega) (hK.trans (Nat.mul_le_mul_left _ (by omega : n ≤ 2 * n)))
    exact ⟨fun entry hm => (h.1 entry hm).trans hbits,
      fun J => (h.2.1 J).trans hbits, fun hl J => (h.2.2 hl J).trans hbits⟩

theorem local_operands_of_trace (trace : Trace s t) (hp : s.pool.palette ≤ 2 * n + 1) (hn : 0 < n) :
    LocalOperands t := local_operands (trace_palette_cap trace hp) hn

theorem rank_key_bits (rows : RankWork.Rows n) (v : Fin n) :
    Nat.size ((RankWork.keys (RankWork.predecessors rows).value).value[v]) ≤ bits n := by
  rw [RankWork.keys_value]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  apply (size_of_le (RankWork.extensionKey_lt (RankWork.values rows) v).le).trans
  have h : n ^ 2 + n ≤ 2 * (n + 1) ^ 2 := by nlinarith
  exact h.trans (small_polynomial_le n 2 2 (by decide) (by decide))

/-- A certificate for one actual active replay state. Each repair-prefix
certificate begins at a real stored node; a public comparison changes its
relation while leaving its palette unchanged. -/
structure ActiveOperands {p : RecursiveController.Parameters} {N : ℕ}
    (clock : Fin (UniformAdversary.cutoff (N + 2) + 1))
    (state : MeasuredController.Active p (N + 2)) : Prop where
  clockBits : Nat.size clock.val ≤ bits (N + 2)
  counterBits : Nat.size state.state.counter ≤ bits (N + 2)
  identities : ∀ identity ∈ TreeChronology.identities state.state.tree.erase,
    Nat.size identity ≤ bits (N + 2)
  nodes : state.state.tree.erase.nodes + 1 ≤ 2 * (N + 2)
  palettes : ∀ entry ∈ storedPools state.state.tree.erase, entry.2.palette ≤ 2 * (N + 2) + 1
  repairs : ∀ identity before, NodeAt state.state.tree identity before →
    ∀ (start next : WidthRepair.State (N + 2)), start.pool.palette = before.pool.palette →
    Trace start next → LocalOperands next

theorem active_operands {p : RecursiveController.Parameters} {N : ℕ}
    (executor : MeasuredController.AnswerExecutor p (N + 2)) (past : History (N + 2))
    (clock : Fin (UniformAdversary.cutoff (N + 2) + 1))
    (state : MeasuredController.Active p (N + 2))
    (he : (MeasuredController.machine p N (UniformAdversary.cutoff (N + 2)) executor).replay past =
      .active clock state) : ActiveOperands clock state := by
  have hc := measured_replay_resources p N executor past clock state he
  refine ⟨(size_of_le (Nat.le_of_lt_succ clock.isLt)).trans (cutoff_le_bits _),
    (size_of_le hc.1).trans (counterBound_le_bits _), ?_, active_nodes state.state (by omega),
    active_palette state.state, ?_⟩
  · intro identity hi
    exact (size_of_le ((hc.2.below identity hi).le.trans hc.1)).trans (counterBound_le_bits _)
  · intro identity before occurs start next hp trace
    apply local_operands_of_trace trace _ (by omega)
    rw [hp]
    exact active_palette state.state (identity, before.pool) (TreeReservationEntropy.nodeAt_storedPools occurs)

theorem capped_scalar_bits {value : ℕ} (h : value ≤ Parameters.logCap n) : Nat.size value ≤ bits n :=
  (size_of_le h).trans (logCap_le_bits n)

theorem prepared_radius_bits (a : UniformStage.Accepted (Parameters.logCap n) j) :
    Nat.size (UniformPreparedWork.prepare a).value.repair.radius ≤ bits n ∧
      Nat.size (UniformPreparedWork.prepare a).value.comparisonRadius ≤ bits n := by
  have h := UniformPreparedWork.radii_le_cap a
  exact ⟨capped_scalar_bits h.1, capped_scalar_bits h.2⟩

theorem stage_power_bits (a : UniformStage.Accepted (Parameters.logCap n) j) :
    (∀ e ≤ a.runtime.normalizer.scale.H + 1,
      Nat.size (WidthScalarWork.power (a.runtime.normalizer.d + 1) e).value ≤ bits n) ∧
    (∀ e ≤ a.runtime.normalizer.scale.H,
      Nat.size (WidthScalarWork.power
        (LocalParameters.clockScale (LocalAccuracy.influenceSize a.runtime.normalizer.scale.H
          a.runtime.normalizer.d)) e).value ≤ bits n) ∧
    (∀ e ≤ 2 * LocalAccuracy.influenceSize a.runtime.normalizer.scale.H a.runtime.normalizer.d,
      Nat.size (WidthScalarWork.power 4 e).value ≤ bits n) := by
  have h := UniformScalarWork.cdf_power_prefixes a
  exact ⟨fun e he => capped_scalar_bits (h.1 e he),
    fun e he => capped_scalar_bits (h.2.1 e he), fun e he => capped_scalar_bits (h.2.2 e he)⟩

theorem stage_base_power_bits (a : UniformStage.Accepted (Parameters.logCap n) j) :
    (∀ e ≤ 2 * a.runtime.normalizer.scale.H + 3,
      Nat.size (WidthScalarWork.power (a.runtime.normalizer.scale.width.L + 1) e).value ≤ bits n) ∧
    (∀ e ≤ a.runtime.normalizer.scale.J + 1,
      Nat.size (WidthScalarWork.power a.runtime.normalizer.scale.A e).value ≤ bits n) := by
  let p := a.runtime.normalizer.scale
  have hpower : (p.width.L + 1) ^ (2 * p.H + 3) ≤ p.A :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide : 0 < 128) p.J_pos)
  refine ⟨?_, ?_⟩
  · intro e he
    exact capped_scalar_bits (((WidthScalarWork.power_value_le (Nat.succ_pos _) he).trans hpower).trans
      (UniformScalarWork.base_cap a))
  · intro e he
    exact capped_scalar_bits ((WidthScalarWork.power_value_le p.one_le_A he).trans a.ratio_cap)

theorem stage_cheap_bits (a : UniformStage.Accepted (Parameters.logCap n) j) :
    Nat.size (a.runtime.normalizer.scale.width.W₀ * 4 ^ a.runtime.normalizer.scale.width.B) ≤ bits n := by
  rw [← a.runtime.cheap_eq]
  exact capped_scalar_bits (UniformScalarWork.cheap_cap a)

theorem width_product_bound (n : ℕ) : 2 * Parameters.logCap n * (localCap n + 1) ≤ bits n := by
  have hlog : Parameters.logCap n ≤ n + 1 := Nat.log_le_self 2 (n + 1)
  have h : 2 * Parameters.logCap n * (localCap n + 1) ≤ 8 * (n + 1) ^ 3 := by
    have hp : localCap n + 1 ≤ 4 * (n + 1) ^ 2 := by unfold localCap; nlinarith
    calc
      _ ≤ 2 * (n + 1) * (4 * (n + 1) ^ 2) := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hlog) hp
      _ = _ := by ring
  exact h.trans (small_polynomial_le n 8 3 (by decide) (by decide))

theorem stage_width_bits (a : UniformStage.Accepted (Parameters.logCap n) j)
    (s : WidthRepair.State n) (hp : s.pool.palette ≤ localCap n) (v : Fin n) :
    Nat.size (a.runtime.normalizer.scale.width.L * s.width v) ≤ bits n ∧
      Nat.size (a.runtime.normalizer.scale.R * s.width v) ≤ bits n := by
  have h := UniformScalarWork.width_products a s v
  have bound : Parameters.logCap n * (s.pool.palette + 1) ≤ bits n := by
    apply (Nat.mul_le_mul_left _ (Nat.add_le_add_right hp 1)).trans
    apply le_trans _ (width_product_bound n)
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
  exact ⟨(size_of_le h.1).trans bound, (size_of_le h.2).trans bound⟩

theorem stage_threshold_bits (a : UniformStage.Accepted (Parameters.logCap n) j)
    (s : WidthRepair.State n) (hp : s.pool.palette ≤ localCap n) (v : Fin n) (i : ℕ)
    (hi : i ≤ a.runtime.normalizer.scale.J + 1) :
    Nat.size ((WidthScalarWork.power a.runtime.normalizer.scale.A i).value * s.width v) ≤ bits n := by
  apply (size_of_le (UniformScalarWork.threshold_product a s v i hi)).trans
  apply (Nat.mul_le_mul_left _ (Nat.add_le_add_right hp 1)).trans
  exact (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))).trans
    (width_product_bound n)

theorem ordinary_receipt_bits {length : ℕ} (hl : length ≤ localCap n + 1) :
    Nat.size (16 * length) ≤ bits n := by
  have h : 16 * (localCap n + 1) ≤ 64 * (n + 1) ^ 2 := by unfold localCap; nlinarith
  exact (size_of_le (Nat.mul_le_mul_left 16 hl)).trans
    (h.trans (small_polynomial_le n 64 2 (by decide) (by decide)))

theorem stage_scale_receipt_bits (a : UniformStage.Accepted (Parameters.logCap n) j)
    {length palette : ℕ} (hp : palette ≤ localCap n) (hl : length ≤ palette + 1) :
    Nat.size (2 * 4 ^ a.runtime.normalizer.scale.width.B * length) ≤ bits n := by
  apply (size_of_le (UniformScalarWork.scale_receipt a hl)).trans
  exact (Nat.mul_le_mul_left _ (Nat.add_le_add_right hp 1)).trans (width_product_bound n)

theorem stage_cut_bits (a : UniformStage.Accepted (Parameters.logCap n) j) :
    Nat.size (WidthScalarWork.cut a.runtime.normalizer.scale.width).value.num.natAbs ≤ bits n ∧
      Nat.size (WidthScalarWork.cut a.runtime.normalizer.scale.width).value.den ≤ bits n := by
  have h := UniformScalarWork.cut_receipt_sizes a
  have hb := (size_le_value (Parameters.logCap n)).trans (logCap_le_bits n)
  exact ⟨h.1.trans hb, h.2.trans hb⟩

theorem charge_polynomial (n C d : ℕ) :
    RationalBitWork.Model.charge (C * (n + 1) ^ d) (bits n) ≤
      C * 1000001 ^ 2 * (n + 1) ^ (d + 16) := by
  have hpow : 1 ≤ (n + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  have hwidth : bits n + 1 ≤ 1000001 * (n + 1) ^ 8 := by unfold bits; omega
  unfold RationalBitWork.Model.charge RationalBitWork.Model.unit
  calc
    _ ≤ C * (n + 1) ^ d * (1000001 * (n + 1) ^ 8) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hwidth 2)
    _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring

theorem step_work_polynomial (a : UniformStage.Accepted (Parameters.logCap n) j)
    (data : UniformPreparedWork.Data a) {cutoff : ℕ}
    (state : MeasuredController.State a.controller n cutoff) (q : Query n) :
    (MeasuredController.step (UniformRoutingWork.executor a data) state q).work ≤
      4000000000000 * (n + 1) ^ 16 := by
  apply (MeasuredController.step_work_le (UniformRoutingWork.executor a data) _
    (UniformRoutingWork.executor_polynomial a data) state q).trans
  unfold MeasuredController.stepBound RankWork.workBound
  ring_nf
  gcongr <;> norm_num <;> omega

/-- The actual measured query's binary charge in the stated model.
`active_operands`, `local_operands_of_trace`, and the stage certificates
above establish the nontrivial operand envelopes on reachable states. -/
theorem step_bitCharge_polynomial (a : UniformStage.Accepted (Parameters.logCap n) j)
    (data : UniformPreparedWork.Data a) {cutoff : ℕ}
    (state : MeasuredController.State a.controller n cutoff) (q : Query n) :
    RationalBitWork.Model.charge
      (MeasuredController.step (UniformRoutingWork.executor a data) state q).work (bits n) ≤
        10000000000000000000000000 * (n + 1) ^ 32 := by
  apply (RationalBitWork.Model.charge_mono (step_work_polynomial a data state q) le_rfl).trans
  apply (charge_polynomial n 4000000000000 16).trans
  exact Nat.mul_le_mul_right _ (by decide)

end SortingAdversary.Optimal.UniformBitResources
