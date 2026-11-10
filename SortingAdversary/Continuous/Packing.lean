import SortingAdversary.Continuous.Accounting
import SortingAdversary.Continuous.Sampling

/-!
# From sampled queried labels to the prefix bound

This module joins the independent-draw ordering theorem, unrestricted insertion
of untouched labels, the actual product of anchor weights, and the refinement
accounting.  Its final theorem lists the remaining tree-semantic obligations
explicitly: the feasible event's probability, its transcript consistency,
the equality of its volume with the gain/loss log, and the arc budget.
-/

namespace SortingAdversary.Continuous

open MeasureTheory
open scoped BigOperators

theorem log2_finset_prod {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 < f i) : log2 (∏ i ∈ S, f i) = ∑ i ∈ S, log2 (f i) := by
  unfold log2
  rw [Real.log_prod (fun i hi => (hf i hi).ne')]
  simp only [div_eq_mul_inv, Finset.sum_mul]

namespace RefinementEvent

noncomputable def weightProduct (k : ℝ) : RefinementEvent → ℝ
  | .selection c _ => anchorWeight k c.1
  | .degree c _ => anchorWeight k c.1
  | .path anchors _ => ∏ c ∈ anchors, anchorWeight k c.1

theorem weightProduct_pos {k : ℝ} (hk : 1 < k) (e : RefinementEvent) :
    0 < e.weightProduct k := by
  cases e with
  | selection c g => exact anchorWeight_pos hk c.1
  | degree c g => exact anchorWeight_pos hk c.1
  | path anchors g => exact Finset.prod_pos (fun c _ => anchorWeight_pos hk c.1)

theorem log_weightProduct {k : ℝ} (hk : 1 < k) (e : RefinementEvent) :
    log2 (e.weightProduct k) = -e.cost k := by
  cases e with
  | selection c g => simp [weightProduct, cost, anchorCost]
  | degree c g => simp [weightProduct, cost, anchorCost]
  | path anchors g =>
    rw [weightProduct, log2_finset_prod _ _ (fun c _ => anchorWeight_pos hk c.1)]
    simp [cost, anchorCost, Finset.sum_neg_distrib]

end RefinementEvent

namespace AccountingLog

noncomputable def weightProduct (L : AccountingLog) (k : ℝ) : ℝ :=
  (L.events.map (RefinementEvent.weightProduct k)).prod

theorem weightProduct_pos {k : ℝ} (hk : 1 < k) (L : AccountingLog) :
    0 < L.weightProduct k := by
  obtain ⟨events, losses⟩ := L
  induction events with
  | nil => simp [weightProduct]
  | cons e es ih =>
    exact mul_pos (e.weightProduct_pos hk) ih

/-- The product of all weights actually recorded by the finite refinement log
has logarithm minus its total information cost. -/
theorem log_weightProduct {k : ℝ} (hk : 1 < k) (L : AccountingLog) :
    log2 (L.weightProduct k) = -L.totalCost k := by
  obtain ⟨events, losses⟩ := L
  induction events with
  | nil => simp [weightProduct, totalCost]
  | cons e es ih =>
    have hp : 0 < (AccountingLog.mk es losses).weightProduct k :=
      (AccountingLog.mk es losses).weightProduct_pos hk
    change log2 (e.weightProduct k * (AccountingLog.mk es losses).weightProduct k) = _
    rw [log2_mul (e.weightProduct_pos hk).ne' hp.ne', e.log_weightProduct hk]
    rw [ih]
    simp [totalCost, add_comm]

end AccountingLog

/-- Sampling only the queried labels retains the full `n!` factor because
unqueried labels may be inserted at *every* position. -/
theorem queried_sample_count {s : ℕ} (h : History s) (r : ℕ)
    (embedding : Item s ↪ Item (s + r)) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (good : Set (Item s → ℝ)) (p : ℝ)
    (hgood : ∀ x ∈ good, ∃ π, Compatible π h ∧ x ∈ orderCell π)
    (hmass : p ≤ (Measure.pi (fun _ : Fin s => ν)).real good) :
    ((s + r).factorial : ℝ) * p ≤ transcriptCount (mapHistory embedding h) := by
  have hs : (0 : ℝ) < s.factorial := by positivity
  have hn : (0 : ℝ) < (s + r).factorial := by positivity
  have hsmall := count_of_iid_event h ν (atomless_iid_tie_free s ν) good hgood
  have hfree : ((s + r).factorial : ℝ) * transcriptCount h ≤
      s.factorial * (transcriptCount (mapHistory embedding h) : ℝ) := by
    exact_mod_cast embedded_history_count h r embedding
  have hsmall' : (s.factorial : ℝ) * p ≤ transcriptCount h :=
    (mul_le_mul_of_nonneg_left hmass hs.le).trans hsmall
  have hlarge := mul_le_mul_of_nonneg_left hsmall' hn.le
  apply (mul_le_mul_iff_right₀ hs).mp
  nlinarith

/-- The logarithmic form of the paper's packing inequality, with the anchor
product computed from the refinement log rather than supplied independently. -/
theorem log_packing {n s : ℕ} {k Z T : ℝ} (hk : 1 < k) (hZ : 0 < Z)
    (L : AccountingLog)
    (hcount : (n.factorial : ℝ) * stopMass k ^ s * Z * L.weightProduct k ≤ T) :
    log2 (n.factorial : ℝ) - s * stopCost k + log2 Z - L.totalCost k ≤ log2 T := by
  have hn : (0 : ℝ) < n.factorial := by positivity
  have hstop := pow_pos (stopMass_pos hk) s
  have hw := L.weightProduct_pos hk
  have hlog := log2_mono (mul_pos (mul_pos (mul_pos hn hstop) hZ) hw) hcount
  rw [log2_mul (mul_pos (mul_pos hn hstop) hZ).ne' hw.ne',
    log2_mul (mul_pos hn hstop).ne' hZ.ne',
    log2_mul hn.ne' hstop.ne', log2_pow, L.log_weightProduct hk] at hlog
  unfold stopCost
  linarith

/-- The complete counting/accounting reduction for the revised paper.

This is intentionally a reduction, not the assertion that its explicit
tree-semantic premises have already been proved for an executable controller.
In particular `hmass` concerns a concrete measurable sampling experiment and
`hvolume` must identify the actual node volume with the recorded gain log.
-/
theorem prefix_count_of_tree_mass {k s : ℕ} (hk : 64 ≤ k)
    (h : History s) (r : ℕ) (embedding : Item s ↪ Item (s + r))
    (L : AccountingLog) (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (good : Set (Item s → ℝ)) (Z : ℝ) (hZ : 0 < Z)
    (hgood : ∀ x ∈ good, ∃ π, Compatible π h ∧ x ∈ orderCell π)
    (hmass : stopMass k ^ s * Z * L.weightProduct k ≤
      (Measure.pi (fun _ : Fin s => ν)).real good)
    (hvolume : log2 Z = L.logVolume) (hvolume_le : L.logVolume ≤ 0)
    (he : ∀ e ∈ L.events, e.Valid k)
    (hloss : ∀ a ∈ L.losses, a ≤ answerLoss k)
    (harcs : k * L.degreeRepairs ≤ L.comparisons)
    (hqueried : s ≤ 2 * L.comparisons)
    (hlength : L.comparisons = h.length) :
    log2 ((s + r).factorial : ℝ) - (1 + prefixOverhead k) * h.length ≤
      log2 (transcriptCount (mapHistory embedding h) : ℝ) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hcount := queried_sample_count h r embedding ν good _ hgood hmass
  have hcount' : ((s + r).factorial : ℝ) * stopMass k ^ s * Z * L.weightProduct k ≤
      transcriptCount (mapHistory embedding h) := by
    simpa only [mul_assoc] using hcount
  have hpacking := log_packing (n := s + r) hk1 hZ L hcount'
  rw [hvolume] at hpacking
  have hprefix := prefix_bound_of_packing hk L s _ _ he hloss hvolume_le harcs hqueried hpacking
  simpa only [hlength] using hprefix

end SortingAdversary.Continuous
