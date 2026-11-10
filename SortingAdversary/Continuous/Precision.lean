import SortingAdversary.Continuous.Dyadic
import SortingAdversary.Continuous.LocalSelection
import SortingAdversary.Continuous.RefinementBatch
import Mathlib.Data.Nat.Size

/-!
# Exact dyadic precision of the continuous implementation

The predicates in this file describe actual rational endpoints. An affine
digit adds at most the binary alphabet exponent; a whole endpoint calculation
therefore adds that exponent times its actual schedule length. Normalization
and restriction take maxima and minima, so do not add precision. The real
rounding routine uses no finer grid than a nondegenerate input interval.
-/

namespace SortingAdversary.Continuous.Precision

open FiniteAveraging OrderRegion Certificates

theorem zero_onGrid (F : ℕ) : OnDyadicGrid F 0 := ⟨0, by simp⟩

theorem one_onGrid (F : ℕ) : OnDyadicGrid F 1 := by
  refine ⟨(2 : ℤ) ^ F, ?_⟩
  simp

theorem grid_mono {F G : ℕ} {q : ℚ} (h : OnDyadicGrid F q) (hFG : F ≤ G) :
    OnDyadicGrid G q := by
  simpa only [Nat.add_sub_of_le hFG] using onDyadicGrid_add h (G - F)

def BoundsOnGrid {ι : Type*} (D : System ι ℚ) (F : ℕ) : Prop :=
  (∀ x, OnDyadicGrid F (D.lower x)) ∧ ∀ x, OnDyadicGrid F (D.upper x)

theorem bounds_mono {ι : Type*} {D : System ι ℚ} {F G : ℕ}
    (h : BoundsOnGrid D F) (hFG : F ≤ G) : BoundsOnGrid D G :=
  ⟨fun x => grid_mono (h.1 x) hFG, fun x => grid_mono (h.2 x) hFG⟩

section Coordinates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fullSteps_onGrid (D : System ι ℚ) (F s : ℕ)
    (steps : List (ι × Fin (2 ^ s))) (Y : ι → ℚ)
    (hD : BoundsOnGrid D F) (hY : ∀ x, OnDyadicGrid F (Y x)) :
    ∀ x, OnDyadicGrid (F + s * steps.length) (fullSteps D (2 ^ s) steps Y x) := by
  induction steps generalizing F Y with
  | nil => simpa only [fullSteps, List.foldl_nil, List.length_nil, mul_zero, add_zero] using hY
  | cons a steps ih =>
    have hD' := bounds_mono hD (Nat.le_add_right F s)
    have hY' := update_onDyadicGrid D F s a.2 a.1 Y (hD.1 a.1) (hD.2 a.1) hY
    have hh := ih (F + s) (update D (2 ^ s) a.2 a.1 Y) hD' hY'
    simpa only [fullSteps, List.foldl_cons, List.length_cons, mul_add, mul_one,
      Nat.add_assoc, Nat.add_comm s, Nat.add_left_comm s] using hh

theorem endpointEntry_onGrid (D : System ι ℚ) (F s : ℕ) (schedule : List ι)
    (digits : Fin schedule.length → Fin (2 ^ s)) (hD : BoundsOnGrid D F) (x : ι) :
    OnDyadicGrid (F + s * schedule.length) (endpointEntry D (2 ^ s) schedule digits x).1 ∧
    OnDyadicGrid (F + s * schedule.length) (endpointEntry D (2 ^ s) schedule digits x).2 := by
  have hlen : (assignedSteps (2 ^ s) schedule digits).length = schedule.length := by
    simp [assignedSteps]
  constructor
  · simpa only [endpointEntry, hlen] using
      fullSteps_onGrid D F s (assignedSteps (2 ^ s) schedule digits) D.lower hD hD.1 x
  · simpa only [endpointEntry, hlen] using
      fullSteps_onGrid D F s (assignedSteps (2 ^ s) schedule digits) D.upper hD hD.2 x

theorem enclose_onGrid (D : System ι ℚ) (F s : ℕ) (schedule : List ι)
    (hD : BoundsOnGrid D F) {I : ι → ℚ × ℚ} (hI : I ∈ enclose D (2 ^ s) schedule)
    (x : ι) :
    OnDyadicGrid (F + s * schedule.length) (I x).1 ∧
    OnDyadicGrid (F + s * schedule.length) (I x).2 := by
  obtain ⟨digits, _, rfl⟩ := List.mem_map.mp hI
  exact endpointEntry_onGrid D F s schedule digits hD x

theorem propagateLower_onGrid (D : System ι ℚ) (F : ℕ) (x : ι)
    (hD : BoundsOnGrid D F) : BoundsOnGrid (propagateLower D x) F := by
  refine ⟨fun y => ?_, hD.2⟩
  by_cases hy : y = x
  · subst y
    simpa only [propagateLower, Function.update_self] using
      conditionalLower_onDyadicGrid D x D.lower F (hD.1 x) hD.1
  · simpa only [propagateLower, Function.update_of_ne hy] using hD.1 y

theorem propagateUpper_onGrid (D : System ι ℚ) (F : ℕ) (x : ι)
    (hD : BoundsOnGrid D F) : BoundsOnGrid (propagateUpper D x) F := by
  refine ⟨hD.1, fun y => ?_⟩
  by_cases hy : y = x
  · subst y
    simpa only [propagateUpper, Function.update_self] using
      conditionalUpper_onDyadicGrid D x D.upper F (hD.2 x) hD.2
  · simpa only [propagateUpper, Function.update_of_ne hy] using hD.2 y

theorem normalize_onGrid (D : System ι ℚ) (F : ℕ) (order : List ι)
    (hD : BoundsOnGrid D F) : BoundsOnGrid (normalize D order) F := by
  have hlo : ∀ (L : List ι) (D : System ι ℚ), BoundsOnGrid D F →
      BoundsOnGrid (L.foldl propagateLower D) F := by
    intro L
    induction L with
    | nil => exact fun _ h => h
    | cons x xs ih => exact fun D h => ih _ (propagateLower_onGrid D F x h)
  have hhi : ∀ (L : List ι) (D : System ι ℚ), BoundsOnGrid D F →
      BoundsOnGrid (L.foldl propagateUpper D) F := by
    intro L
    induction L with
    | nil => exact fun _ h => h
    | cons x xs ih => exact fun D h => ih _ (propagateUpper_onGrid D F x h)
  exact hhi order.reverse _ (hlo order D hD)

end Coordinates

/-- A nonzero dyadic interval is at least one grid spacing wide. -/
theorem interval_width_ge {a b : ℚ} {F : ℕ} (ha : OnDyadicGrid F a)
    (hb : OnDyadicGrid F b) (hab : a < b) : 1 / (2 : ℚ) ^ F ≤ b - a := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨w, rfl⟩ := hb
  have hp : (0 : ℚ) < 2 ^ F := by positivity
  have hzw : z < w := by exact_mod_cast (div_lt_div_iff_of_pos_right hp).mp hab
  have hz : (1 : ℚ) ≤ (w : ℚ) - z := by exact_mod_cast (show (1 : ℤ) ≤ w - z by omega)
  have hh := div_le_div_of_nonneg_right hz hp.le
  calc
    1 / (2 : ℚ) ^ F ≤ ((w : ℚ) - z) / 2 ^ F := hh
    _ = (w : ℚ) / 2 ^ F - z / 2 ^ F := by ring

theorem roundingExponent_le {J : Interval} {F : ℕ}
    (hgrid : OnDyadicGrid F J.1 ∧ OnDyadicGrid F J.2)
    (hl : 0 < J.1) (hu : J.2 < 1) (hJ : J.1 < J.2) : roundingExponent J ≤ F := by
  have hw := interval_width_ge hgrid.1 hgrid.2 hJ
  have hs := (spacing_spec hJ).2
  rw [spacing_eq_inverse_pow hl hu hJ] at hs
  by_contra h
  have hpow : (2 : ℚ) ^ (F + 1) ≤ 2 ^ roundingExponent J :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hi := one_div_le_one_div_of_le (by positivity : (0 : ℚ) < 2 ^ (F + 1)) hpow
  have he : (2 : ℚ) * (1 / 2 ^ (F + 1)) = 1 / 2 ^ F := by
    rw [pow_succ]
    field_simp
  linarith

theorem roundUp_preserves_grid {J : Interval} {F : ℕ}
    (hgrid : OnDyadicGrid F J.1 ∧ OnDyadicGrid F J.2)
    (hl : 0 < J.1) (hu : J.2 < 1) (hJ : J.1 < J.2) : OnDyadicGrid F (roundUp J) :=
  grid_mono (roundUp_onDyadicGrid hl hu hJ) (roundingExponent_le hgrid hl hu hJ)

theorem middleHalf_onGrid {a b : ℚ} {F : ℕ} (ha : OnDyadicGrid F a)
    (hb : OnDyadicGrid F b) :
    OnDyadicGrid (F + 2) (middleHalf a b).1 ∧
    OnDyadicGrid (F + 2) (middleHalf a b).2 := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨w, rfl⟩ := hb
  constructor
  · refine ⟨3 * z + w, ?_⟩
    simp only [middleHalf, pow_add, pow_two, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    ring
  · refine ⟨z + 3 * w, ?_⟩
    simp only [middleHalf, pow_add, pow_two, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    ring

theorem middleHalf_anchor_onGrid {a b : ℚ} {F : ℕ} (ha : OnDyadicGrid F a)
    (hb : OnDyadicGrid F b) (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hab : a < b) :
    OnDyadicGrid (F + 2) (roundUp (middleHalf a b)) := by
  apply roundUp_preserves_grid (middleHalf_onGrid ha hb)
  all_goals dsimp [middleHalf]; linarith

theorem initial_onGrid (n F : ℕ) : BoundsOnGrid (TreeState.initial n).system F :=
  ⟨fun _ => zero_onGrid F, fun _ => one_onGrid F⟩

theorem resetCoordinate_onGrid {n : ℕ} (D : System (Fin n) ℚ) (F : ℕ)
    (x : Fin n) (c : ℚ) (hD : BoundsOnGrid D F) (hc : OnDyadicGrid F c) :
    BoundsOnGrid (TreeState.resetCoordinate D x c) F := by
  constructor
  · intro y
    simp only [TreeState.resetCoordinate]
    split_ifs
    · exact zero_onGrid F
    · exact onDyadicGrid_max (hD.1 y) hc
    · exact hD.1 y
  · intro y
    simp only [TreeState.resetCoordinate]
    split_ifs
    · exact one_onGrid F
    · exact onDyadicGrid_min (hD.2 y) hc
    · exact hD.2 y

/-- Actual stored bounds in a completed batch use no grid finer than its
input bounds and the finitely many anchors actually written by that batch. -/
theorem refinementSteps_onGrid {n : ℕ} {s s' : TreeState.State n ℚ}
    {moves : List (Fin n × ℚ)} (h : TreeState.RefinementSteps s moves s') (F : ℕ)
    (hD : BoundsOnGrid s.system F) (hc : ∀ m ∈ moves, OnDyadicGrid F m.2) :
    BoundsOnGrid s'.system F := by
  induction h with
  | nil s => exact hD
  | cons s x c order moves s' hxx hxc tail ih =>
    apply ih
    · exact normalize_onGrid _ F order
        (resetCoordinate_onGrid s.system F x c hD (hc (x, c) (by simp)))
    · exact fun m hm => hc m (by simp [hm])

private theorem list_getD_onGrid (L : List ℚ) (i F : ℕ)
    (h : ∀ q ∈ L, OnDyadicGrid F q) : OnDyadicGrid F (L[i]?.getD 0) := by
  cases he : L[i]? with
  | none => simpa only [he, Option.getD_none] using zero_onGrid F
  | some q => simpa only [he, Option.getD_some] using h q (List.mem_of_getElem? he)

theorem centralCandidate_onGrid (L : List Interval) (F : ℕ)
    (h : ∀ I ∈ L, OnDyadicGrid F I.1 ∧ OnDyadicGrid F I.2) :
    OnDyadicGrid F (centralCandidate L).1 ∧ OnDyadicGrid F (centralCandidate L).2 := by
  constructor
  · apply list_getD_onGrid
    intro q hq
    obtain ⟨I, hI, rfl⟩ := List.mem_map.mp (List.mem_mergeSort.mp hq)
    exact (h I hI).2
  · apply list_getD_onGrid
    intro q hq
    obtain ⟨I, hI, rfl⟩ := List.mem_map.mp (List.mem_mergeSort.mp hq)
    exact (h I hI).1

theorem centralInterval_onGrid {L : List Interval} {J : Interval} (F : ℕ)
    (hgrid : ∀ I ∈ L, OnDyadicGrid F I.1 ∧ OnDyadicGrid F I.2)
    (h : centralInterval L = some J) : OnDyadicGrid F J.1 ∧ OnDyadicGrid F J.2 := by
  unfold centralInterval at h
  split at h
  · contradiction
  · dsimp only at h
    split at h
    · cases h
      exact centralCandidate_onGrid L F hgrid
    · contradiction

theorem centralInterval_interior {l r : ℚ} {L : List Interval} {J : Interval}
    (hL : ∀ I ∈ L, l < I.2 ∧ I.1 < r) (hc : centralInterval L = some J) :
    l < J.1 ∧ J.2 < r := by
  have hcert := centralInterval_certificates hc
  have hN := centralInterval_positive hc
  have hleft : 0 < leftCount L J.1 := by omega
  have hright : 0 < rightCount L J.2 := by omega
  obtain ⟨I, hI, hend⟩ := List.countP_pos_iff.mp hleft
  obtain ⟨I', hI', hstart⟩ := List.countP_pos_iff.mp hright
  exact ⟨(hL I hI).1.trans_le (of_decide_eq_true hend),
    (of_decide_eq_true hstart).trans_lt (hL I' hI').2⟩

/-- Both actual branches of `ChooseAnchor` obey one shared mesh bound. -/
theorem chooseAnchor_onGrid {l r : ℚ} {L : List Interval} {F G : ℕ}
    (hl : OnDyadicGrid F l) (hr : OnDyadicGrid F r)
    (hgrid : ∀ I ∈ L, OnDyadicGrid G I.1 ∧ OnDyadicGrid G I.2)
    (hL : ∀ I ∈ L, l < I.2 ∧ I.1 < r)
    (hl0 : 0 ≤ l) (hr1 : r ≤ 1) (hlr : l < r) (hFG : F + 2 ≤ G) :
    OnDyadicGrid G (chooseAnchor l r L) := by
  cases hc : centralInterval L with
  | none =>
    simpa only [chooseAnchor, hc, Option.getD_none] using
      grid_mono (middleHalf_anchor_onGrid hl hr hl0 hr1 hlr) hFG
  | some J =>
    have hi := centralInterval_interior hL hc
    simpa only [chooseAnchor, hc, Option.getD_some] using
      roundUp_preserves_grid (centralInterval_onGrid G hgrid hc)
        (hl0.trans_lt hi.1) (hi.2.trans_le hr1) (centralInterval_inside hc).1

theorem localAnchor_onGrid {n : ℕ} (D : System (Fin n) ℚ) (F s : ℕ)
    (schedule : List (Fin n)) (x : Fin n) (hD : BoundsOnGrid D F)
    (hl : D.WeaklyFeasible D.lower) (hu : D.WeaklyFeasible D.upper)
    (hw : ∀ v, D.lower v < D.upper v) (h0 : 0 ≤ D.lower x) (h1 : D.upper x ≤ 1)
    (hwork : 2 ≤ s * schedule.length) :
    OnDyadicGrid (F + s * schedule.length) (LocalSelection.anchor D (2 ^ s) schedule x) := by
  apply chooseAnchor_onGrid (hD.1 x) (hD.2 x)
  · intro I hI
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hI
    exact enclose_onGrid D F s schedule hD he x
  · intro I hI
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hI
    exact ⟨enclose_right_gt_lower D (2 ^ s) schedule hu hw he x,
      enclose_left_lt_upper D (2 ^ s) schedule hl hw he x⟩
  · exact h0
  · exact h1
  · exact hw x
  · omega

/-- The precision increment is exactly `log₂ E` for the actual word count. -/
theorem enumeration_log (s m : ℕ) : Nat.log 2 ((2 ^ s) ^ m) = s * m := by
  rw [← pow_mul, Nat.log_pow (by decide)]

theorem endpoint_precision_log (D : System ι ℚ) [Fintype ι] [DecidableEq ι]
    (F s : ℕ) (schedule : List ι) (hD : BoundsOnGrid D F)
    {I : ι → ℚ × ℚ} (hI : I ∈ enclose D (2 ^ s) schedule) (x : ι) :
    OnDyadicGrid (F + Nat.log 2 (enclose D (2 ^ s) schedule).length) (I x).1 ∧
    OnDyadicGrid (F + Nat.log 2 (enclose D (2 ^ s) schedule).length) (I x).2 := by
  rw [enclose_length, enumeration_log]
  exact enclose_onGrid D F s schedule hD hI x

/-- Reduction of a rational cannot enlarge either stored integer past the
common mesh denominator, when the position lies in the unit interval. -/
theorem rational_bits {q : ℚ} {F : ℕ} (hq : OnDyadicGrid F q)
    (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    q.den.size ≤ F + 1 ∧ q.num.natAbs.size ≤ F + 1 := by
  have hd : q.den ≤ 2 ^ F := Nat.le_of_dvd (by positivity) (onDyadicGrid_den_dvd hq)
  have hn0 : 0 ≤ q.num := Rat.num_nonneg.mpr h0
  have hnQ : (q.num : ℚ) ≤ q.den := by
    apply (div_le_one (by exact_mod_cast q.den_pos : (0 : ℚ) < q.den)).mp
    simpa only [Rat.num_div_den] using h1
  have hnZ : q.num ≤ (q.den : ℤ) := by exact_mod_cast hnQ
  have hn : q.num.natAbs ≤ q.den := by
    exact_mod_cast (show (q.num.natAbs : ℤ) ≤ (q.den : ℤ) by
      simpa only [Int.natCast_natAbs, abs_of_nonneg hn0] using hnZ)
  constructor
  · simpa only [Nat.size_pow] using Nat.size_le_size hd
  · simpa only [Nat.size_pow] using Nat.size_le_size (hn.trans hd)

end SortingAdversary.Continuous.Precision
