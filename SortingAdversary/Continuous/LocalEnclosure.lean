import SortingAdversary.Continuous.FiniteAveraging
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import SortingAdversary.Optimal.FiniteProbability

/-!
# Frozen boundaries and explicit finite enumeration

`maskedStep` performs an endpoint update only at an interior vertex. A coupled
full trajectory may update every vertex. The frozen endpoints still enclose
that full trajectory, for every sequence of digits, because a full update at
a boundary vertex remains between the original stored bounds.

`words` and `enclose` are executable enumerations. No existential oracle or
unspecified list is substituted for Algorithm `Enclose`.
-/

namespace SortingAdversary.Continuous.FiniteAveraging

section Boundary

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- At vertices outside the retained interior, the endpoint is frozen. -/
def maskedStep (D : System ι K) (S : ℕ) (F : Finset ι) (step : ι × Fin S)
    (Y : ι → K) : ι → K :=
  if step.1 ∈ F then update D S step.2 step.1 Y else Y

theorem maskedStep_frozen (D : System ι K) (S : ℕ) (F : Finset ι)
    (step : ι × Fin S) (Y : ι → K) (w : ι) (hw : w ∉ F) :
    maskedStep D S F step Y w = Y w := by
  unfold maskedStep
  split_ifs with hv
  · exact update_other D S step.2 step.1 w Y (fun h => hw (h ▸ hv))
  · rfl

/-- A full update and its two masked endpoint updates preserve a sandwich.
Only boundary bounds are needed when the full update is outside the interior. -/
theorem maskedStep_encloses (D : System ι K) (S : ℕ) (F : Finset ι)
    (step : ι × Fin S) {A Y B : ι → K} (hY : D.WeaklyFeasible Y)
    (hAY : ∀ w, A w ≤ Y w) (hYB : ∀ w, Y w ≤ B w)
    (hA : ∀ w ∉ F, A w = D.lower w) (hB : ∀ w ∉ F, B w = D.upper w) :
    ∀ w, maskedStep D S F step A w ≤ update D S step.2 step.1 Y w ∧
      update D S step.2 step.1 Y w ≤ maskedStep D S F step B w := by
  intro w
  by_cases hv : step.1 ∈ F
  · simp only [maskedStep, if_pos hv]
    exact ⟨update_mono D S step.2 step.1 hAY w,
      update_mono D S step.2 step.1 hYB w⟩
  · simp only [maskedStep, if_neg hv]
    by_cases hw : w = step.1
    · subst w
      have hnew := update_weaklyFeasible D S step.2 step.1 hY
      rw [hA _ hv, hB _ hv]
      exact hnew.1 step.1
    · rw [update_other D S step.2 step.1 w Y hw]
      exact ⟨hAY w, hYB w⟩

def fullSteps (D : System ι K) (S : ℕ) (steps : List (ι × Fin S))
    (Y : ι → K) : ι → K :=
  steps.foldl (fun Z step => update D S step.2 step.1 Z) Y

def maskedSteps (D : System ι K) (S : ℕ) (F : Finset ι) (steps : List (ι × Fin S))
    (Y : ι → K) : ι → K :=
  steps.foldl (fun Z step => maskedStep D S F step Z) Y

theorem maskedSteps_frozen (D : System ι K) (S : ℕ) (F : Finset ι)
    (steps : List (ι × Fin S)) (Y : ι → K) (w : ι) (hw : w ∉ F) :
    maskedSteps D S F steps Y w = Y w := by
  induction steps generalizing Y with
  | nil => rfl
  | cons step steps ih =>
    change maskedSteps D S F steps (maskedStep D S F step Y) w = Y w
    rw [ih, maskedStep_frozen D S F step Y w hw]

theorem maskedSteps_encloses_aux (D : System ι K) (S : ℕ) (F : Finset ι)
    (steps : List (ι × Fin S)) {A Y B : ι → K} (hY : D.WeaklyFeasible Y)
    (hAY : ∀ w, A w ≤ Y w) (hYB : ∀ w, Y w ≤ B w)
    (hA : ∀ w ∉ F, A w = D.lower w) (hB : ∀ w ∉ F, B w = D.upper w) :
    ∀ w, maskedSteps D S F steps A w ≤ fullSteps D S steps Y w ∧
      fullSteps D S steps Y w ≤ maskedSteps D S F steps B w := by
  induction steps generalizing A Y B with
  | nil => exact fun w => ⟨hAY w, hYB w⟩
  | cons step steps ih =>
    have hone := maskedStep_encloses D S F step hY hAY hYB hA hB
    apply ih (update_weaklyFeasible D S step.2 step.1 hY)
      (fun w => (hone w).1) (fun w => (hone w).2)
    · intro w hw
      rw [maskedStep_frozen D S F step A w hw, hA w hw]
    · intro w hw
      rw [maskedStep_frozen D S F step B w hw, hB w hw]

/-- The deterministic enclosure part of the paper's local interval theorem.
This allows arbitrary full updates outside the retained interior. -/
theorem maskedSteps_encloses (D : System ι K) (S : ℕ) (F : Finset ι)
    (steps : List (ι × Fin S)) {Y : ι → K} (hY : D.WeaklyFeasible Y) :
    ∀ w, maskedSteps D S F steps D.lower w ≤ fullSteps D S steps Y w ∧
      fullSteps D S steps Y w ≤ maskedSteps D S F steps D.upper w :=
  maskedSteps_encloses_aux D S F steps hY (fun w => (hY.1 w).1)
    (fun w => (hY.1 w).2) (fun _ _ => rfl) (fun _ _ => rfl)

end Boundary

/-- All words of length `m` in the alphabet `Fin S`, in lexicographic order.
Unlike a choice of an enumeration from `Fintype`, this is executable. -/
def words (S : ℕ) : (m : ℕ) → List (Fin m → Fin S)
  | 0 => [Fin.elim0]
  | m + 1 => (List.finRange S).flatMap fun j => (words S m).map (Fin.cons j)

@[simp] theorem words_length (S m : ℕ) : (words S m).length = S ^ m := by
  induction m with
  | zero => simp [words]
  | succ m ih =>
    simp [words, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

theorem mem_words {S m : ℕ} (digits : Fin m → Fin S) : digits ∈ words S m := by
  induction m with
  | zero =>
    have he : digits = Fin.elim0 := funext (fun i => Fin.elim0 i)
    simp [words, he]
  | succ m ih =>
    rw [words]
    apply List.mem_flatMap.mpr
    refine ⟨digits 0, by simp, ?_⟩
    apply List.mem_map.mpr
    refine ⟨Fin.tail digits, ih _, ?_⟩
    exact Fin.cons_self_tail digits

/-- Every digit assignment occurs exactly once. Output interval families
may repeat, as required by the paper's counting of list entries. -/
theorem words_nodup (S m : ℕ) : (words S m).Nodup := by
  classical
  have hall : (words S m).toFinset = Finset.univ := by
    ext digits
    simp [mem_words digits]
  have hcard : (words S m).toFinset.card = (words S m).length := by
    rw [hall, Finset.card_univ, words_length]
    simp
  exact (Multiset.toFinset_card_eq_card_iff_nodup (m := ⟦words S m⟧)).mp hcard

section Enumeration

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Attach one digit to each occurrence in an explicit update schedule. -/
def assignedSteps (S : ℕ) (schedule : List ι) (digits : Fin schedule.length → Fin S) :
    List (ι × Fin S) :=
  List.ofFn fun i => (schedule[i], digits i)

theorem assignedSteps_cons {S : ℕ} (x : ι) (xs : List ι)
    (digits : Fin (x :: xs).length → Fin S) :
    assignedSteps S (x :: xs) digits = (x, digits 0) :: assignedSteps S xs (Fin.tail digits) := by
  unfold assignedSteps
  rw [List.ofFn_succ]
  rfl

/-- The exact two endpoint calculations for one enumerated digit word. -/
def endpointEntry (D : System ι K) (S : ℕ) (schedule : List ι)
    (digits : Fin schedule.length → Fin S) : ι → K × K := fun x =>
  (fullSteps D S (assignedSteps S schedule digits) D.lower x,
    fullSteps D S (assignedSteps S schedule digits) D.upper x)

/-- Enumerate all endpoint entries. For `t` sweeps the caller supplies its
interior topological schedule repeated `t` times. Boundary vertices never
occur in that schedule. -/
def enclose (D : System ι K) (S : ℕ) (schedule : List ι) : List (ι → K × K) :=
  (words S schedule.length).map (endpointEntry D S schedule)

@[simp] theorem enclose_length (D : System ι K) (S : ℕ) (schedule : List ι) :
    (enclose D S schedule).length = S ^ schedule.length := by
  simp [enclose]

theorem enclose_repeated_length (D : System ι K) (S t : ℕ) (interior : List ι) :
    (enclose D S (List.replicate t interior).flatten).length = S ^ (interior.length * t) := by
  simp [List.length_flatten, Nat.mul_comm]

/-- Every possible shared digit history is actually present in the list. -/
theorem endpointEntry_mem (D : System ι K) (S : ℕ) (schedule : List ι)
    (digits : Fin schedule.length → Fin S) :
    endpointEntry D S schedule digits ∈ enclose D S schedule :=
  List.mem_map.mpr ⟨digits, mem_words digits, rfl⟩

theorem fullSteps_mono (D : System ι K) (S : ℕ) (steps : List (ι × Fin S))
    {Y Z : ι → K} (h : ∀ w, Y w ≤ Z w) :
    ∀ w, fullSteps D S steps Y w ≤ fullSteps D S steps Z w := by
  induction steps generalizing Y Z with
  | nil => exact h
  | cons step steps ih => exact ih (update_mono D S step.2 step.1 h)

theorem fullSteps_strict_lower (D : System ι K) (S : ℕ) (steps : List (ι × Fin S))
    {Y : ι → K} (hY : D.WeaklyFeasible Y) (hstrict : ∀ w, D.lower w < Y w) :
    ∀ w, D.lower w < fullSteps D S steps Y w := by
  induction steps generalizing Y with
  | nil => exact hstrict
  | cons step steps ih =>
    exact ih (update_weaklyFeasible D S step.2 step.1 hY)
      (update_strict_lower D S step.2 step.1 hY hstrict)

theorem fullSteps_strict_upper (D : System ι K) (S : ℕ) (steps : List (ι × Fin S))
    {Y : ι → K} (hY : D.WeaklyFeasible Y) (hstrict : ∀ w, Y w < D.upper w) :
    ∀ w, fullSteps D S steps Y w < D.upper w := by
  induction steps generalizing Y with
  | nil => exact hstrict
  | cons step steps ih =>
    exact ih (update_weaklyFeasible D S step.2 step.1 hY)
      (update_strict_upper D S step.2 step.1 hY hstrict)

/-- Every right endpoint remains strictly above its original lower wall. -/
theorem endpointEntry_right_gt_lower (D : System ι K) (S : ℕ) (schedule : List ι)
    (digits : Fin schedule.length → Fin S) (hupper : D.WeaklyFeasible D.upper)
    (hwidth : ∀ w, D.lower w < D.upper w) :
    ∀ w, D.lower w < (endpointEntry D S schedule digits w).2 :=
  fullSteps_strict_lower D S _ hupper hwidth

/-- Every left endpoint remains strictly below its original upper wall. -/
theorem endpointEntry_left_lt_upper (D : System ι K) (S : ℕ) (schedule : List ι)
    (digits : Fin schedule.length → Fin S) (hlower : D.WeaklyFeasible D.lower)
    (hwidth : ∀ w, D.lower w < D.upper w) :
    ∀ w, (endpointEntry D S schedule digits w).1 < D.upper w :=
  fullSteps_strict_upper D S _ hlower hwidth

theorem enclose_right_gt_lower (D : System ι K) (S : ℕ) (schedule : List ι)
    (hupper : D.WeaklyFeasible D.upper) (hwidth : ∀ w, D.lower w < D.upper w)
    {entry : ι → K × K} (hentry : entry ∈ enclose D S schedule) :
    ∀ w, D.lower w < (entry w).2 := by
  obtain ⟨digits, _, rfl⟩ := List.mem_map.mp hentry
  exact endpointEntry_right_gt_lower D S schedule digits hupper hwidth

theorem enclose_left_lt_upper (D : System ι K) (S : ℕ) (schedule : List ι)
    (hlower : D.WeaklyFeasible D.lower) (hwidth : ∀ w, D.lower w < D.upper w)
    {entry : ι → K × K} (hentry : entry ∈ enclose D S schedule) :
    ∀ w, (entry w).1 < D.upper w := by
  obtain ⟨digits, _, rfl⟩ := List.mem_map.mp hentry
  exact endpointEntry_left_lt_upper D S schedule digits hlower hwidth

theorem endpointEntry_encloses (D : System ι K) (S : ℕ) (schedule : List ι)
    (digits : Fin schedule.length → Fin S) {Y : ι → K} (hY : D.WeaklyFeasible Y) :
    ∀ w, (endpointEntry D S schedule digits w).1 ≤
        fullSteps D S (assignedSteps S schedule digits) Y w ∧
      fullSteps D S (assignedSteps S schedule digits) Y w ≤
        (endpointEntry D S schedule digits w).2 := by
  intro w
  exact ⟨fullSteps_mono D S _ (fun w => (hY.1 w).1) w,
    fullSteps_mono D S _ (fun w => (hY.1 w).2) w⟩

end Enumeration

section Precision

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual endpoint calculation adds at most `log₂ S` fractional digits
per scheduled update. This includes updates whose inputs are earlier outputs. -/
theorem fullSteps_onDyadicGrid (D : System ι ℚ) (F s : ℕ)
    (steps : List (ι × Fin (2 ^ s))) (Y : ι → ℚ)
    (hl : ∀ w, OnDyadicGrid F (D.lower w))
    (hu : ∀ w, OnDyadicGrid F (D.upper w)) (hY : ∀ w, OnDyadicGrid F (Y w)) :
    ∀ w, OnDyadicGrid (F + steps.length * s) (fullSteps D (2 ^ s) steps Y w) := by
  induction steps generalizing F Y with
  | nil => simpa [fullSteps] using hY
  | cons step steps ih =>
    have hnext := update_onDyadicGrid D F s step.2 step.1 Y (hl _) (hu _) hY
    have hrest := ih (F + s) (update D (2 ^ s) step.2 step.1 Y)
      (fun w => onDyadicGrid_add (hl w) s) (fun w => onDyadicGrid_add (hu w) s) hnext
    simpa [fullSteps, Nat.succ_mul, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrest

end Precision

section Contraction

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Eliminate predecessor terms in a finite-height directed recurrence.
Unlike the earlier integer-colour calculation, there is no additive rounding
loss in this continuous affine recurrence. -/
theorem contraction_of_rank {ι : Type*} (R : ι → ι → Prop)
    (rank : ι → ℕ) (hrank : ∀ {x y}, R x y → rank x < rank y)
    (p widths : ι → K) (floor bound : K)
    (hf0 : 0 ≤ floor) (hf1 : floor ≤ 1) (hbound : 0 ≤ bound)
    (hp : ∀ v, floor ≤ p v)
    (hstep : ∀ v E, 0 ≤ E → (∀ x, R x v → widths x ≤ E) →
      widths v ≤ p v * E + (1 - p v) * bound) :
    ∀ v, widths v ≤ (1 - floor ^ (rank v + 1)) * bound := by
  intro v
  induction hn : rank v using Nat.strong_induction_on generalizing v with
  | h n ih =>
    have hpow : 0 ≤ floor ^ n := pow_nonneg hf0 _
    have hpow1 : floor ^ n ≤ 1 := pow_le_one₀ hf0 hf1
    have hE : 0 ≤ (1 - floor ^ n) * bound := mul_nonneg (sub_nonneg.mpr hpow1) hbound
    have hpred : ∀ x, R x v → widths x ≤ (1 - floor ^ n) * bound := by
      intro x hx
      have hxn : rank x < n := hn ▸ hrank hx
      have hxbound := ih (rank x) hxn x rfl
      have hpower := pow_le_pow_of_le_one hf0 hf1 (Nat.succ_le_of_lt hxn)
      exact hxbound.trans (mul_le_mul_of_nonneg_right (sub_le_sub_left hpower 1) hbound)
    have h := hstep v _ hE hpred
    rw [pow_succ]
    have hterm := mul_le_mul_of_nonneg_right (hp v) (mul_nonneg hpow hbound)
    nlinarith

/-- Structural description of the predecessors and old-value dependencies
of one queried vertex. All fields concern finite graph membership or ranks. -/
structure SweepRegion {n : ℕ} (D : System (Fin n) K) (v : Fin n) (H : ℕ) where
  ancestors : Finset (Fin n)
  dependencies : Finset (Fin n)
  root_mem : v ∈ ancestors
  self_covered : ∀ x ∈ ancestors, x ∈ dependencies
  predecessor_closed : ∀ x ∈ ancestors, ∀ y, D.edge y x = true → y ∈ ancestors
  successor_covered : ∀ x ∈ ancestors, ∀ y, D.edge x y = true → y ∈ dependencies
  rank : Fin n → ℕ
  rank_strict : ∀ x ∈ ancestors, ∀ y ∈ ancestors,
    D.edge x y = true → rank x < rank y
  height : ∀ x ∈ ancestors, rank x + 1 ≤ H

/-- A contraction of the implemented full sweep, using any common lower
bound on the predecessor coefficients within the actual ancestor region. -/
theorem orderedSweep_contraction {n S : ℕ} (D : System (Fin n) K)
    (horder : ∀ x y, D.edge x y = true → x.val < y.val)
    (digits : Fin n → Fin S) (A B : Fin n → K) (v : Fin n) (H : ℕ)
    (region : SweepRegion D v H) (floor bound : K)
    (hf0 : 0 ≤ floor) (hf1 : floor ≤ 1) (hbound : 0 ≤ bound)
    (hcoeff : ∀ x ∈ region.ancestors,
      floor ≤ ((S : K) - 1 - (digits x).val) / S)
    (hdep : ∀ x ∈ region.dependencies, B x - A x ≤ bound) :
    orderedSweep D digits B v - orderedSweep D digits A v ≤
      (1 - floor ^ H) * bound := by
  let R : region.ancestors → region.ancestors → Prop :=
    fun x y => D.edge x.val y.val = true
  have hrank : ∀ {x y : region.ancestors}, R x y → region.rank x.val < region.rank y.val :=
    fun {x y} h => region.rank_strict x.val x.property y.val y.property h
  have h := contraction_of_rank R (fun x => region.rank x.val) hrank
    (fun x => ((S : K) - 1 - (digits x.val).val) / S)
    (fun x => orderedSweep D digits B x.val - orderedSweep D digits A x.val)
    floor bound hf0 hf1 hbound (fun x => hcoeff x.val x.property)
    (by
      intro x E hE hpred
      have hrec := orderedSweep_width_recurrence D horder digits A B x.val hE hbound
        (hdep _ (region.self_covered _ x.property))
        (by
          intro y hy
          exact hpred ⟨y, region.predecessor_closed _ x.property y hy⟩ hy)
        (fun y hy => hdep y (region.successor_covered _ x.property y hy))
      convert hrec using 1
      have hS0 : (S : K) ≠ 0 := ne_of_gt (alphabet_pos (K := K) (digits x.val))
      field_simp
      <;> ring)
  have hroot := h ⟨v, region.root_mem⟩
  have hpower := pow_le_pow_of_le_one hf0 hf1 (region.height v region.root_mem)
  exact hroot.trans (mul_le_mul_of_nonneg_right (sub_le_sub_left hpower 1) hbound)

/-- If no ancestor takes the last digit, every predecessor coefficient is
at least `1/S`, giving the paper's `1-S^{-H}` contraction. -/
theorem orderedSweep_good_contraction {n S : ℕ} (D : System (Fin n) K)
    (horder : ∀ x y, D.edge x y = true → x.val < y.val)
    (digits : Fin n → Fin S) (A B : Fin n → K) (v : Fin n) (H : ℕ)
    (region : SweepRegion D v H) (bound : K) (hbound : 0 ≤ bound)
    (hgood : ∀ x ∈ region.ancestors, (digits x).val + 1 < S)
    (hdep : ∀ x ∈ region.dependencies, B x - A x ≤ bound) :
    orderedSweep D digits B v - orderedSweep D digits A v ≤
      (1 - (1 / (S : K)) ^ H) * bound := by
  have hS := alphabet_pos (K := K) (digits v)
  have hS1 : (1 : K) ≤ S := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.zero_lt_of_lt (digits v).isLt))
  apply orderedSweep_contraction D horder digits A B v H region (1 / (S : K)) bound
    (by positivity) ((div_le_one hS).mpr hS1) hbound _ hdep
  intro x hx
  apply div_le_div_of_nonneg_right _ hS.le
  have hj : ((digits x).val : K) + 2 ≤ S := by
    exact_mod_cast Nat.succ_le_of_lt (hgood x hx)
  linarith

end Contraction

section FiniteMoments

open SortingAdversary.Optimal.FiniteProbability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ℕ} [NeZero S]

def BadDigits (C : Finset ι) (digits : ι → Fin S) : Prop :=
  ∃ x ∈ C, (digits x).val + 1 = S

instance (C : Finset ι) (digits : ι → Fin S) : Decidable (BadDigits C digits) :=
  inferInstanceAs (Decidable (∃ x ∈ C, (digits x).val + 1 = S))

/-- A fresh uniform digit is the last digit with probability exactly `1/S`. -/
theorem last_digit_probability : probability (fun j : Fin S => j.val + 1 = S) = 1 / S := by
  let last : Fin S := ⟨S - 1, Nat.sub_lt (NeZero.pos S) (by decide)⟩
  have hlast : last.val + 1 = S := by dsimp [last]; have := NeZero.pos S; omega
  have heq (j : Fin S) : j.val + 1 = S ↔ j = last := by
    constructor
    · intro hj
      apply Fin.ext
      omega
    · rintro rfl
      exact hlast
  have hfilter : Finset.univ.filter (fun j : Fin S => j.val + 1 = S) = {last} := by
    ext j
    simp [heq j]
  rw [probability_eq_card, hfilter, Fintype.card_fin]
  simp

/-- The bad event includes every ancestor, so adaptive choices of a
maximizing predecessor do not require any independence assumption. -/
theorem bad_digits_probability (C : Finset ι) :
    probability (BadDigits (S := S) C) ≤ (C.card : ℚ) / S := by
  apply (probability_exists_le_sum C (fun x (digits : ι → Fin S) => (digits x).val + 1 = S)).trans
  calc
    (∑ x ∈ C, probability (fun digits : ι → Fin S => (digits x).val + 1 = S))
        = ∑ _x ∈ C, probability (fun j : Fin S => j.val + 1 = S) := by
      apply Finset.sum_congr rfl
      intro x _
      exact mean_pi_apply x (indicator (fun j : Fin S => j.val + 1 = S))
    _ = (C.card : ℚ) / S := by rw [last_digit_probability]; simp [div_eq_mul_inv]
    _ ≤ (C.card : ℚ) / S := le_rfl

def sweepFactor (C : Finset ι) (H : ℕ) (digits : ι → Fin S) : ℚ :=
  if BadDigits C digits then 1 else 1 - (1 / (S : ℚ)) ^ H

theorem reciprocal_alphabet_mem : (0 : ℚ) ≤ 1 / S ∧ (1 : ℚ) / S ≤ 1 := by
  have hS : (0 : ℚ) < S := by exact_mod_cast NeZero.pos S
  have hS1 : (1 : ℚ) ≤ S := by exact_mod_cast NeZero.one_le
  exact ⟨by positivity, (div_le_one hS).mpr hS1⟩

theorem sweepFactor_mem (C : Finset ι) (H : ℕ) (digits : ι → Fin S) :
    0 ≤ sweepFactor C H digits ∧ sweepFactor C H digits ≤ 1 := by
  have hr := reciprocal_alphabet_mem (S := S)
  unfold sweepFactor
  split_ifs
  · exact ⟨zero_le_one, le_rfl⟩
  · exact ⟨sub_nonneg.mpr (pow_le_one₀ hr.1 hr.2), by nlinarith [pow_nonneg hr.1 H]⟩

set_option maxHeartbeats 1000000 in
theorem sweepFactor_moment (C : Finset ι) (H p : ℕ) :
    mean (fun digits : ι → Fin S => sweepFactor C H digits ^ p) ≤
      (C.card : ℚ) / S + (1 - (1 / (S : ℚ)) ^ H) ^ p := by
  have hr := reciprocal_alphabet_mem (S := S)
  have hc : 0 ≤ (1 - (1 / (S : ℚ)) ^ H) ^ p :=
    pow_nonneg (sub_nonneg.mpr (pow_le_one₀ hr.1 hr.2)) _
  have h := mean_le_bad_probability_add (BadDigits (S := S) C) hc
    (f := fun digits => sweepFactor C H digits ^ p)
    (fun digits => pow_le_one₀ (sweepFactor_mem C H digits).1 (sweepFactor_mem C H digits).2)
    (fun digits hd => by simp [sweepFactor, hd])
  exact h.trans (add_le_add (bad_digits_probability (S := S) C) le_rfl)

/-- The paper's explicit choices `S ≥ 4M²` and `β^p ≤ 1/(4M)` give the
coefficient moment `1/(2M)` on the actual finite product digit space. -/
theorem sweepFactor_moment_le (C : Finset ι) (H p M : ℕ) (hM : 0 < M)
    (hC : C.card ≤ M) (hS : 4 * M ^ 2 ≤ S)
    (hp : (1 - (1 / (S : ℚ)) ^ H) ^ p ≤ 1 / (4 * (M : ℚ))) :
    mean (fun digits : ι → Fin S => sweepFactor C H digits ^ p) ≤ 1 / (2 * (M : ℚ)) := by
  have hMr : (0 : ℚ) < M := by exact_mod_cast hM
  have hSr : (0 : ℚ) < S := by exact_mod_cast NeZero.pos S
  have hCr : (C.card : ℚ) ≤ M := by exact_mod_cast hC
  have hSr' : 4 * (M : ℚ) ^ 2 ≤ S := by exact_mod_cast hS
  have hfrac : (M : ℚ) / S ≤ 1 / (4 * (M : ℚ)) := by
    apply (div_le_div_iff₀ hSr (by positivity : (0 : ℚ) < 4 * M)).mpr
    nlinarith
  have h := sweepFactor_moment (S := S) C H p
  have hcfrac := (div_le_div_of_nonneg_right hCr hSr.le).trans hfrac
  have hdouble : (1 : ℚ) / (4 * M) + 1 / (4 * M) = 1 / (2 * M) := by
    field_simp
    <;> ring
  exact h.trans ((add_le_add hcfrac hp).trans_eq hdouble)

end FiniteMoments

section ActualMoments

open SortingAdversary.Optimal.FiniteProbability

variable {n S : ℕ} [NeZero S]

theorem orderedAfter_mono (D : System (Fin n) ℚ) (digits : Fin n → Fin S)
    {A B : Fin n → ℚ} (hAB : ∀ x, A x ≤ B x) (t : ℕ) :
    ∀ x, orderedAfter D digits A t x ≤ orderedAfter D digits B t x := by
  induction t with
  | zero => exact hAB
  | succ t ih =>
    simp only [orderedAfter]
    split_ifs with ht
    · exact update_mono D S (digits ⟨t, ht⟩) ⟨t, ht⟩ ih
    · exact ih

/-- Actual sweep contraction with the two-valued random factor of the paper. -/
theorem orderedSweep_factor (D : System (Fin n) ℚ)
    (horder : ∀ x y, D.edge x y = true → x.val < y.val)
    (digits : Fin n → Fin S) (A B : Fin n → ℚ) (v : Fin n) (H : ℕ)
    (region : SweepRegion D v H) (bound : ℚ) (hbound : 0 ≤ bound)
    (hdep : ∀ x ∈ region.dependencies, B x - A x ≤ bound) :
    orderedSweep D digits B v - orderedSweep D digits A v ≤
      sweepFactor region.ancestors H digits * bound := by
  have hS : (0 : ℚ) < S := by exact_mod_cast NeZero.pos S
  by_cases hb : BadDigits region.ancestors digits
  · have hH : 0 < H := by have := region.height v region.root_mem; omega
    have h := orderedSweep_contraction D horder digits A B v H region 0 bound
      le_rfl zero_le_one hbound (fun x _ => div_nonneg (lower_coefficient_nonneg (digits x)) hS.le) hdep
    simpa [sweepFactor, hb, zero_pow hH.ne'] using h
  · have hgood : ∀ x ∈ region.ancestors, (digits x).val + 1 < S := by
      intro x hx
      have hne : (digits x).val + 1 ≠ S := fun he => hb ⟨x, hx, he⟩
      have hj := (digits x).isLt
      omega
    simpa [sweepFactor, hb] using
      orderedSweep_good_contraction D horder digits A B v H region bound hbound hgood hdep

def maxWidth (C : Finset (Fin n)) (A B : Fin n → ℚ) : ℚ :=
  C.fold max 0 (fun x => B x - A x)

theorem maxWidth_nonneg (C : Finset (Fin n)) (A B : Fin n → ℚ) : 0 ≤ maxWidth C A B :=
  (Finset.le_fold_max _).mpr (Or.inl le_rfl)

theorem le_maxWidth (C : Finset (Fin n)) (A B : Fin n → ℚ) {x : Fin n} (hx : x ∈ C) :
    B x - A x ≤ maxWidth C A B :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨x, hx, le_rfl⟩)

theorem maxWidth_attained (C : Finset (Fin n)) (A B : Fin n → ℚ) :
    maxWidth C A B = 0 ∨ ∃ x ∈ C, maxWidth C A B = B x - A x := by
  induction C using Finset.induction_on with
  | empty => simp [maxWidth]
  | @insert x C hx ih =>
    simp only [maxWidth, Finset.fold_insert_idem]
    rcases max_choice (B x - A x) (maxWidth C A B) with h | h
    · exact Or.inr ⟨x, Finset.mem_insert_self _ _, h⟩
    · rcases ih with ih | ⟨y, hy, ih⟩
      · exact Or.inl (h.trans ih)
      · exact Or.inr ⟨y, Finset.mem_insert_of_mem hy, h.trans ih⟩

theorem maxWidth_power_le_sum (C : Finset (Fin n)) (A B : Fin n → ℚ)
    (hAB : ∀ x, A x ≤ B x) (p : ℕ) (hp : 0 < p) :
    maxWidth C A B ^ p ≤ ∑ x ∈ C, (B x - A x) ^ p := by
  rcases maxWidth_attained C A B with hz | ⟨x, hx, he⟩
  · rw [hz, zero_pow hp.ne']
    exact Finset.sum_nonneg (fun x _ => pow_nonneg (sub_nonneg.mpr (hAB x)) p)
  · rw [he]
    exact Finset.single_le_sum (fun x _ => pow_nonneg (sub_nonneg.mpr (hAB x)) p) hx

/-- The pointwise pth-moment estimate is derived from the implemented sweep,
not assumed as an input to an abstract stochastic process. -/
theorem orderedSweep_power_le (D : System (Fin n) ℚ)
    (horder : ∀ x y, D.edge x y = true → x.val < y.val)
    (digits : Fin n → Fin S) (A B : Fin n → ℚ) (hAB : ∀ x, A x ≤ B x)
    (v : Fin n) (H p : ℕ) (hp : 0 < p) (region : SweepRegion D v H) :
    (orderedSweep D digits B v - orderedSweep D digits A v) ^ p ≤
      (∑ x ∈ region.dependencies, (B x - A x) ^ p) * sweepFactor region.ancestors H digits ^ p := by
  have hstep := orderedSweep_factor D horder digits A B v H region
    (maxWidth region.dependencies A B) (maxWidth_nonneg _ _ _) (fun x hx => le_maxWidth _ _ _ hx)
  have hnonneg : 0 ≤ orderedSweep D digits B v - orderedSweep D digits A v :=
    sub_nonneg.mpr (orderedAfter_mono D digits hAB n v)
  have hpower := pow_le_pow_left₀ hnonneg hstep p
  rw [mul_pow] at hpower
  have hsum := maxWidth_power_le_sum region.dependencies A B hAB p hp
  have hmul := mul_le_mul_of_nonneg_right hsum
    (pow_nonneg (sweepFactor_mem region.ancestors H digits).1 p)
  nlinarith

/-- Fresh digits form a Cartesian product with the old sample space.
Consequently the actual sweep halves every local pth moment under exactly
the paper's alphabet, height, and moment-parameter inequalities. -/
theorem orderedSweep_moment {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (D : System (Fin n) ℚ)
    (horder : ∀ x y, D.edge x y = true → x.val < y.val)
    (A B : Ω → Fin n → ℚ) (hAB : ∀ ω x, A ω x ≤ B ω x)
    (v : Fin n) (H p M : ℕ) (hp : 0 < p) (hM : 0 < M)
    (region : SweepRegion D v H)
    (hanc : region.ancestors.card ≤ M) (hdep : region.dependencies.card ≤ M)
    (hS : 4 * M ^ 2 ≤ S)
    (hpower : (1 - (1 / (S : ℚ)) ^ H) ^ p ≤ 1 / (4 * (M : ℚ)))
    (W : ℚ) (hW : 0 ≤ W)
    (hold : ∀ x ∈ region.dependencies, mean (fun ω => (B ω x - A ω x) ^ p) ≤ W) :
    mean (fun sample : Ω × (Fin n → Fin S) =>
      (orderedSweep D sample.2 (B sample.1) v - orderedSweep D sample.2 (A sample.1) v) ^ p) ≤ W / 2 := by
  let F : Ω → ℚ := fun ω => ∑ x ∈ region.dependencies, (B ω x - A ω x) ^ p
  let G : (Fin n → Fin S) → ℚ := fun digits => sweepFactor region.ancestors H digits ^ p
  have hF : mean F ≤ (M : ℚ) * W := by
    unfold F
    rw [mean_sum]
    calc
      _ ≤ ∑ _x ∈ region.dependencies, W := Finset.sum_le_sum (fun x hx => hold x hx)
      _ = (region.dependencies.card : ℚ) * W := by simp
      _ ≤ (M : ℚ) * W := mul_le_mul_of_nonneg_right (by exact_mod_cast hdep) hW
  have hG0 : 0 ≤ mean G := mean_nonneg (fun digits =>
    pow_nonneg (sweepFactor_mem region.ancestors H digits).1 p)
  have hG : mean G ≤ 1 / (2 * (M : ℚ)) := sweepFactor_moment_le
    region.ancestors H p M hM hanc hS hpower
  have hpoint := mean_mono (fun sample : Ω × (Fin n → Fin S) =>
    orderedSweep_power_le D horder sample.2 (A sample.1) (B sample.1) (hAB sample.1) v H p hp region)
  change _ ≤ mean (fun sample : Ω × (Fin n → Fin S) => F sample.1 * G sample.2) at hpoint
  rw [mean_independent_mul] at hpoint
  have h1 := mul_le_mul_of_nonneg_right hF hG0
  have h2 := mul_le_mul_of_nonneg_left hG (show 0 ≤ (M : ℚ) * W by positivity)
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have he : (M : ℚ) * W * (1 / (2 * (M : ℚ))) = W / 2 := by field_simp
  exact hpoint.trans (h1.trans (h2.trans_eq he))

end ActualMoments

section IteratedMoments

open SortingAdversary.Optimal.FiniteProbability

/-- An explicit independent digit family at every sweep. -/
def SweepHistory (n S : ℕ) : ℕ → Type
  | 0 => PUnit
  | t + 1 => SweepHistory n S t × (Fin n → Fin S)

instance sweepHistoryFintype (n S t : ℕ) : Fintype (SweepHistory n S t) := by
  induction t with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ t ih =>
    letI := ih
    exact inferInstanceAs (Fintype (SweepHistory n S t × (Fin n → Fin S)))

instance sweepHistoryNonempty (n S t : ℕ) [NeZero S] : Nonempty (SweepHistory n S t) := by
  induction t with
  | zero => exact inferInstanceAs (Nonempty PUnit)
  | succ t ih =>
    letI := ih
    exact inferInstanceAs (Nonempty (SweepHistory n S t × (Fin n → Fin S)))

variable {n S : ℕ} [NeZero S]

def iterateSweep (D : System (Fin n) ℚ) (initial : Fin n → ℚ) :
    (t : ℕ) → SweepHistory n S t → Fin n → ℚ
  | 0 => fun _ => initial
  | t + 1 => fun history => orderedSweep D history.2 (iterateSweep D initial t history.1)

theorem iterateSweep_mono (D : System (Fin n) ℚ) {A B : Fin n → ℚ}
    (hAB : ∀ x, A x ≤ B x) (t : ℕ) (history : SweepHistory n S t) :
    ∀ x, iterateSweep D A t history x ≤ iterateSweep D B t history x := by
  induction t with
  | zero => exact hAB
  | succ t ih =>
    exact orderedAfter_mono D history.2 (ih history.1) n

/-- The pth moments of the actual full-graph endpoint calculation decay as
`2^{-t}`. The finite histories explicitly supply fresh independent digits. -/
theorem iterateSweep_moment (D : System (Fin n) ℚ)
    (horder : ∀ x y, D.edge x y = true → x.val < y.val)
    (A B : Fin n → ℚ) (hAB : ∀ x, A x ≤ B x) (hunit : ∀ x, B x - A x ≤ 1)
    (H p M : ℕ) (hp : 0 < p) (hM : 0 < M)
    (regions : ∀ v, SweepRegion D v H)
    (hanc : ∀ v, (regions v).ancestors.card ≤ M)
    (hdep : ∀ v, (regions v).dependencies.card ≤ M)
    (hS : 4 * M ^ 2 ≤ S)
    (hpower : (1 - (1 / (S : ℚ)) ^ H) ^ p ≤ 1 / (4 * (M : ℚ)))
    (t : ℕ) : ∀ v, mean (fun history : SweepHistory n S t =>
      (iterateSweep D B t history v - iterateSweep D A t history v) ^ p) ≤ (1 / 2 : ℚ) ^ t := by
  induction t with
  | zero =>
    intro v
    simpa [iterateSweep] using pow_le_one₀ (sub_nonneg.mpr (hAB v)) (hunit v) (n := p)
  | succ t ih =>
    intro v
    have h := orderedSweep_moment D horder (iterateSweep D A t) (iterateSweep D B t)
      (fun history => iterateSweep_mono D hAB t history) v H p M hp hM (regions v)
      (hanc v) (hdep v) hS hpower ((1 / 2 : ℚ) ^ t) (by positivity)
      (fun x _ => ih x)
    have hmean : mean (fun history : SweepHistory n S (t + 1) =>
        (iterateSweep D B (t + 1) history v - iterateSweep D A (t + 1) history v) ^ p) =
        mean (fun sample : SweepHistory n S t × (Fin n → Fin S) =>
          (orderedSweep D sample.2 (iterateSweep D B t sample.1) v -
            orderedSweep D sample.2 (iterateSweep D A t sample.1) v) ^ p) :=
      mean_congr_fintype _ _ (fun _ => rfl)
    rw [hmean]
    simpa [pow_succ, div_eq_mul_inv] using h

/-- Markov's inequality for one endpoint width, derived from the actual
history process and the preceding moment theorem. -/
theorem iterateSweep_width_probability (D : System (Fin n) ℚ)
    (horder : ∀ x y, D.edge x y = true → x.val < y.val)
    (A B : Fin n → ℚ) (hAB : ∀ x, A x ≤ B x) (hunit : ∀ x, B x - A x ≤ 1)
    (H p M : ℕ) (hp : 0 < p) (hM : 0 < M)
    (regions : ∀ v, SweepRegion D v H)
    (hanc : ∀ v, (regions v).ancestors.card ≤ M)
    (hdep : ∀ v, (regions v).dependencies.card ≤ M)
    (hS : 4 * M ^ 2 ≤ S)
    (hpower : (1 - (1 / (S : ℚ)) ^ H) ^ p ≤ 1 / (4 * (M : ℚ)))
    (t : ℕ) (v : Fin n) (δ : ℚ) (hδ : 0 < δ) :
    probability (fun history : SweepHistory n S t =>
      δ < iterateSweep D B t history v - iterateSweep D A t history v) ≤
        (1 / 2 : ℚ) ^ t / δ ^ p := by
  have hmono := probability_mono
    (P := fun history : SweepHistory n S t =>
      δ < iterateSweep D B t history v - iterateSweep D A t history v)
    (Q := fun history : SweepHistory n S t =>
      δ ^ p < (iterateSweep D B t history v - iterateSweep D A t history v) ^ p)
    (fun _ h => pow_lt_pow_left₀ h hδ.le hp.ne')
  have hmarkov := probability_le_mean_div
    (fun history : SweepHistory n S t => pow_nonneg
      (sub_nonneg.mpr (iterateSweep_mono D hAB t history v)) p) (pow_pos hδ p)
  have hm := iterateSweep_moment D horder A B hAB hunit H p M hp hM regions hanc hdep hS hpower t v
  exact hmono.trans (hmarkov.trans (div_le_div_of_nonneg_right hm (pow_pos hδ p).le))

end IteratedMoments

section Stationarity

open MeasureTheory
open scoped Interval

/-- Averaging the `S` affine branches preserves Lebesgue integration on a
conditional interval. This is the continuous single-coordinate stationarity
identity used in the paper: the image intervals tile the original interval.
It is proved for arbitrary integrable test functions, not merely for moments. -/
theorem digit_integral_stationary (S : ℕ) (hS : 0 < S) {l u : ℝ} (hlu : l < u)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume l u) :
    (∑ j : Fin S, ∫ y in l..u, f (digit S j y l u)) / (S : ℝ) =
      ∫ y in l..u, f y := by
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  have hS0 : (S : ℝ) ≠ 0 := ne_of_gt hSr
  let a : ℕ → ℝ := fun i => l + (u - l) * i / S
  have ha0 : a 0 = l := by simp [a]
  have haS : a S = u := by simp [a, hS0]
  have ha_mem (i : ℕ) (hi : i ≤ S) : a i ∈ Set.Icc l u := by
    have hir : (i : ℝ) ≤ S := by exact_mod_cast hi
    have hin : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have hw : 0 ≤ u - l := sub_nonneg.mpr hlu.le
    have hright : (u - l) * i / S ≤ u - l := by
      apply (div_le_iff₀ hSr).mpr
      exact mul_le_mul_of_nonneg_left hir hw
    have hleft : 0 ≤ (u - l) * i / S := by positivity
    constructor <;> dsimp [a] <;> linarith
  have hint (i : ℕ) (hi : i < S) : IntervalIntegrable f volume (a i) (a (i + 1)) := by
    apply hf.mono_set
    apply Set.uIcc_subset_uIcc
    · simpa [Set.uIcc_of_le hlu.le] using ha_mem i hi.le
    · simpa [Set.uIcc_of_le hlu.le] using ha_mem (i + 1) (Nat.succ_le_of_lt hi)
  have htile : (∑ i ∈ Finset.range S, ∫ y in a i..a (i + 1), f y) =
      ∫ y in l..u, f y := by
    simpa [ha0, haS] using intervalIntegral.sum_integral_adjacent_intervals hint
  have hbranch (j : Fin S) :
      (∫ y in l..u, f (digit S j y l u)) =
        (S : ℝ) * ∫ y in a j.val..a (j.val + 1), f y := by
    let d : ℝ := (((S : ℝ) - 1 - j.val) * l + j.val * u) / S
    have hformula (y : ℝ) : digit S j y l u = y / S + d := by
      dsimp [digit, d]
      ring
    simp_rw [hformula]
    have h := intervalIntegral.integral_comp_div_add f hS0 d (a := l) (b := u)
    have hlo : l / S + d = a j.val := by
      dsimp [d, a]
      field_simp
      <;> ring
    have hhi : u / S + d = a (j.val + 1) := by
      dsimp [d, a]
      push_cast
      field_simp
      <;> ring
    rw [hlo, hhi] at h
    simpa only [smul_eq_mul] using h
  simp_rw [hbranch]
  rw [← Finset.mul_sum, mul_div_cancel_left₀ _ hS0,
    Fin.sum_univ_eq_sum_range (fun i : ℕ => ∫ y in a i..a (i + 1), f y)]
  exact htile

/-- Uniform probability has density `1/(u-l)`, so the same identity holds
for normalized conditional expectations. -/
theorem digit_uniform_expectation (S : ℕ) (hS : 0 < S) {l u : ℝ} (hlu : l < u)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume l u) :
    ((∑ j : Fin S, ∫ y in l..u, f (digit S j y l u)) / S) / (u - l) =
      (∫ y in l..u, f y) / (u - l) := by
  rw [digit_integral_stationary S hS hlu f hf]

end Stationarity

end SortingAdversary.Continuous.FiniteAveraging
