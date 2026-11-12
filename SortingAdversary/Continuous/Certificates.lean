import SortingAdversary.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Int.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite interval certificates for the continuous construction

These routines consume the rational interval lists produced by `Enclose`.
They do not call a real-valued probability oracle.  An answer is certified
by counting strictly separated intervals.  `centralInterval` uses the two
order statistics in the paper, counting repetitions in the input list.

The soundness lemmas below separate these finite calculations from the
continuous coupling theorem: enclosure implies the corresponding order or
region membership pointwise, and hence for every probability distribution
coupled to the intervals.  The existence of that continuous coupling is a
separate obligation, not an assumption concealed in the executable code.
-/

namespace SortingAdversary.Continuous.Certificates

abbrev Interval := ℚ × ℚ
abbrev ComparisonIntervals := Interval × Interval

def Interval.Contains (I : Interval) (x : ℝ) : Prop :=
  (I.1 : ℝ) ≤ x ∧ x ≤ (I.2 : ℝ)

def separated (I : ComparisonIntervals) : Bool := decide (I.1.2 < I.2.1)

def reverseSeparated (I : ComparisonIntervals) : Bool := decide (I.2.2 < I.1.1)

/-- The fraction of entries certifying the first queried position is smaller. -/
def lowerFraction (L : List ComparisonIntervals) : ℚ :=
  (L.countP separated : ℚ) / L.length

/-- The fraction of entries certifying the reverse answer. -/
def upperFraction (L : List ComparisonIntervals) : ℚ :=
  (L.countP reverseSeparated : ℚ) / L.length

/-- The answer branch of `Select`, including the paper's tie rule.
`none` asks the caller to refine the smallest queried label.
The guard on empty lists makes malformed external inputs fail safely. -/
def selectAnswer (k : ℕ) (L : List ComparisonIntervals) : Option Answer :=
  if L.isEmpty then none else
  let p := lowerFraction L
  let q := upperFraction L
  if max p q < 1 / 2 - 1 / (100 * (k : ℚ)) then none
  else if q ≤ p then some .less else some .greater

theorem separated_sound {I : ComparisonIntervals} {x y : ℝ}
    (hx : I.1.Contains x) (hy : I.2.Contains y) (h : separated I = true) : x < y := by
  have hq : I.1.2 < I.2.1 := of_decide_eq_true h
  have hr : (I.1.2 : ℝ) < I.2.1 := by exact_mod_cast hq
  exact lt_of_le_of_lt hx.2 (lt_of_lt_of_le hr hy.1)

theorem reverseSeparated_sound {I : ComparisonIntervals} {x y : ℝ}
    (hx : I.1.Contains x) (hy : I.2.Contains y)
    (h : reverseSeparated I = true) : y < x := by
  have hq : I.2.2 < I.1.1 := of_decide_eq_true h
  have hr : (I.2.2 : ℝ) < I.1.1 := by exact_mod_cast hq
  exact lt_of_le_of_lt hy.2 (lt_of_lt_of_le hr hx.1)

/-- Overlapping narrow enclosures can hide only a small difference.
This is the pointwise input to the paper's anti-concentration estimate. -/
theorem unresolved_close {I : ComparisonIntervals} {x y : ℝ} {δ : ℚ}
    (hx : I.1.Contains x) (hy : I.2.Contains y)
    (hwx : I.1.2 - I.1.1 ≤ δ) (hwy : I.2.2 - I.2.1 ≤ δ)
    (h₁ : separated I = false) (h₂ : reverseSeparated I = false) :
    |x - y| ≤ 2 * (δ : ℝ) := by
  have ho₁ : I.2.1 ≤ I.1.2 := le_of_not_gt (of_decide_eq_false h₁)
  have ho₂ : I.1.1 ≤ I.2.2 := le_of_not_gt (of_decide_eq_false h₂)
  have hr₁ : (I.2.1 : ℝ) ≤ I.1.2 := by exact_mod_cast ho₁
  have hr₂ : (I.1.1 : ℝ) ≤ I.2.2 := by exact_mod_cast ho₂
  have hrx : (I.1.2 : ℝ) - I.1.1 ≤ δ := by exact_mod_cast hwx
  have hry : (I.2.2 : ℝ) - I.2.1 ≤ δ := by exact_mod_cast hwy
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem lowerFraction_nonneg (L : List ComparisonIntervals) : 0 ≤ lowerFraction L := by
  unfold lowerFraction
  positivity

theorem upperFraction_nonneg (L : List ComparisonIntervals) : 0 ≤ upperFraction L := by
  unfold upperFraction
  positivity

theorem lowerFraction_le_one (L : List ComparisonIntervals) : lowerFraction L ≤ 1 := by
  unfold lowerFraction
  by_cases h : L.length = 0
  · simp [h]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)).2
    exact_mod_cast (List.countP_le_length (p := separated) (l := L))

theorem upperFraction_le_one (L : List ComparisonIntervals) : upperFraction L ≤ 1 := by
  unfold upperFraction
  by_cases h : L.length = 0
  · simp [h]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)).2
    exact_mod_cast (List.countP_le_length (p := reverseSeparated) (l := L))

/-- Every returned answer has the advertised finite lower certificate. -/
theorem selectAnswer_certificate (k : ℕ) (L : List ComparisonIntervals) (a : Answer)
    (h : selectAnswer k L = some a) :
    1 / 2 - 1 / (100 * (k : ℚ)) ≤
      match a with
      | .less => lowerFraction L
      | .greater => upperFraction L := by
  unfold selectAnswer at h
  split at h
  · contradiction
  · dsimp only at h
    split at h
    · contradiction
    · rename_i hcert
      have hc := le_of_not_gt hcert
      split at h
      · rename_i horder
        cases h
        simpa only [max_eq_left horder] using hc
      · rename_i horder
        cases h
        simpa only [max_eq_right (le_of_lt (lt_of_not_ge horder))] using hc

/-- A sufficiently small unresolved fraction forces a successful answer.
This is the numerical implication used after the small-difference bound. -/
theorem selectAnswer_succeeds (k : ℕ) (L : List ComparisonIntervals)
    (hne : L ≠ [])
    (hmass : 1 - 1 / (100 * (k : ℚ)) ≤ lowerFraction L + upperFraction L) :
    ∃ a, selectAnswer k L = some a := by
  have heta : 0 ≤ 1 / (100 * (k : ℚ)) := by positivity
  have hmax : 1 / 2 - 1 / (100 * (k : ℚ)) ≤
      max (lowerFraction L) (upperFraction L) := by
    have h₁ := le_max_left (lowerFraction L) (upperFraction L)
    have h₂ := le_max_right (lowerFraction L) (upperFraction L)
    linarith
  simp only [selectAnswer, List.isEmpty_iff, hne, ↓reduceIte, not_lt.mpr hmax]
  split
  · exact ⟨.less, rfl⟩
  · exact ⟨.greater, rfl⟩

/-- Bounds needed by the comparison calibration, with the constants as printed. -/
theorem calibration {η w B : ℚ} (hw : 0 < w) (hB : 0 ≤ B) :
    η / 2 + 4 * (B + 1) * (η * w / (8 * (B + 1))) / w = η ∧
    η / 2 + 2 * (B + 1) * (η * w / (8 * (B + 1))) / w = 3 * η / 4 := by
  have hB' : B + 1 ≠ 0 := by linarith
  constructor <;> field_simp <;> ring

def leftCount (L : List Interval) (u : ℚ) : ℕ :=
  L.countP (fun I => decide (I.2 ≤ u))

def rightCount (L : List Interval) (v : ℚ) : ℕ :=
  L.countP (fun I => decide (v ≤ I.1))

def insideCount (L : List Interval) (J : Interval) : ℕ :=
  L.countP (fun I => decide (J.1 ≤ I.1 ∧ I.2 ≤ J.2))

def crossingCount (L : List Interval) (c : ℚ) : ℕ :=
  L.countP (fun I => decide (I.1 ≤ c ∧ c ≤ I.2))

private theorem countP_cover_le {α : Type*} (L : List α) (p q r : α → Bool)
    (h : ∀ x ∈ L, p x = true → q x = true ∨ r x = true) :
    L.countP p ≤ L.countP q + L.countP r := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.countP_cons]
    cases hp : p x <;> cases hq : q x <;> cases hr : r x <;>
      simp_all <;> omega

private theorem sorted_count_lt_pivot (L : List ℚ) (hs : L.SortedLE)
    (i : ℕ) (hi : i < L.length) :
    L.countP (fun x => decide (x < L[i])) ≤ i := by
  have hz : (L.drop i).countP (fun x => decide (x < L[i])) = 0 := by
    apply List.countP_eq_zero.mpr
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp hx
    have ho : L[i] ≤ L[i + j] :=
      hs.getElem_le_getElem_of_le (show i ≤ i + j by omega)
    simpa only [decide_eq_true_eq] using not_lt.mpr ho
  have heq := List.countP_append (p := fun x => decide (x < L[i]))
    (l₁ := L.take i) (l₂ := L.drop i)
  rw [List.take_append_drop, hz, Nat.add_zero] at heq
  rw [heq]
  exact (List.countP_le_length).trans (by simp)

private theorem sorted_count_gt_pivot (L : List ℚ) (hs : L.SortedLE)
    (i : ℕ) (hi : i < L.length) :
    L.countP (fun x => decide (L[i] < x)) ≤ L.length - (i + 1) := by
  have hz : (L.take (i + 1)).countP (fun x => decide (L[i] < x)) = 0 := by
    apply List.countP_eq_zero.mpr
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hx
    have ho : L[j] ≤ L[i] := hs.getElem_le_getElem_of_le (show j ≤ i by omega)
    simpa only [decide_eq_true_eq] using not_lt.mpr ho
  have heq := List.countP_append (p := fun x => decide (L[i] < x))
    (l₁ := L.take (i + 1)) (l₂ := L.drop (i + 1))
  rw [List.take_append_drop, hz, Nat.zero_add] at heq
  rw [heq]
  exact (List.countP_le_length).trans (by simp)

/-- One-based `N/4`-th upper and `3N/4`-th lower endpoints.
Defaults are used only for malformed lists, rejected by `centralInterval`. -/
def centralCandidate (L : List Interval) : Interval :=
  let uppers := (L.map Prod.snd).mergeSort (· ≤ ·)
  let lowers := (L.map Prod.fst).mergeSort (· ≤ ·)
  (uppers[L.length / 4 - 1]?.getD 0,
   lowers[3 * L.length / 4 - 1]?.getD 0)

/-- The paper's `CentralInterval`. Its list has a positive length divisible
by four; the first guard explicitly rejects inputs violating that interface. -/
def centralInterval (L : List Interval) : Option Interval :=
  if L.length = 0 ∨ ¬ 4 ∣ L.length then none else
  let J := centralCandidate L
  if J.1 < J.2 ∧ L.length ≤ 4 * insideCount L J then some J else none

private theorem sorted_count_le_pivot (L : List ℚ) (hs : L.SortedLE)
    (i : ℕ) (hi : i < L.length) :
    i + 1 ≤ L.countP (fun x => decide (x ≤ L[i])) := by
  have htake : (L.take (i + 1)).countP (fun x => decide (x ≤ L[i])) =
      (L.take (i + 1)).length := by
    apply List.countP_eq_length.mpr
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hx
    exact decide_eq_true (hs.getElem_le_getElem_of_le (by omega))
  have hmono := (List.take_sublist (i + 1) L).countP_le
    (p := fun x => decide (x ≤ L[i]))
  rw [htake, List.length_take, min_eq_left (by omega)] at hmono
  exact hmono

private theorem sorted_count_ge_pivot (L : List ℚ) (hs : L.SortedLE)
    (i : ℕ) (hi : i < L.length) :
    L.length - i ≤ L.countP (fun x => decide (L[i] ≤ x)) := by
  have hdrop : (L.drop i).countP (fun x => decide (L[i] ≤ x)) =
      (L.drop i).length := by
    apply List.countP_eq_length.mpr
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp hx
    exact decide_eq_true (hs.getElem_le_getElem_of_le (by omega))
  have hmono := (List.drop_sublist i L).countP_le
    (p := fun x => decide (L[i] ≤ x))
  simpa only [hdrop, List.length_drop] using hmono

/-- The two tail certificates follow from the actual sorted-list ranks.
Repeated endpoints are allowed; no distinctness hypothesis is needed. -/
theorem centralCandidate_tails (L : List Interval) (hpos : 0 < L.length)
    (hfour : 4 ∣ L.length) :
    L.length ≤ 4 * leftCount L (centralCandidate L).1 ∧
    L.length ≤ 4 * rightCount L (centralCandidate L).2 := by
  let U := (L.map Prod.snd).mergeSort (· ≤ ·)
  let A := (L.map Prod.fst).mergeSort (· ≤ ·)
  have hu : U.length = L.length := by simp [U]
  have ha : A.length = L.length := by simp [A]
  have hm : L.length % 4 = 0 := Nat.mod_eq_zero_of_dvd hfour
  have hi : L.length / 4 - 1 < U.length := by omega
  have hj : 3 * L.length / 4 - 1 < A.length := by omega
  have huget : (centralCandidate L).1 = U[L.length / 4 - 1] := by
    simp [centralCandidate, U, List.getElem?_eq_getElem hi]
  have haget : (centralCandidate L).2 = A[3 * L.length / 4 - 1] := by
    simp [centralCandidate, A, List.getElem?_eq_getElem hj]
  have hp := sorted_count_le_pivot U (List.sortedLE_mergeSort (l := L.map Prod.snd)) _ hi
  have hq := sorted_count_ge_pivot A (List.sortedLE_mergeSort (l := L.map Prod.fst)) _ hj
  have hp' : U.countP (fun x => decide (x ≤ U[L.length / 4 - 1])) =
      leftCount L (centralCandidate L).1 := by
    rw [huget]
    unfold leftCount
    simpa only [List.countP_map, Function.comp_def] using
      List.Perm.countP_eq (fun x => decide (x ≤ U[L.length / 4 - 1]))
        (List.mergeSort_perm (L.map Prod.snd) (· ≤ ·))
  have hq' : A.countP (fun x => decide (A[3 * L.length / 4 - 1] ≤ x)) =
      rightCount L (centralCandidate L).2 := by
    rw [haget]
    unfold rightCount
    simpa only [List.countP_map, Function.comp_def] using
      List.Perm.countP_eq (fun x => decide (A[3 * L.length / 4 - 1] ≤ x))
        (List.mergeSort_perm (L.map Prod.fst) (· ≤ ·))
  rw [hp'] at hp
  rw [hq', ha] at hq
  constructor <;> omega

private theorem centralCandidate_strict_tails (L : List Interval) (hpos : 0 < L.length)
    (hfour : 4 ∣ L.length) :
    4 * L.countP (fun I => decide (I.2 < (centralCandidate L).1)) ≤ L.length ∧
    4 * L.countP (fun I => decide ((centralCandidate L).2 < I.1)) ≤ L.length := by
  let U := (L.map Prod.snd).mergeSort (· ≤ ·)
  let A := (L.map Prod.fst).mergeSort (· ≤ ·)
  have hu : U.length = L.length := by simp [U]
  have ha : A.length = L.length := by simp [A]
  have hm : L.length % 4 = 0 := Nat.mod_eq_zero_of_dvd hfour
  have hi : L.length / 4 - 1 < U.length := by omega
  have hj : 3 * L.length / 4 - 1 < A.length := by omega
  have huget : (centralCandidate L).1 = U[L.length / 4 - 1] := by
    simp [centralCandidate, U, List.getElem?_eq_getElem hi]
  have haget : (centralCandidate L).2 = A[3 * L.length / 4 - 1] := by
    simp [centralCandidate, A, List.getElem?_eq_getElem hj]
  have hp := sorted_count_lt_pivot U (List.sortedLE_mergeSort (l := L.map Prod.snd)) _ hi
  have hq := sorted_count_gt_pivot A (List.sortedLE_mergeSort (l := L.map Prod.fst)) _ hj
  have hp' : U.countP (fun x => decide (x < U[L.length / 4 - 1])) =
      L.countP (fun I => decide (I.2 < (centralCandidate L).1)) := by
    rw [huget]
    simpa only [List.countP_map, Function.comp_def] using
      List.Perm.countP_eq (fun x => decide (x < U[L.length / 4 - 1]))
        (List.mergeSort_perm (L.map Prod.snd) (· ≤ ·))
  have hq' : A.countP (fun x => decide (A[3 * L.length / 4 - 1] < x)) =
      L.countP (fun I => decide ((centralCandidate L).2 < I.1)) := by
    rw [haget]
    simpa only [List.countP_map, Function.comp_def] using
      List.Perm.countP_eq (fun x => decide (A[3 * L.length / 4 - 1] < x))
        (List.mergeSort_perm (L.map Prod.fst) (· ≤ ·))
  rw [hp'] at hp
  rw [hq', ha] at hq
  constructor <;> omega

private theorem outside_left_bound (L : List Interval) (u : ℚ) :
    L.countP (fun I => decide (I.1 < u)) ≤
      L.countP (fun I => decide (I.2 < u)) + crossingCount L u := by
  apply countP_cover_le
  intro I _ h
  have hl : I.1 < u := of_decide_eq_true h
  by_cases hu : I.2 < u
  · exact Or.inl (decide_eq_true hu)
  · exact Or.inr (decide_eq_true ⟨hl.le, le_of_not_gt hu⟩)

private theorem outside_right_bound (L : List Interval) (v : ℚ) :
    L.countP (fun I => decide (v < I.2)) ≤
      L.countP (fun I => decide (v < I.1)) + crossingCount L v := by
  apply countP_cover_le
  intro I _ h
  have hr : v < I.2 := of_decide_eq_true h
  by_cases hl : v < I.1
  · exact Or.inl (decide_eq_true hl)
  · exact Or.inr (decide_eq_true ⟨le_of_not_gt hl, hr.le⟩)

private theorem outside_inside_cover (L : List Interval) (J : Interval) :
    L.length ≤ L.countP (fun I => decide (I.1 < J.1)) +
      L.countP (fun I => decide (J.2 < I.2)) + insideCount L J := by
  induction L with
  | nil => simp [insideCount]
  | cons I L ih =>
    by_cases hl : J.1 ≤ I.1 <;> by_cases hr : I.2 ≤ J.2 <;>
      simp [insideCount, hl, hr, not_lt.mpr, lt_of_not_ge] at * <;> omega

/-- The combinatorial core of central certification. If no point is covered
by more than an eighth of the intervals, both tests in the actual routine
succeed. The paper's calibrated overlap estimate is stronger than this. -/
theorem centralInterval_succeeds (L : List Interval) (hpos : 0 < L.length)
    (hfour : 4 ∣ L.length) (hvalid : ∀ I ∈ L, I.1 ≤ I.2)
    (hcross : ∀ c, 8 * crossingCount L c ≤ L.length) :
    centralInterval L = some (centralCandidate L) := by
  let J := centralCandidate L
  have ht := centralCandidate_strict_tails L hpos hfour
  have hl := outside_left_bound L J.1
  have hr := outside_right_bound L J.2
  have hcover := outside_inside_cover L J
  have hcu := hcross J.1
  have hcv := hcross J.2
  have hins : L.length ≤ 4 * insideCount L J := by
    dsimp only [J] at hl hr hcover hcu hcv ⊢
    omega
  have hlt : J.1 < J.2 := by
    by_contra h
    have hrev : J.2 ≤ J.1 := le_of_not_gt h
    have hi : insideCount L J ≤ crossingCount L J.1 := by
      apply List.countP_mono_left
      intro I hI hc
      have hc' : J.1 ≤ I.1 ∧ I.2 ≤ J.2 := of_decide_eq_true hc
      have he : I.1 = J.1 ∧ I.2 = J.1 := by
        have hw := hvalid I hI
        constructor <;> linarith
      exact decide_eq_true ⟨he.1.le, he.2.ge⟩
    omega
  simp only [centralInterval, Nat.ne_of_gt hpos, hfour, not_true_eq_false,
    or_self, ↓reduceIte]
  exact if_pos ⟨hlt, hins⟩

theorem centralInterval_inside {L : List Interval} {J : Interval}
    (h : centralInterval L = some J) :
    J.1 < J.2 ∧ L.length ≤ 4 * insideCount L J := by
  unfold centralInterval at h
  split at h
  · contradiction
  · dsimp only at h
    split at h
    · rename_i hc
      cases h
      exact hc
    · contradiction

/-- A successful central interval certifies a quarter in all three regions. -/
theorem centralInterval_certificates {L : List Interval} {J : Interval}
    (h : centralInterval L = some J) :
    J.1 < J.2 ∧ L.length ≤ 4 * leftCount L J.1 ∧
      L.length ≤ 4 * insideCount L J ∧ L.length ≤ 4 * rightCount L J.2 := by
  have hins := centralInterval_inside h
  unfold centralInterval at h
  split at h
  · contradiction
  · rename_i hvalid
    have hpos : 0 < L.length := by omega
    have hfour : 4 ∣ L.length := by tauto
    dsimp only at h
    split at h
    · cases h
      have ht := centralCandidate_tails L hpos hfour
      exact ⟨hins.1, ht.1, hins.2, ht.2⟩
    · contradiction

theorem left_sound {I : Interval} {x : ℝ} {u : ℚ}
    (hx : I.Contains x) (h : I.2 ≤ u) : x ≤ u :=
  hx.2.trans (by exact_mod_cast h)

theorem right_sound {I : Interval} {x : ℝ} {v : ℚ}
    (hx : I.Contains x) (h : v ≤ I.1) : (v : ℝ) ≤ x :=
  (show (v : ℝ) ≤ (I.1 : ℝ) by exact_mod_cast h).trans hx.1

theorem inside_sound {I J : Interval} {x : ℝ}
    (hx : I.Contains x) (h : J.1 ≤ I.1 ∧ I.2 ≤ J.2) : J.Contains x :=
  ⟨(show (J.1 : ℝ) ≤ (I.1 : ℝ) by exact_mod_cast h.1).trans hx.1,
    hx.2.trans (by exact_mod_cast h.2)⟩

/-- Rounding on a specified dyadic grid. The exponent selection is separated
from this operation so its mathematical specification is independently checked. -/
def roundOnGrid (r : ℕ) (u : ℚ) : ℚ :=
  (⌈u * (2 : ℚ) ^ r⌉ : ℚ) / (2 : ℚ) ^ r

theorem roundOnGrid_ge (r : ℕ) (u : ℚ) : u ≤ roundOnGrid r u := by
  unfold roundOnGrid
  apply (le_div_iff₀ (by positivity : (0 : ℚ) < 2 ^ r)).2
  exact Int.le_ceil _

theorem roundOnGrid_lt (r : ℕ) (u : ℚ) : roundOnGrid r u < u + 1 / (2 : ℚ) ^ r := by
  unfold roundOnGrid
  apply (div_lt_iff₀ (by positivity : (0 : ℚ) < 2 ^ r)).2
  have h := Int.ceil_lt_add_one (u * (2 : ℚ) ^ r)
  have heq : (u + 1 / (2 : ℚ) ^ r) * (2 : ℚ) ^ r = u * 2 ^ r + 1 := by
    field_simp
  simpa only [heq] using h

theorem roundOnGrid_mem {u v : ℚ} {r : ℕ}
    (hspacing : 1 / (2 : ℚ) ^ r ≤ v - u) :
    u ≤ roundOnGrid r u ∧ roundOnGrid r u ≤ v := by
  constructor
  · exact roundOnGrid_ge r u
  · have h := roundOnGrid_lt r u
    linarith

/-- Rounding anywhere in the middle half gives an interior anchor. -/
theorem middle_half_interior {l r c : ℚ} (hlr : l < r)
    (hc : l + (r - l) / 4 ≤ c ∧ c ≤ r - (r - l) / 4) :
    l < c ∧ c < r := by
  constructor <;> linarith

/-- Largest power of two at most the length, computed using integer arithmetic. -/
def spacing (J : Interval) : ℚ := (2 : ℚ) ^ Int.log 2 (J.2 - J.1)

/-- `RoundUp` from the paper, using the largest admissible dyadic spacing. -/
def roundUp (J : Interval) : ℚ := spacing J * (⌈J.1 / spacing J⌉ : ℚ)

theorem spacing_pos (J : Interval) : 0 < spacing J := by
  unfold spacing
  exact zpow_pos (by norm_num) _

theorem spacing_spec {J : Interval} (hJ : J.1 < J.2) :
    spacing J ≤ J.2 - J.1 ∧ J.2 - J.1 < 2 * spacing J := by
  constructor
  · exact Int.zpow_log_le_self (by decide) (sub_pos.mpr hJ)
  · have h := Int.lt_zpow_succ_log_self (R := ℚ) (by decide : 1 < 2) (J.2 - J.1)
    norm_num only [Nat.cast_ofNat] at h
    rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one] at h
    simpa only [spacing, mul_comm] using h

theorem roundUp_mem {J : Interval} (hJ : J.1 < J.2) :
    J.1 ≤ roundUp J ∧ roundUp J < J.2 := by
  have hs := spacing_pos J
  have hlow := Int.le_ceil (J.1 / spacing J)
  have hupp := Int.ceil_lt_add_one (J.1 / spacing J)
  have hl : J.1 ≤ roundUp J := by
    unfold roundUp
    exact (div_le_iff₀ hs).mp hlow |>.trans_eq (mul_comm _ _)
  have hu : roundUp J < J.1 + spacing J := by
    unfold roundUp
    have h := mul_lt_mul_of_pos_left hupp hs
    have heq : spacing J * (J.1 / spacing J + 1) = J.1 + spacing J := by
      field_simp
    simpa only [heq] using h
  exact ⟨hl, hu.trans_le (by linarith [(spacing_spec hJ).1])⟩

def middleHalf (l r : ℚ) : Interval := (l + (r - l) / 4, r - (r - l) / 4)

/-- The executable fallback anchor is strictly inside its canonical interval. -/
theorem roundUp_middleHalf_interior {l r : ℚ} (h : l < r) :
    l < roundUp (middleHalf l r) ∧ roundUp (middleHalf l r) < r := by
  have hJ : (middleHalf l r).1 < (middleHalf l r).2 := by dsimp [middleHalf]; linarith
  have hc := roundUp_mem hJ
  exact middle_half_interior h ⟨hc.1, hc.2.le⟩

/-- The actual central-test-or-middle-half anchor routine. -/
def chooseAnchor (l r : ℚ) (L : List Interval) : ℚ :=
  roundUp ((centralInterval L).getD (middleHalf l r))

theorem centralInterval_positive {L : List Interval} {J : Interval}
    (h : centralInterval L = some J) : 0 < L.length := by
  unfold centralInterval at h
  split at h
  · contradiction
  · rename_i hv
    omega

/-- Interior output follows from the endpoint calculations alone: every upper
endpoint is strictly above the stored lower bound and every lower endpoint is
strictly below the stored upper bound. No density oracle is used here. -/
theorem chooseAnchor_interior {l r : ℚ} {L : List Interval} (hlr : l < r)
    (hL : ∀ I ∈ L, l < I.2 ∧ I.1 < r) :
    l < chooseAnchor l r L ∧ chooseAnchor l r L < r := by
  cases hc : centralInterval L with
  | none => simpa [chooseAnchor, hc] using roundUp_middleHalf_interior hlr
  | some J =>
    have hcert := centralInterval_certificates hc
    have hN := centralInterval_positive hc
    have hleft : 0 < leftCount L J.1 := by omega
    have hright : 0 < rightCount L J.2 := by omega
    obtain ⟨I, hI, hend⟩ := List.countP_pos_iff.mp hleft
    obtain ⟨I', hI', hstart⟩ := List.countP_pos_iff.mp hright
    have hlu : l < J.1 := (hL I hI).1.trans_le (of_decide_eq_true hend)
    have hvr : J.2 < r := (of_decide_eq_true hstart).trans_lt (hL I' hI').2
    have hr := roundUp_mem hcert.1
    simpa only [chooseAnchor, hc, Option.getD_some] using
      And.intro (hlu.trans_le hr.1) (hr.2.trans hvr)

end SortingAdversary.Continuous.Certificates
