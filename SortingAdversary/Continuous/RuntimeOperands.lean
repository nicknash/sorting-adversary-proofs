import SortingAdversary.Continuous.ConcreteRoutines
import SortingAdversary.Continuous.OperandBounds
import SortingAdversary.Continuous.StateOperandBounds

/-!
# Operand bounds for actual admitted controller calls

The families below are the concrete lower and upper endpoint trajectories,
their conditional-bound and affine-digit temporaries, the public finite
certificate lists, both rounding branches, and the integer calibration
tests. Every family is bounded from the stored-state invariant and the
admitted-stage cap. In particular the prefix statements cover all rejected
words and every intermediate update, not just successful output values.
-/

namespace SortingAdversary.Continuous.RuntimeOperands

set_option maxHeartbeats 800000

open SortingAdversary.Optimal
open FiniteAveraging Precision OperandBounds EnclosureWork StateWork
open UniformStages EnclosureParameters ControllerWork Certificates

variable {n : ℕ}

def operandBits (n : ℕ) : ℕ := 10000 * (n + 4) ^ 3
def prefixGrid (n : ℕ) : ℕ := gridCap n + n ^ 2
def roundingGrid (n : ℕ) : ℕ := prefixGrid n + 2
def baseBits (n : ℕ) : ℕ := prefixGrid n + n + 2

def exponent (j : ℕ) : ℕ := alphabetExponent (degree j) (ArbitraryLabels.pathHeight (degree j))
def alphabet (j : ℕ) : ℕ := 2 ^ exponent j

@[simp] theorem alphabet_eq (j : ℕ) : alphabet j =
    EnclosureParameters.alphabet (degree j) (ArbitraryLabels.pathHeight (degree j)) := rfl

def schedule (M : StoredMemory n) (j : ℕ) (Q : Finset (Fin n)) : List (Fin n) :=
  ArbitraryLabels.fullSchedule M.data.system (degree j) (ArbitraryLabels.pathHeight (degree j))
    (degree_pos j) Q

def start (M : StoredMemory n) (upper : Bool) : Vector ℚ n :=
  if upper then M.data.upper else M.data.lower

def prefixState (M : StoredMemory n) (j : ℕ) (upper : Bool)
    (steps : List (Fin n × Fin (alphabet j))) : Vector ℚ n :=
  (EnclosureWork.fullSteps M.data (alphabet j) steps (start M upper)).value

def oneList (M : StoredMemory n) (j : ℕ) (x : Fin n) : List Interval :=
  (EnclosureWork.oneIntervals M.data (alphabet j) (schedule M j {x}) x).value

def twoList (M : StoredMemory n) (j : ℕ) (x y : Fin n) : List ComparisonIntervals :=
  (EnclosureWork.twoIntervals M.data (alphabet j) (schedule M j {x, y}) x y).value

def thresholdList (M : StoredMemory n) (j : ℕ) (x : Fin n) (c : ℚ) : List ComparisonIntervals :=
  (EnclosureWork.thresholdIntervals M.data (alphabet j) (schedule M j {x}) x c).value

theorem oneList_eq_public (M : StoredMemory n) (j : ℕ) (x : Fin n) :
    oneList M j x = ArbitraryLabels.oneIntervals M.data.system (degree j)
      (ArbitraryLabels.pathHeight (degree j)) (degree_pos j) x := by
  rw [ArbitraryLabels.oneIntervals_eq_full]
  exact EnclosureWork.oneIntervals_value _ _ _ _

theorem twoList_eq_public (M : StoredMemory n) (j : ℕ) (x y : Fin n) :
    twoList M j x y = ArbitraryLabels.twoIntervals M.data.system (degree j)
      (ArbitraryLabels.pathHeight (degree j)) (degree_pos j) x y := by
  rw [ArbitraryLabels.twoIntervals_eq_full]
  exact EnclosureWork.twoIntervals_value _ _ _ _ _

theorem thresholdList_eq_public (M : StoredMemory n) (j : ℕ) (x : Fin n) (c : ℚ) :
    thresholdList M j x c = ArbitraryLabels.thresholdIntervals M.data.system (degree j)
      (ArbitraryLabels.pathHeight (degree j)) (degree_pos j) x c := by
  rw [ArbitraryLabels.thresholdIntervals_eq_full]
  exact EnclosureWork.thresholdIntervals_value _ _ _ _ _

private theorem numerical_bounds (n : ℕ) :
    gridCap n + 1 ≤ operandBits n ∧
    8 * baseBits n + 4 ≤ operandBits n ∧
    4 * roundingGrid n + 5 ≤ operandBits n ∧
    200 * (n + 1) ≤ operandBits n ∧
    n ^ 3 + n + 3 ≤ operandBits n ∧ 4 * n + 1 ≤ operandBits n := by
  have hn : n ≤ (n + 4) ^ 3 := by
    have h := Nat.pow_le_pow_right (show 0 < n + 4 by omega) (show 1 ≤ 3 by decide)
    simp only [pow_one] at h
    omega
  have h2 : n ^ 2 ≤ (n + 4) ^ 3 :=
    (Nat.pow_le_pow_left (show n ≤ n + 4 by omega) 2).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  have h3 : (n + 3) ^ 3 ≤ (n + 4) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h0 : 1 ≤ (n + 4) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hn3 : n ^ 3 ≤ (n + 4) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  unfold operandBits baseBits roundingGrid prefixGrid gridCap
  omega

theorem baseBits_le_operandBits (n : ℕ) : baseBits n ≤ operandBits n := by
  have h := (numerical_bounds n).2.1
  omega

theorem alphabet_le (j : ℕ) (hcap : Recipe.budget.need j ≤ n) : alphabet j ≤ n :=
  (admitted_scalar_bounds j n hcap).2.2.2.2.1

theorem exponent_le (j : ℕ) (hcap : Recipe.budget.need j ≤ n) : exponent j ≤ n :=
  (admitted_scalar_bounds j n hcap).2.2.2.1

theorem schedule_words (M : StoredMemory n) (j : ℕ) (hcap : Recipe.budget.need j ≤ n)
    (hM : Controller.Admissible (degree j) M.memory) (Q : Finset (Fin n)) (hQ : Q.card ≤ 2) :
    alphabet j ^ (schedule M j Q).length ≤ n :=
  SelectionWork.admitted_words M.data j (degree_pos j) hcap Q hQ hM.degree

theorem schedule_length (M : StoredMemory n) (j : ℕ) (hcap : Recipe.budget.need j ≤ n)
    (hM : Controller.Admissible (degree j) M.memory) (Q : Finset (Fin n)) (hQ : Q.card ≤ 2) :
    (schedule M j Q).length ≤ n := by
  have hS : 2 ≤ alphabet j := by
    rw [alphabet_eq]
    have h := alphabet_large (degree j) (ArbitraryLabels.pathHeight (degree j))
    have hm := neighborhoodBound_pos (degree j) (ArbitraryLabels.pathHeight (degree j))
    nlinarith
  exact (SelectionWork.length_le_wordCount _ _ hS).trans (schedule_words M j hcap hM Q hQ)

theorem start_grid (M : StoredMemory n) (F : ℕ) (hg : M.memory.OnGrid F) (upper : Bool) :
    ∀ x : Fin n, OnDyadicGrid F (start M upper)[x] := by
  cases upper
  · exact hg.1.1
  · exact hg.1.2

theorem start_feasible (M : StoredMemory n) (k : ℕ) (hM : Controller.Admissible k M.memory)
    (upper : Bool) : M.data.system.WeaklyFeasible (values (start M upper)) := by
  have h := ArbitraryLabels.weak_endpoints M.data.system hM.normalized hM.toGeometric.widths
  cases upper
  · exact h.1
  · exact h.2

theorem prefix_grid (M : StoredMemory n) (j : ℕ) (hcap : Recipe.budget.need j ≤ n)
    (hg : M.memory.OnGrid (gridCap n)) (upper : Bool)
    (steps : List (Fin n × Fin (alphabet j))) (hlen : steps.length ≤ n) :
    ∀ x : Fin n, OnDyadicGrid (prefixGrid n) (values (prefixState M j upper steps) x) := by
  intro x
  have h := fullSteps_onGrid M.data.system (gridCap n) (exponent j) steps
    (values (start M upper)) hg.1 (start_grid M _ hg upper) x
  have hv := congrFun (EnclosureWork.fullSteps_value M.data (alphabet j) steps (start M upper)) x
  change (values (prefixState M j upper steps) x) =
    FiniteAveraging.fullSteps M.data.system (alphabet j) steps (values (start M upper)) x at hv
  rw [hv]
  apply grid_mono h
  unfold prefixGrid
  simpa only [pow_two, alphabet] using
    Nat.add_le_add_left (Nat.mul_le_mul (exponent_le j hcap) hlen) (gridCap n)

theorem prefix_feasible (M : StoredMemory n) (j : ℕ)
    (hM : Controller.Admissible (degree j) M.memory) (upper : Bool)
    (steps : List (Fin n × Fin (alphabet j))) :
    M.data.system.WeaklyFeasible (values (prefixState M j upper steps)) := by
  rw [prefixState, EnclosureWork.fullSteps_value]
  exact OperandBounds.fullSteps_feasible _ _ _ _ (start_feasible M _ hM upper)

theorem prefix_bits (M : StoredMemory n) (j : ℕ) (hcap : Recipe.budget.need j ≤ n)
    (hM : Controller.Admissible (degree j) M.memory) (hg : M.memory.OnGrid (gridCap n))
    (upper : Bool) (steps : List (Fin n × Fin (alphabet j))) (hlen : steps.length ≤ n) (x : Fin n) :
    Fits (baseBits n) (values (prefixState M j upper steps) x) ∧
      Fits (baseBits n) (EnclosureWork.conditionalLower M.data x (prefixState M j upper steps)).value ∧
      Fits (baseBits n) (EnclosureWork.conditionalUpper M.data x (prefixState M j upper steps)).value := by
  have hgrid := prefix_grid M j hcap hg upper steps hlen
  have hf := prefix_feasible M j hM upper steps
  have hunit := hM.toGeometric.rationalBounds
  have hy := Fits.of_grid (hgrid x) ((hunit x).1.trans (hf.1 x).1)
    ((hf.1 x).2.trans (hunit x).2)
  have hc := conditional_bits M.data (prefixGrid n) (prefixState M j upper steps)
    (bounds_mono hg.1 (by unfold prefixGrid; omega)) hgrid hf hunit x
  have hle : prefixGrid n + 1 ≤ baseBits n := by unfold baseBits; omega
  exact ⟨hy.mono hle, hc.1.mono hle, hc.2.mono hle⟩

theorem prefix_digit_operands (M : StoredMemory n) (j : ℕ) (hcap : Recipe.budget.need j ≤ n)
    (hM : Controller.Admissible (degree j) M.memory) (hg : M.memory.OnGrid (gridCap n))
    (upper : Bool) (steps : List (Fin n × Fin (alphabet j))) (hlen : steps.length ≤ n)
    (x : Fin n) (digit : Fin (alphabet j)) :
    ∀ q ∈ digitOperands (alphabet j) digit (values (prefixState M j upper steps) x)
      (EnclosureWork.conditionalLower M.data x (prefixState M j upper steps)).value
      (EnclosureWork.conditionalUpper M.data x (prefixState M j upper steps)).value,
      Fits (operandBits n) q := by
  have hf := prefix_bits M j hcap hM hg upper steps hlen x
  have hB : 1 ≤ baseBits n := by unfold baseBits; omega
  have hs := (fits_natCast (alphabet j) n (alphabet_le j hcap)).mono
    (show n + 1 ≤ baseBits n by unfold baseBits; omega)
  have hj := (fits_natCast digit.val n (digit.isLt.le.trans (alphabet_le j hcap))).mono
    (show n + 1 ≤ baseBits n by unfold baseBits; omega)
  intro q hq
  exact (digit_operands _ _ digit _ _ _ hB hf.1 hf.2.1 hf.2.2 hs hj q hq).mono
    (numerical_bounds n).2.1

theorem oneList_length (M : StoredMemory n) (j : ℕ) (hcap : Recipe.budget.need j ≤ n)
    (hM : Controller.Admissible (degree j) M.memory) (x : Fin n) : (oneList M j x).length ≤ n := by
  simpa only [oneList, EnclosureWork.oneIntervals_value, List.length_map, enclose_length] using
    schedule_words M j hcap hM {x} (by simp)

theorem twoList_length (M : StoredMemory n) (j : ℕ) (hcap : Recipe.budget.need j ≤ n)
    (hM : Controller.Admissible (degree j) M.memory) (x y : Fin n) : (twoList M j x y).length ≤ n := by
  simpa only [twoList, EnclosureWork.twoIntervals_value, LocalSelection.comparisonList,
    List.length_map, enclose_length] using schedule_words M j hcap hM {x, y} Finset.card_le_two

theorem thresholdList_length (M : StoredMemory n) (j : ℕ) (hcap : Recipe.budget.need j ≤ n)
    (hM : Controller.Admissible (degree j) M.memory) (x : Fin n) (c : ℚ) :
    (thresholdList M j x c).length ≤ n := by
  simpa only [thresholdList, EnclosureWork.thresholdIntervals_value, LocalSelection.thresholdList,
    List.length_map, enclose_length] using schedule_words M j hcap hM {x} (by simp)

theorem oneList_grid (M : StoredMemory n) (j : ℕ) (hcap : Recipe.budget.need j ≤ n)
    (hM : Controller.Admissible (degree j) M.memory) (hg : M.memory.OnGrid (gridCap n))
    (x : Fin n) {I : Interval} (hI : I ∈ oneList M j x) :
    OnDyadicGrid (prefixGrid n) I.1 ∧ OnDyadicGrid (prefixGrid n) I.2 := by
  rw [oneList, EnclosureWork.oneIntervals_value] at hI
  obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hI
  have h := enclose_onGrid M.data.system (gridCap n) (exponent j) (schedule M j {x}) hg.1 he x
  have hlen := schedule_length M j hcap hM {x} (by simp)
  have hb : gridCap n + exponent j * (schedule M j {x}).length ≤ prefixGrid n := by
    unfold prefixGrid
    exact Nat.add_le_add_left (by simpa only [pow_two] using Nat.mul_le_mul (exponent_le j hcap) hlen) _
  exact ⟨grid_mono h.1 hb, grid_mono h.2 hb⟩

theorem oneList_bits (M : StoredMemory n) (j : ℕ) (hcap : Recipe.budget.need j ≤ n)
    (hM : Controller.Admissible (degree j) M.memory) (hg : M.memory.OnGrid (gridCap n))
    (x : Fin n) {I : Interval} (hI : I ∈ oneList M j x) :
    Fits (operandBits n) I.1 ∧ Fits (operandBits n) I.2 := by
  have he := ArbitraryLabels.weak_endpoints M.data.system hM.normalized hM.toGeometric.widths
  have hb := OperandBounds.oneIntervals_bits M.data (gridCap n) (exponent j) (schedule M j {x})
    x hg.1 he.1 he.2 hM.toGeometric.rationalBounds I hI
  have hl := Nat.mul_le_mul (exponent_le j hcap) (schedule_length M j hcap hM {x} (by simp))
  have hle : gridCap n + exponent j * (schedule M j {x}).length + 1 ≤ operandBits n := by
    have h := (numerical_bounds n).2.1
    unfold baseBits prefixGrid at h
    nlinarith
  exact ⟨hb.1.mono hle, hb.2.mono hle⟩

theorem twoList_bits (M : StoredMemory n) (j : ℕ) (hcap : Recipe.budget.need j ≤ n)
    (hM : Controller.Admissible (degree j) M.memory) (hg : M.memory.OnGrid (gridCap n))
    (x y : Fin n) {I : ComparisonIntervals} (hI : I ∈ twoList M j x y) :
    Fits (operandBits n) I.1.1 ∧ Fits (operandBits n) I.1.2 ∧
      Fits (operandBits n) I.2.1 ∧ Fits (operandBits n) I.2.2 := by
  simp only [twoList, EnclosureWork.twoIntervals, PrimitiveWork.map_value] at hI
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hI
  have he := ArbitraryLabels.weak_endpoints M.data.system hM.normalized hM.toGeometric.widths
  have hx := endpointEntry_bits M.data (gridCap n) (exponent j) (schedule M j {x, y}) w x
    hg.1 he.1 he.2 hM.toGeometric.rationalBounds
  have hy := endpointEntry_bits M.data (gridCap n) (exponent j) (schedule M j {x, y}) w y
    hg.1 he.1 he.2 hM.toGeometric.rationalBounds
  have hl := Nat.mul_le_mul (exponent_le j hcap)
    (schedule_length M j hcap hM {x, y} Finset.card_le_two)
  have hle : gridCap n + exponent j * (schedule M j {x, y}).length + 1 ≤ operandBits n := by
    have h := (numerical_bounds n).2.1
    unfold baseBits prefixGrid at h
    nlinarith
  exact ⟨hx.1.mono hle, hx.2.mono hle, hy.1.mono hle, hy.2.mono hle⟩

theorem thresholdList_bits (M : StoredMemory n) (j : ℕ) (hcap : Recipe.budget.need j ≤ n)
    (hM : Controller.Admissible (degree j) M.memory) (hg : M.memory.OnGrid (gridCap n))
    (x : Fin n) (c : ℚ) (hc : Fits (operandBits n) c)
    {I : ComparisonIntervals} (hI : I ∈ thresholdList M j x c) :
    Fits (operandBits n) I.1.1 ∧ Fits (operandBits n) I.1.2 ∧
      Fits (operandBits n) I.2.1 ∧ Fits (operandBits n) I.2.2 := by
  simp only [thresholdList, EnclosureWork.thresholdIntervals, PrimitiveWork.map_value] at hI
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hI
  have he := ArbitraryLabels.weak_endpoints M.data.system hM.normalized hM.toGeometric.widths
  have hx := endpointEntry_bits M.data (gridCap n) (exponent j) (schedule M j {x}) w x
    hg.1 he.1 he.2 hM.toGeometric.rationalBounds
  have hl := Nat.mul_le_mul (exponent_le j hcap) (schedule_length M j hcap hM {x} (by simp))
  have hle : gridCap n + exponent j * (schedule M j {x}).length + 1 ≤ operandBits n := by
    have h := (numerical_bounds n).2.1
    unfold baseBits prefixGrid at h
    nlinarith
  exact ⟨hx.1.mono hle, hx.2.mono hle, hc, hc⟩

def RoundingFits (B : ℕ) (J : Interval) : Prop :=
  (Int.log 2 (J.2 - J.1)).natAbs.size ≤ B ∧
    (Nat.ceil (J.2 - J.1)⁻¹).size ≤ B ∧ ∀ q ∈ roundingOperands J, Fits B q

private theorem roundingFits (n : ℕ) (J : Interval)
    (hg : OnDyadicGrid (roundingGrid n) J.1 ∧ OnDyadicGrid (roundingGrid n) J.2)
    (hl : 0 < J.1) (hu : J.2 < 1) (hJ : J.1 < J.2) : RoundingFits (operandBits n) J := by
  have h := rounding_operands J (roundingGrid n) hg hl hu hJ
  have hb := (numerical_bounds n).2.2.1
  exact ⟨h.1.trans (by omega), h.2.1.trans (by omega), fun q hq => (h.2.2 q hq).mono hb⟩

theorem rounding_loop_operands (J : Interval)
    (hg : OnDyadicGrid (roundingGrid n) J.1 ∧ OnDyadicGrid (roundingGrid n) J.2)
    (hl : 0 < J.1) (hu : J.2 < 1) (hJ : J.1 < J.2) :
    (∀ a ≤ Nat.ceil (J.2 - J.1)⁻¹ + 1, a.size ≤ operandBits n) ∧
      ∀ e ≤ (Int.log 2 (J.2 - J.1)).natAbs, (StateWork.powTwo e).value.size ≤ operandBits n := by
  have h := rounding_operands J (roundingGrid n) hg hl hu hJ
  have hb := (numerical_bounds n).2.2.1
  have he := roundingExponent_le hg hl hu hJ
  constructor
  · intro a ha
    have hs := (Nat.size_le_size ha).trans (RationalWork.size_add_le (Nat.ceil (J.2 - J.1)⁻¹) 1)
    simp only [Nat.size_one] at hs
    omega
  · intro e hep
    rw [RoundingWork.log_natAbs_eq_roundingExponent (by linarith)] at hep
    rw [StateWork.powTwo_value, Nat.size_pow]
    omega

theorem middle_rounding (M : StoredMemory n) (j : ℕ)
    (hM : Controller.Admissible (degree j) M.memory) (hg : M.memory.OnGrid (gridCap n)) (x : Fin n) :
    RoundingFits (operandBits n) (middleHalf (M.data.system.lower x) (M.data.system.upper x)) := by
  have hgrid := middleHalf_onGrid (hg.1.1 x) (hg.1.2 x)
  have hunit := hM.toGeometric.rationalBounds x
  have hw := hM.toGeometric.widths x
  change 0 ≤ M.data.system.lower x ∧ M.data.system.upper x ≤ 1 at hunit
  change M.data.system.lower x < M.data.system.upper x at hw
  apply roundingFits
  · exact ⟨grid_mono hgrid.1 (by unfold roundingGrid prefixGrid; omega),
      grid_mono hgrid.2 (by unfold roundingGrid prefixGrid; omega)⟩
  all_goals dsimp only [middleHalf]; linarith

theorem central_rounding (M : StoredMemory n) (j : ℕ) (hcap : Recipe.budget.need j ≤ n)
    (hM : Controller.Admissible (degree j) M.memory) (hg : M.memory.OnGrid (gridCap n))
    (x : Fin n) {J : Interval} (hJ : centralInterval (oneList M j x) = some J) :
    RoundingFits (operandBits n) J := by
  have hgrid := centralInterval_onGrid (prefixGrid n) (fun I hI => oneList_grid M j hcap hM hg x hI) hJ
  have hi := ArbitraryLabels.central_interior M.data.system (degree j)
    (ArbitraryLabels.pathHeight (degree j)) (degree_pos j)
    (ArbitraryLabels.weak_endpoints M.data.system hM.normalized hM.toGeometric.widths).1
    (ArbitraryLabels.weak_endpoints M.data.system hM.normalized hM.toGeometric.widths).2
    hM.toGeometric.widths x J (by rwa [← oneList_eq_public])
  have hunit := hM.toGeometric.rationalBounds x
  apply roundingFits
  · exact ⟨grid_mono hgrid.1 (by unfold roundingGrid; omega),
      grid_mono hgrid.2 (by unfold roundingGrid; omega)⟩
  · exact hunit.1.trans_lt hi.1
  · exact hi.2.trans_le hunit.2
  · exact (centralInterval_inside hJ).1

def RoutingFits (B : ℕ) : TreeState.Routing ℚ → Prop
  | .coordinates => True
  | .leftFree c | .rightFree c => Fits B c
  | .anchors c d => Fits B c ∧ Fits B d

theorem route_fits {B : ℕ} (p q : List ℚ)
    (hp : ∀ c ∈ p, Fits B c) (hq : ∀ c ∈ q, Fits B c) :
    RoutingFits B (TreeState.route p q) := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => trivial
    | cons c q => exact hq c (by simp)
  | cons c p ih =>
    cases q with
    | nil => exact hp c (by simp)
    | cons d q =>
      simp only [TreeState.route]
      split
      · exact ih q (fun e he => hp e (by simp [he])) (fun e he => hq e (by simp [he]))
      · exact ⟨hp c (by simp), hq d (by simp)⟩

def AnchorFits (B : ℕ) (c : DyadicAnchor) : Prop :=
  (c.1 + 1).size ≤ B ∧ c.2.val.size ≤ B ∧ (2 * c.2.val + 1).size ≤ B ∧
    (2 ^ (c.1 + 1)).size ≤ B ∧ Fits B c.coordinate

theorem anchorFits_of_level (c : DyadicAnchor) (F : ℕ) (hlevel : c.1 + 1 ≤ F) :
    AnchorFits (F + 1) c := by
  have hpow : 2 ^ (c.1 + 1) ≤ 2 ^ F := Nat.pow_le_pow_right (by decide) hlevel
  have hi : c.2.val ≤ 2 ^ F := c.2.isLt.le.trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hnum : 2 * c.2.val + 1 ≤ 2 ^ F := by
    have h : 2 * c.2.val + 1 < 2 ^ (c.1 + 1) := by rw [pow_succ]; omega
    exact h.le.trans hpow
  have hgrid : OnDyadicGrid (c.1 + 1) c.coordinate := by
    refine ⟨2 * (c.2.val : ℤ) + 1, ?_⟩
    simp [DyadicAnchor.coordinate]
  have hf := Fits.of_grid (grid_mono hgrid hlevel) c.coordinate_pos.le c.coordinate_lt_one.le
  exact ⟨(size_le_value _).trans (by omega),
    by simpa only [Nat.size_pow] using Nat.size_le_size hi,
    by simpa only [Nat.size_pow] using Nat.size_le_size hnum,
    by simpa only [Nat.size_pow] using Nat.size_le_size hpow, hf⟩

theorem AnchorFits.mono {A B : ℕ} {c : DyadicAnchor} (h : AnchorFits A c) (hAB : A ≤ B) :
    AnchorFits B c := ⟨h.1.trans hAB, h.2.1.trans hAB, h.2.2.1.trans hAB,
      h.2.2.2.1.trans hAB, h.2.2.2.2.mono hAB⟩

theorem stored_anchor (M : StoredMemory n) (hg : M.memory.OnGrid (gridCap n))
    (x : Fin n) (c : DyadicAnchor) (hc : c ∈ M.paths[x]) : AnchorFits (operandBits n) c :=
  (anchorFits_of_level c _ (Controller.stored_anchor_level hg x c hc)).mono (numerical_bounds n).1

theorem routed_operands (M : StoredMemory n) (hg : M.memory.OnGrid (gridCap n)) (q : Query n) :
    RoutingFits (operandBits n) (StateWork.route M q).value := by
  rw [StateWork.route_value]
  apply route_fits
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    exact (stored_anchor M hg q.left a ha).2.2.2.2
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    exact (stored_anchor M hg q.right a ha).2.2.2.2

/-- The total decoder is bounded even before using the round-trip theorem;
all actual rounded interior inputs are a special case. -/
theorem decoded_operands (q : ℚ) (hq : OnDyadicGrid (roundingGrid n) q) :
    AnchorFits (operandBits n) (StateWork.decode q).value := by
  have h := StateWork.decode_level_grid q (roundingGrid n) hq
  apply (anchorFits_of_level _ _ h).mono
  have hb := (numerical_bounds n).2.2.1
  omega

theorem rounded_decode (J : Interval)
    (hg : OnDyadicGrid (roundingGrid n) J.1 ∧ OnDyadicGrid (roundingGrid n) J.2)
    (hl : 0 < J.1) (hu : J.2 < 1) (hJ : J.1 < J.2) :
    AnchorFits (operandBits n) (StateWork.decode (Certificates.roundUp J)).value :=
  decoded_operands _ (roundUp_preserves_grid hg hl hu hJ)

theorem raw_decoder (q : ℚ) (hq : OnDyadicGrid (roundingGrid n) q) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    StateOperandBounds.DecoderOperands q (operandBits n) := by
  apply (StateOperandBounds.decode_operands_of_unit_grid q (roundingGrid n) hq h0 h1).mono
  have hb := (numerical_bounds n).2.2.1
  omega

theorem rounded_raw_decoder (J : Interval)
    (hg : OnDyadicGrid (roundingGrid n) J.1 ∧ OnDyadicGrid (roundingGrid n) J.2)
    (hl : 0 < J.1) (hu : J.2 < 1) (hJ : J.1 < J.2) :
    StateOperandBounds.DecoderOperands (Certificates.roundUp J) (operandBits n) := by
  have hm := roundUp_mem hJ
  exact raw_decoder _ (roundUp_preserves_grid hg hl hu hJ)
    (hl.le.trans hm.1) (hm.2.le.trans hu.le)

theorem repair_path_count (M : StoredMemory n) (j : ℕ) (hcap : Recipe.budget.need j ≤ n)
    (hM : Controller.Admissible (degree j) M.memory) :
    (GraphScanWork.paths M.data (2 ^ degree j)).value.length ≤ n ^ 2 := by
  rw [GraphScanWork.paths_value]
  have hb := (admitted_scalar_bounds j n hcap).2.2.1
  have hH : 2 ^ degree j ≤ ArbitraryLabels.pathHeight (degree j) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpower : (degree j + 1) ^ (2 ^ degree j) ≤ n := by
    apply le_trans ?_ hb
    exact Nat.pow_le_pow_right (by omega) (hH.trans (Nat.le_succ _))
  obtain ⟨h, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pow_pos (by decide : 0 < 2)).ne'
  have hc := GraphPaths.paths_length_le M.data.system.edge (degree j) hM.toGeometric.noLoop hM.degree h
  rw [he] at hpower ⊢
  have hp : degree j ^ h ≤ n := (Nat.pow_le_pow_left (Nat.le_succ _) h).trans
    ((Nat.pow_le_pow_right (by omega) (Nat.le_succ h)).trans hpower)
  exact hc.trans (by simpa only [pow_two] using Nat.mul_le_mul_left n hp)

structure NaturalBounds (M : StoredMemory n) (j : ℕ) : Prop where
  height : (StageWork.calibrate (degree j) (degree_pos j)).value.height ≤ n
  sweeps : (StageWork.calibrate (degree j) (degree_pos j)).value.sweeps ≤ n
  radius : (StageWork.calibrate (degree j) (degree_pos j)).value.radius ≤ n ^ 2
  paths : (GraphScanWork.paths M.data (2 ^ degree j)).value.length ≤ n ^ 2
  history : M.history.length ≤ historyCap n
  depth : Controller.totalDepth M.memory ≤ depthCap n
  small : ∀ a ≤ (n + 3) ^ 3, a.size ≤ operandBits n

theorem natural_bounds (M : StoredMemory n) (j : ℕ) (hcap : Recipe.budget.need j ≤ n)
    (hM : Controller.Admissible (degree j) M.memory)
    (hs : Sized M.memory (depthCap n) (gridCap n) (historyCap n)) : NaturalBounds M j := by
  have hH := (admitted_scalar_bounds j n hcap).2.1
  have ht := admitted_sweepCount j n hcap
  constructor
  · simpa only [StageWork.calibrate_height] using hH
  · simpa only [StageWork.calibrate_sweeps, Neighborhood.sweeps] using ht
  · rw [StageWork.calibrate_radius]
    simpa only [pow_two, Neighborhood.sweeps] using Nat.mul_le_mul hH ht
  · exact repair_path_count M j hcap hM
  · exact hs.history
  · exact hs.depth
  · intro a ha
    apply (size_le_value a).trans (ha.trans ?_)
    have hp : (n + 3) ^ 3 ≤ (n + 4) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    unfold operandBits
    omega

theorem stored_bounds (M : StoredMemory n) (j : ℕ)
    (hM : Controller.Admissible (degree j) M.memory) (hg : M.memory.OnGrid (gridCap n)) :
    StateOperandBounds.BoundsFit (operandBits n) M.data.system := by
  intro x
  have hu := hM.toGeometric.rationalBounds x
  have hw := hM.toGeometric.widths x
  exact ⟨(Fits.of_grid (hg.1.1 x) hu.1 (hw.le.trans hu.2)).mono (numerical_bounds n).1,
    (Fits.of_grid (hg.1.2 x) (hu.1.trans hw.le) hu.2).mono (numerical_bounds n).1⟩

theorem conditional_scan_operands (M : StoredMemory n) (j : ℕ) (hcap : Recipe.budget.need j ≤ n)
    (hM : Controller.Admissible (degree j) M.memory) (hg : M.memory.OnGrid (gridCap n))
    (upper : Bool) (steps : List (Fin n × Fin (alphabet j))) (hlen : steps.length ≤ n)
    (x : Fin n) (Q : Finset (Fin n)) :
    Fits (operandBits n) (Q.fold max (M.data.system.lower x) (values (prefixState M j upper steps))) ∧
      Fits (operandBits n) (Q.fold min (M.data.system.upper x) (values (prefixState M j upper steps))) := by
  have hD := stored_bounds M j hM hg x
  have hY (y : Fin n) : Fits (operandBits n) (values (prefixState M j upper steps) y) :=
    (prefix_bits M j hcap hM hg upper steps hlen y).1.mono (baseBits_le_operandBits n)
  exact ⟨StateOperandBounds.maxFold_fits Q _ _ hD.1 (fun y _ => hY y),
    StateOperandBounds.minFold_fits Q _ _ hD.2 (fun y _ => hY y)⟩

theorem reset_passes (M : StoredMemory n) (j : ℕ)
    (hM : Controller.Admissible (degree j) M.memory) (hg : M.memory.OnGrid (gridCap n))
    (x : Fin n) (c : ℚ) (hc : Fits (operandBits n) c) (lowerOrder upperOrder : List (Fin n)) :
    StateOperandBounds.BoundsFit (operandBits n)
      (StateWork.upperPass (StateWork.lowerPass (StateWork.reset M.data x c).value lowerOrder).value
        upperOrder).value.system := by
  have hB : 1 ≤ operandBits n := by have h := (numerical_bounds n).1; omega
  exact StateOperandBounds.upperPass_fits _ _
    (StateOperandBounds.lowerPass_fits _ _
      (StateOperandBounds.reset_fits M.data x c (stored_bounds M j hM hg) hc hB))

theorem record_passes (M : StoredMemory n) (j : ℕ)
    (hM : Controller.Admissible (degree j) M.memory) (hg : M.memory.OnGrid (gridCap n))
    (q : Query n) (a : Answer) (lowerOrder upperOrder : List (Fin n)) :
    StateOperandBounds.BoundsFit (operandBits n)
      (StateWork.upperPass (StateWork.lowerPass
        (StateWork.recordSystem M.data (StateWork.route M q).value q.left q.right a).value
          lowerOrder).value upperOrder).value.system := by
  exact StateOperandBounds.upperPass_fits _ _
    (StateOperandBounds.lowerPass_fits _ _
      (StateOperandBounds.recordSystem_fits M.data _ q.left q.right a (stored_bounds M j hM hg)
        (routed_operands M hg q)))

/-- Actual admitted calls share one operand certificate. The fields name
concrete trajectories and tests; `component_operands` derives every field
from the controller invariant and its proved input caps. -/
structure ComponentOperands (M : StoredMemory n) (j : ℕ) : Prop where
  natural : NaturalBounds M j
  stored : ∀ x, Fits (operandBits n) (M.data.system.lower x) ∧
    Fits (operandBits n) (M.data.system.upper x)
  anchors : ∀ (x : Fin n) (c : DyadicAnchor), c ∈ M.paths[x] → Fits (operandBits n) c.coordinate
  anchorCodes : ∀ (x : Fin n) (c : DyadicAnchor), c ∈ M.paths[x] → AnchorFits (operandBits n) c
  routed : ∀ q, RoutingFits (operandBits n) (StateWork.route M q).value
  decoded : ∀ q, OnDyadicGrid (roundingGrid n) q →
    AnchorFits (operandBits n) (StateWork.decode q).value
  decodedRaw : ∀ q, OnDyadicGrid (roundingGrid n) q → 0 ≤ q → q ≤ 1 →
    StateOperandBounds.DecoderOperands q (operandBits n)
  prefixes : ∀ (upper : Bool) (steps : List (Fin n × Fin (alphabet j))), steps.length ≤ n → ∀ x,
    Fits (operandBits n) (values (prefixState M j upper steps) x) ∧
      Fits (operandBits n) (EnclosureWork.conditionalLower M.data x (prefixState M j upper steps)).value ∧
      Fits (operandBits n) (EnclosureWork.conditionalUpper M.data x (prefixState M j upper steps)).value
  digits : ∀ (upper : Bool) (steps : List (Fin n × Fin (alphabet j))), steps.length ≤ n → ∀ x digit,
    ∀ q ∈ digitOperands (alphabet j) digit (values (prefixState M j upper steps) x)
      (EnclosureWork.conditionalLower M.data x (prefixState M j upper steps)).value
      (EnclosureWork.conditionalUpper M.data x (prefixState M j upper steps)).value,
      Fits (operandBits n) q
  conditionalScans : ∀ (upper : Bool) (steps : List (Fin n × Fin (alphabet j))), steps.length ≤ n →
    ∀ x (Q : Finset (Fin n)),
      Fits (operandBits n) (Q.fold max (M.data.system.lower x) (values (prefixState M j upper steps))) ∧
        Fits (operandBits n) (Q.fold min (M.data.system.upper x) (values (prefixState M j upper steps)))
  resetPasses : ∀ x c, Fits (operandBits n) c → ∀ lowerOrder upperOrder,
    StateOperandBounds.BoundsFit (operandBits n)
      (StateWork.upperPass (StateWork.lowerPass (StateWork.reset M.data x c).value lowerOrder).value
        upperOrder).value.system
  recordPasses : ∀ q a lowerOrder upperOrder,
    StateOperandBounds.BoundsFit (operandBits n)
      (StateWork.upperPass (StateWork.lowerPass
        (StateWork.recordSystem M.data (StateWork.route M q).value q.left q.right a).value
          lowerOrder).value upperOrder).value.system
  words : ∀ Q : Finset (Fin n), Q.card ≤ 2 → alphabet j ^ (schedule M j Q).length ≤ n
  one : ∀ x, (oneList M j x).length ≤ n ∧ ∀ I ∈ oneList M j x,
    Fits (operandBits n) I.1 ∧ Fits (operandBits n) I.2
  two : ∀ x y, (twoList M j x y).length ≤ n ∧ ∀ I ∈ twoList M j x y,
    Fits (operandBits n) I.1.1 ∧ Fits (operandBits n) I.1.2 ∧
      Fits (operandBits n) I.2.1 ∧ Fits (operandBits n) I.2.2
  threshold : ∀ x c, Fits (operandBits n) c →
    (thresholdList M j x c).length ≤ n ∧ ∀ I ∈ thresholdList M j x c,
      Fits (operandBits n) I.1.1 ∧ Fits (operandBits n) I.1.2 ∧
        Fits (operandBits n) I.2.1 ∧ Fits (operandBits n) I.2.2
  middle : ∀ x, RoundingFits (operandBits n) (middleHalf (M.data.system.lower x) (M.data.system.upper x))
  central : ∀ x J, centralInterval (oneList M j x) = some J → RoundingFits (operandBits n) J
  roundingLoops : ∀ J : Interval,
    OnDyadicGrid (roundingGrid n) J.1 ∧ OnDyadicGrid (roundingGrid n) J.2 →
    0 < J.1 → J.2 < 1 → J.1 < J.2 →
    (∀ a ≤ Nat.ceil (J.2 - J.1)⁻¹ + 1, a.size ≤ operandBits n) ∧
      ∀ e ≤ (Int.log 2 (J.2 - J.1)).natAbs, (StateWork.powTwo e).value.size ≤ operandBits n
  answer : ∀ L : List ComparisonIntervals, L.length ≤ n →
    ∀ q ∈ answerOperands (degree j) L, Fits (operandBits n) q
  quantile : ∀ (L : List Interval), L.length ≤ n → ∀ J,
    (L.length / 4 - 1).size ≤ operandBits n ∧
      (3 * L.length / 4 - 1).size ≤ operandBits n ∧
      (insideCount L J).size ≤ operandBits n ∧ (4 * insideCount L J).size ≤ operandBits n
  moment : ∀ p ≤ momentPower (degree j) (ArbitraryLabels.pathHeight (degree j)),
    ((alphabet j ^ ArbitraryLabels.pathHeight (degree j)) ^ p).size ≤ operandBits n ∧
      (4 * neighborhoodBound (degree j) (ArbitraryLabels.pathHeight (degree j)) *
        (alphabet j ^ ArbitraryLabels.pathHeight (degree j) - 1) ^ p).size ≤ operandBits n
  sweep : ∀ t ≤ (StageWork.sweeps (degree j) (degree_pos j)).value,
    (2 * failureDen (degree j) * accuracyDen (degree j) ^
      momentPower (degree j) (ArbitraryLabels.pathHeight (degree j))).size ≤ operandBits n ∧
      (2 ^ t).size ≤ operandBits n

theorem component_operands (M : StoredMemory n) (j : ℕ) (hcap : Recipe.budget.need j ≤ n)
    (hM : Controller.Admissible (degree j) M.memory)
    (hs : Sized M.memory (depthCap n) (gridCap n) (historyCap n)) : ComponentOperands M j := by
  obtain ⟨hk, hH, hB, he, hS, hp, hA, hD, _⟩ := admitted_scalar_bounds j n hcap
  have ht : (StageWork.sweeps (degree j) (degree_pos j)).value ≤ n := by
    simpa only [StageWork.sweeps_value, Neighborhood.sweeps] using admitted_sweepCount j n hcap
  constructor
  · exact natural_bounds M j hcap hM hs
  · exact stored_bounds M j hM hs.grid
  · intro x c hc
    exact (stored_anchor M hs.grid x c hc).2.2.2.2
  · exact stored_anchor M hs.grid
  · exact routed_operands M hs.grid
  · exact decoded_operands
  · exact raw_decoder
  · intro upper steps hlen x
    have h := prefix_bits M j hcap hM hs.grid upper steps hlen x
    exact ⟨h.1.mono (baseBits_le_operandBits n), h.2.1.mono (baseBits_le_operandBits n),
      h.2.2.mono (baseBits_le_operandBits n)⟩
  · exact prefix_digit_operands M j hcap hM hs.grid
  · exact conditional_scan_operands M j hcap hM hs.grid
  · exact reset_passes M j hM hs.grid
  · exact record_passes M j hM hs.grid
  · exact schedule_words M j hcap hM
  · intro x
    exact ⟨oneList_length M j hcap hM x, fun _ hI => oneList_bits M j hcap hM hs.grid x hI⟩
  · intro x y
    exact ⟨twoList_length M j hcap hM x y, fun _ hI => twoList_bits M j hcap hM hs.grid x y hI⟩
  · intro x c hc
    exact ⟨thresholdList_length M j hcap hM x c,
      fun _ hI => thresholdList_bits M j hcap hM hs.grid x c hc hI⟩
  · exact middle_rounding M j hM hs.grid
  · intro x J hJ
    exact central_rounding M j hcap hM hs.grid x hJ
  · exact rounding_loop_operands
  · intro L hL q hq
    exact (answer_operands (degree j) n L hk hL q hq).mono (numerical_bounds n).2.2.2.1
  · intro L hL J
    have h := certificate_indices L n hL J
    have hb := (numerical_bounds n).2.2.2.2.2
    exact ⟨h.1.trans (by omega), h.2.1.trans (by omega), h.2.2.1.trans (by omega), h.2.2.2.trans (by omega)⟩
  · intro p hple
    have h := StageArithmetic.moment_operand_sizes (degree j) (ArbitraryLabels.pathHeight (degree j))
      p n hS hH (hple.trans hp) hB
    have hb := (numerical_bounds n).2.2.2.2.1
    exact ⟨h.1.trans (by omega), h.2.trans hb⟩
  · intro t htle
    have h := StageArithmetic.sweep_operand_sizes (failureDen (degree j)) (accuracyDen (degree j))
      (momentPower (degree j) (ArbitraryLabels.pathHeight (degree j))) t n hA hD hp (htle.trans ht)
    have h2 : n ^ 2 ≤ (n + 4) ^ 3 :=
      (Nat.pow_le_pow_left (show n ≤ n + 4 by omega) 2).trans
        (Nat.pow_le_pow_right (by omega) (by decide))
    have hn : n ≤ (n + 4) ^ 3 := by
      have hh := Nat.pow_le_pow_right (show 0 < n + 4 by omega) (show 1 ≤ 3 by decide)
      simp only [pow_one] at hh
      omega
    have h0 : 1 ≤ (n + 4) ^ 3 := Nat.one_le_pow _ _ (by omega)
    constructor
    · apply h.1.trans
      unfold operandBits
      omega
    · apply h.2.trans
      unfold operandBits
      omega

end SortingAdversary.Continuous.RuntimeOperands
