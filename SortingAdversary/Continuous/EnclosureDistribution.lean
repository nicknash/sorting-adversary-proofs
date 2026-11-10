import SortingAdversary.Continuous.FiniteDependence

/-!
# The distribution of the actual finite enclosure list

Finite word averaging makes the connection between the full-graph moment
calculation and the executable local list. Frozen updates are literal no-ops
and disappear from an average without changing its value.
-/

namespace SortingAdversary.Continuous.FiniteAveraging

open SortingAdversary.Optimal.FiniteProbability
open SortingAdversary.Optimal.GraphBalls
open scoped BigOperators

section Programs

variable {ι σ : Type*} {S : ℕ}

/-- Evaluate a scheduled deterministic program with one digit per operation. -/
def evalWord (step : σ → ι → Fin S → σ) :
    (schedule : List ι) → (Fin schedule.length → Fin S) → σ → σ
  | [], _, state => state
  | x :: xs, digits, state => evalWord step xs (Fin.tail digits) (step state x (digits 0))

/-- Evaluate the same program by averaging over each independent digit. -/
def averageRun (step : σ → ι → Fin S → σ) : List ι → σ → (σ → ℚ) → ℚ
  | [], state, observable => observable state
  | x :: xs, state, observable => mean (fun j : Fin S =>
      averageRun step xs (step state x j) observable)

variable [NeZero S]

theorem mean_evalWord (step : σ → ι → Fin S → σ) (schedule : List ι)
    (state : σ) (observable : σ → ℚ) :
    mean (fun digits : Fin schedule.length → Fin S => observable (evalWord step schedule digits state)) =
      averageRun step schedule state observable := by
  induction schedule generalizing state with
  | nil => simp [evalWord, averageRun]
  | cons x xs ih =>
    let e := Fin.consEquiv (fun _ : Fin (xs.length + 1) => Fin S)
    have he := mean_equiv e (fun digits => observable (evalWord step (x :: xs) digits state))
    trans mean (fun ω => observable (evalWord step (x :: xs) (e ω) state))
    · exact (mean_congr_fintype _ _ (fun _ => rfl)).trans he.symm
    rw [mean_product]
    simp only [e, Fin.consEquiv_apply, evalWord, Fin.cons_zero, Fin.tail_cons, averageRun]
    exact mean_congr (fun j => ih (step state x j))

theorem averageRun_append (step : σ → ι → Fin S → σ) (xs ys : List ι)
    (state : σ) (observable : σ → ℚ) :
    averageRun step (xs ++ ys) state observable =
      averageRun step xs state (fun state' => averageRun step ys state' observable) := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, averageRun]
    exact mean_congr (fun j => ih (step state x j))

theorem averageRun_mask (step : σ → ι → Fin S → σ) (active : ι → Bool)
    (schedule : List ι) (state : σ) (observable : σ → ℚ) :
    averageRun (fun state x j => if active x then step state x j else state)
      schedule state observable = averageRun step (schedule.filter active) state observable := by
  induction schedule generalizing state with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : active x = true
    · simp only [averageRun, hx, ↓reduceIte, List.filter_cons_of_pos hx]
      exact mean_congr (fun j => ih (step state x j))
    · have hx' : active x = false := Bool.eq_false_iff.mpr hx
      simp [averageRun, hx', ih]

def repeatSchedule (schedule : List ι) : ℕ → List ι
  | 0 => []
  | t + 1 => repeatSchedule schedule t ++ schedule

@[simp] theorem repeatSchedule_length (schedule : List ι) (t : ℕ) :
    (repeatSchedule schedule t).length = schedule.length * t := by
  induction t with
  | zero => simp [repeatSchedule]
  | succ t ih => simp [repeatSchedule, ih, Nat.mul_add]

theorem repeatSchedule_filter (schedule : List ι) (active : ι → Bool) (t : ℕ) :
    (repeatSchedule schedule t).filter active = repeatSchedule (schedule.filter active) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [repeatSchedule, List.filter_append, ih]

end Programs

section Enumeration

theorem words_average (S m : ℕ) (observable : (Fin m → Fin S) → ℚ) :
    ((words S m).map observable).sum / (words S m).length = mean observable := by
  classical
  have hall : (words S m).toFinset = Finset.univ := by
    ext digits
    simp [mem_words digits]
  have hsum : ((words S m).map observable).sum = ∑ digits, observable digits := by
    rw [← List.sum_toFinset observable (words_nodup S m), hall]
  rw [hsum, words_length]
  simp [mean]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ℕ}

theorem enclose_average (D : System ι ℚ) (schedule : List ι)
    (observable : (ι → ℚ × ℚ) → ℚ) :
    ((enclose D S schedule).map observable).sum / (enclose D S schedule).length =
      mean (fun digits => observable (endpointEntry D S schedule digits)) := by
  simpa only [enclose, List.map_map, Function.comp_def, List.length_map] using
    words_average S schedule.length (fun digits => observable (endpointEntry D S schedule digits))

def pairStep (D : System ι ℚ) (state : (ι → ℚ) × (ι → ℚ)) (x : ι) (j : Fin S) :
    (ι → ℚ) × (ι → ℚ) := (update D S j x state.1, update D S j x state.2)

def pairMaskedStep (D : System ι ℚ) (F : Finset ι)
    (state : (ι → ℚ) × (ι → ℚ)) (x : ι) (j : Fin S) : (ι → ℚ) × (ι → ℚ) :=
  if x ∈ F then pairStep (S := S) D state x j else state

theorem evalWord_pairStep (D : System ι ℚ) (schedule : List ι)
    (digits : Fin schedule.length → Fin S) (A B : ι → ℚ) :
    evalWord (pairStep (S := S) D) schedule digits (A, B) =
      (fullSteps D S (assignedSteps S schedule digits) A,
        fullSteps D S (assignedSteps S schedule digits) B) := by
  induction schedule generalizing A B with
  | nil => rfl
  | cons x xs ih =>
    rw [evalWord, assignedSteps_cons]
    exact ih (Fin.tail digits) _ _

theorem evalWord_pairMaskedStep (D : System ι ℚ) (F : Finset ι) (schedule : List ι)
    (digits : Fin schedule.length → Fin S) (A B : ι → ℚ) :
    evalWord (pairMaskedStep (S := S) D F) schedule digits (A, B) =
      (maskedSteps D S F (assignedSteps S schedule digits) A,
        maskedSteps D S F (assignedSteps S schedule digits) B) := by
  induction schedule generalizing A B with
  | nil => rfl
  | cons x xs ih =>
    rw [evalWord, assignedSteps_cons]
    by_cases hx : x ∈ F
    · simpa [pairMaskedStep, pairStep, maskedSteps, maskedStep, hx] using
        ih (Fin.tail digits) (update D S (digits 0) x A) (update D S (digits 0) x B)
    · simpa [pairMaskedStep, maskedSteps, maskedStep, hx] using ih (Fin.tail digits) A B

end Enumeration

section FullHistory

variable {n S : ℕ} [NeZero S]

/-- The list of all vertex labels has precisely one word digit per vertex. -/
def finRangeWordEquiv : (Fin n → Fin S) ≃ (Fin (List.finRange n).length → Fin S) where
  toFun digits i := digits (Fin.cast (List.length_finRange (n := n)) i)
  invFun digits i := digits (Fin.cast (List.length_finRange (n := n)).symm i)
  left_inv digits := by funext i; simp
  right_inv digits := by funext i; simp

theorem assignedSteps_finRange (digits : Fin n → Fin S) :
    assignedSteps S (List.finRange n) (finRangeWordEquiv digits) =
      prefixSteps digits n le_rfl := by
  unfold assignedSteps
  rw [List.ofFn_congr (List.length_finRange (n := n))]
  unfold prefixSteps
  congr 1
  funext i
  simp [finRangeWordEquiv]

theorem mean_orderedMaskedSweep (D : System (Fin n) ℚ) (F : Finset (Fin n))
    (A B : Fin n → ℚ) (observable : ((Fin n → ℚ) × (Fin n → ℚ)) → ℚ) :
    mean (fun digits : Fin n → Fin S =>
      observable (orderedMaskedSweep D F digits A, orderedMaskedSweep D F digits B)) =
      averageRun (pairMaskedStep (S := S) D F) (List.finRange n) (A, B) observable := by
  calc
    _ = mean (fun digits : Fin n → Fin S =>
        observable (evalWord (pairMaskedStep (S := S) D F) (List.finRange n)
          (finRangeWordEquiv digits) (A, B))) := by
      apply mean_congr
      intro digits
      rw [evalWord_pairMaskedStep, assignedSteps_finRange]
      simp only [orderedMaskedSweep, orderedMaskedAfter_eq_steps D F digits _ n le_rfl]
    _ = mean (fun word : Fin (List.finRange n).length → Fin S =>
        observable (evalWord (pairMaskedStep (S := S) D F) (List.finRange n) word (A, B))) :=
      mean_equiv (finRangeWordEquiv (n := n) (S := S))
        (fun word => observable (evalWord (pairMaskedStep (S := S) D F)
          (List.finRange n) word (A, B)))
    _ = _ := mean_evalWord _ _ _ _

theorem mean_iterateMaskedSweep (D : System (Fin n) ℚ) (F : Finset (Fin n))
    (A B : Fin n → ℚ) (t : ℕ)
    (observable : ((Fin n → ℚ) × (Fin n → ℚ)) → ℚ) :
    mean (fun history : SweepHistory n S t =>
      observable (iterateMaskedSweep D F A t history, iterateMaskedSweep D F B t history)) =
      averageRun (pairMaskedStep (S := S) D F) (repeatSchedule (List.finRange n) t) (A, B) observable := by
  induction t generalizing observable with
  | zero => simp [iterateMaskedSweep, repeatSchedule, averageRun]
  | succ t ih =>
    have he : mean (fun history : SweepHistory n S (t + 1) =>
        observable (iterateMaskedSweep D F A (t + 1) history,
          iterateMaskedSweep D F B (t + 1) history)) =
        mean (fun sample : SweepHistory n S t × (Fin n → Fin S) =>
          observable (orderedMaskedSweep D F sample.2 (iterateMaskedSweep D F A t sample.1),
            orderedMaskedSweep D F sample.2 (iterateMaskedSweep D F B t sample.1))) :=
      mean_congr_fintype _ _ (fun _ => rfl)
    rw [he, mean_product]
    simp_rw [mean_orderedMaskedSweep]
    rw [ih (fun state => averageRun (pairMaskedStep (S := S) D F) (List.finRange n) state observable),
      repeatSchedule, averageRun_append]

/-- The two endpoint functions represented by one interval-family entry. -/
def entryState (entry : Fin n → ℚ × ℚ) : (Fin n → ℚ) × (Fin n → ℚ) :=
  (fun x => (entry x).1, fun x => (entry x).2)

/-- Exact marginalization: averaging the full digit history with exterior
updates frozen gives the empirical average of the executable local list.
Repeated equal entries are counted with their original multiplicity. -/
theorem enclose_average_eq_masked_history (D : System (Fin n) ℚ)
    (F : Finset (Fin n)) (t : ℕ)
    (observable : ((Fin n → ℚ) × (Fin n → ℚ)) → ℚ) :
    let schedule := repeatSchedule ((List.finRange n).filter fun x => x ∈ F) t
    ((enclose D S schedule).map (fun entry => observable (entryState entry))).sum /
        (enclose D S schedule).length =
      mean (fun history : SweepHistory n S t => observable
        (iterateMaskedSweep D F D.lower t history, iterateMaskedSweep D F D.upper t history)) := by
  dsimp only
  rw [enclose_average, mean_iterateMaskedSweep]
  have he : mean (fun digits : Fin
        (repeatSchedule ((List.finRange n).filter fun x => x ∈ F) t).length → Fin S =>
        observable (entryState (endpointEntry D S _ digits))) =
      mean (fun digits : Fin
        (repeatSchedule ((List.finRange n).filter fun x => x ∈ F) t).length → Fin S =>
        observable (evalWord (pairStep (S := S) D) _ digits (D.lower, D.upper))) := by
    apply mean_congr
    intro digits
    rw [evalWord_pairStep]
    rfl
  rw [he, mean_evalWord]
  symm
  unfold pairMaskedStep
  simpa only [repeatSchedule_filter, decide_eq_true_eq] using
    averageRun_mask (pairStep (S := S) D) (fun x => decide (x ∈ F))
      (repeatSchedule (List.finRange n) t) (D.lower, D.upper) observable

end FullHistory

end SortingAdversary.Continuous.FiniteAveraging
