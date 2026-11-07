import SortingAdversary.Optimal.MeasuredWidthTypes
import SortingAdversary.Optimal.MeasuredEarlyMove
import SortingAdversary.Optimal.RepairSelectWork

/-!
# A counted execution of cheap pins and strict cuts

Each iteration runs the measured selector and executes precisely its chosen
move. The recursive call receives the newly cached state; the original
normalizer appears only in the erased equality certificate. Termination and
work both use the strict decrease of the actual free-label/active-row measure.
-/

namespace SortingAdversary.Optimal.MeasuredEarlyNormalize

open PrimitiveWork RepresentationWork WidthRepair

variable {n : ℕ} {s : State n}

def prepend (p : WidthParameters) (hB : ComparableBound s p.B) (move : EarlyMove s p.W₀ p.L)
    (next : Σ t : State n, Step s t) (actual : next = move.execute p hB)
    (rest : EarlyResult next.1 p) : EarlyResult s p where
  final := rest.final
  trace := .cons next.2 rest.trace
  events := by
    subst next
    exact .cons hB move rest.trace rest.events
  incident := by
    refine ⟨?_, rest.trace.incidentFrom_mono next.2.active_old rest.incident⟩
    subst next
    exact move.execute_incident p hB
  bound := rest.bound
  normal := rest.normal

theorem prepend_actual (p : WidthParameters) (hB : ComparableBound s p.B)
    (move : EarlyMove s p.W₀ p.L) (selected : selectEarly s p.W₀ p.L = some move)
    (next : Σ t : State n, Step s t) (actual : next = move.execute p hB)
    (rest : EarlyResult next.1 p)
    (rest_actual : rest = WidthRepair.normalizeEarly next.1 p (comparableBound_step next.2 hB)) :
    prepend p hB move next actual rest = WidthRepair.normalizeEarly s p hB := by
  subst next
  subst rest
  conv_rhs => unfold WidthRepair.normalizeEarly
  split
  · rename_i hnone
    have hbad : some move = none := selected.symm.trans hnone
    cases hbad
  · rename_i chosen hchosen
    have heq : chosen = move := Option.some.inj (hchosen.symm.trans selected)
    subst chosen
    rfl

def normalizeEarly {s : State n} (a : LocalAccess s) (ha : AccessBound a 2)
    (p : WidthParameters) (hB : ComparableBound s p.B) : Result (Output s p hB) :=
  let selected := RepairSelectWork.early a p.W₀ p.L
  match hs : selected.value with
  | none =>
    have hn : selectEarly s p.W₀ p.L = none := (RepairSelectWork.early_value a p.W₀ p.L).symm.trans hs
    let result : EarlyResult s p :=
      ⟨s, .nil s, .nil s, trivial, hB, (selectEarly_none s p.W₀ p.L).mp hn⟩
    ⟨⟨result, a, (by
        conv_rhs => unfold WidthRepair.normalizeEarly
        split
        · rfl
        · rename_i chosen hchosen
          have hbad : none = some chosen := hn.symm.trans hchosen
          cases hbad), ha⟩, selected.work + 8⟩
  | some move =>
    have hs' : selectEarly s p.W₀ p.L = some move := (RepairSelectWork.early_value a p.W₀ p.L).symm.trans hs
    let moved := MeasuredEarlyMove.execute a p hB move
    let next : Σ t : State n, Step s t := ⟨moved.value.next, moved.value.step⟩
    let rest := normalizeEarly (s := moved.value.next) moved.value.access moved.value.cached p (comparableBound_step next.2 hB)
    let result := prepend p hB move next moved.value.actual rest.value.result
    ⟨⟨result, rest.value.access,
        prepend_actual p hB move hs' next moved.value.actual rest.value.result rest.value.actual,
        rest.value.cached⟩,
      selected.work + moved.work + rest.work + 16⟩
termination_by s.measure
decreasing_by exact (MeasuredEarlyMove.execute a p hB move).value.step.measure_lt

@[simp] theorem normalizeEarly_actual (a : LocalAccess s) (ha : AccessBound a 2)
    (p : WidthParameters) (hB : ComparableBound s p.B) :
    (normalizeEarly a ha p hB).value.result = WidthRepair.normalizeEarly s p hB :=
  (normalizeEarly a ha p hB).value.actual

def kernelBound (n palette : ℕ) (p : WidthParameters) : ℕ :=
  RepairSelectWork.earlyBound n 2 + MeasuredEarlyMove.workBound n palette 2 p + 16

theorem step_potential {t : State n} (step : Step s t) :
    t.pool.palette + t.measure ≤ s.pool.palette + s.measure := by
  have hp := step_palette_le step
  have hm := step.measure_lt
  omega

theorem normalizeEarly_work_budget {s : State n} (a : LocalAccess s) (ha : AccessBound a 2)
    (p : WidthParameters) (hB : ComparableBound s p.B) (K : ℕ)
    (hK : s.pool.palette + s.measure ≤ K) :
    (normalizeEarly a ha p hB).work ≤ (s.measure + 1) * kernelBound n K p := by
  unfold normalizeEarly
  dsimp only
  split
  · have hs := RepairSelectWork.early_work_le a ha p.W₀ p.L
    have hm : RepairSelectWork.earlyBound n 2 + 8 ≤ kernelBound n K p := by
      unfold kernelBound
      omega
    have hmul := Nat.le_mul_of_pos_left (kernelBound n K p) (by omega : 0 < s.measure + 1)
    dsimp only
    omega
  · rename_i move selected
    let moved := MeasuredEarlyMove.execute a p hB move
    have hpot := step_potential moved.value.step
    have hnext : moved.value.next.pool.palette + moved.value.next.measure ≤ K := hpot.trans hK
    have ih := normalizeEarly_work_budget (s := moved.value.next) moved.value.access moved.value.cached p
      (comparableBound_step moved.value.step hB) K hnext
    have hs := RepairSelectWork.early_work_le a ha p.W₀ p.L
    have hm := MeasuredEarlyMove.execute_work_le a ha p hB move
    have hmono := MeasuredEarlyMove.workBound_mono (n := n) (A := 2) p
      ((Nat.le_add_right s.pool.palette s.measure).trans hK)
    have hmeasure := moved.value.step.measure_lt
    have hmul := Nat.mul_le_mul_right (kernelBound n K p)
      (Nat.succ_le_of_lt hmeasure)
    change _ + _ + _ + 16 ≤ _
    change moved.work ≤ _ at hm
    change (normalizeEarly moved.value.access moved.value.cached p
      (comparableBound_step moved.value.step hB)).work ≤ _ at ih
    simp only [kernelBound, Nat.succ_eq_add_one] at hmul ih ⊢
    dsimp only [moved] at hm ih hmul
    rw [Nat.add_mul, one_mul]
    omega
termination_by s.measure
decreasing_by exact moved.value.step.measure_lt

theorem normalizeEarly_work_le (a : LocalAccess s) (ha : AccessBound a 2)
    (p : WidthParameters) (hB : ComparableBound s p.B) :
    (normalizeEarly a ha p hB).work ≤
      (s.measure + 1) * kernelBound n (s.pool.palette + s.measure) p :=
  normalizeEarly_work_budget a ha p hB _ le_rfl

end SortingAdversary.Optimal.MeasuredEarlyNormalize
