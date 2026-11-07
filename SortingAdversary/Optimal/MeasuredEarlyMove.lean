import SortingAdversary.Optimal.CentralChoiceWork
import SortingAdversary.Optimal.WidthScalarWork
import SortingAdversary.Optimal.MeasuredPin
import SortingAdversary.Optimal.RepresentationShape

/-!
# Measured W1 and W2 transitions

The branch comes from the measured early selector. Cheap pins use the
measured first central colour; strict cuts compute their propagated threshold
once. Every next state is rebuilt from its cached getters before execution
continues. Reference transitions occur only in erased equalities.
-/

namespace SortingAdversary.Optimal.MeasuredEarlyMove

open PrimitiveWork RepresentationWork WidthRepair

variable {n : ℕ} {s : State n}

structure Output (expected : Σ t : State n, Step s t) where
  next : State n
  step : Step s next
  access : LocalAccess next
  actual : (⟨next, step⟩ : Σ t : State n, Step s t) = expected
  cached : AccessBound access 2

theorem sigma_transport {α : Type} (β : α → Type) {x y : α} (h : x = y) (v : β x) :
    (⟨y, h ▸ v⟩ : Sigma β) = ⟨x, v⟩ := by
  cases h
  rfl

theorem cheap_retained (s : State n) (p : WidthParameters) (hB : ComparableBound s p.B)
    (v : Fin n) (incident : (GraphBalls.neighbors s.rows.active v).Nonempty) (narrow : s.width v < p.W₀)
    (c : Fin (s.pool.palette + 1)) (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v)
    (hcolour : c = s.centralColour v) (charge : ℚ) (hcharge : charge = p.cheapCharge) :
    (s.pool.system.count : ℚ) ≤ charge *
      (Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v
        (s.nonisolated_free incident) c hc).system.count := by
  subst c
  subst charge
  exact (s.cheapUpdate p hB v incident narrow).retained

def package {t : State n} (transition : Step s t) (a : LocalAccess t)
    (palette : ℕ) (members : Finset (Fin n))
    (hp : palette = t.pool.palette) (hm : members = t.pool.members)
    (h : AccessBound a 2) (expected : Σ u : State n, Step s u)
    (heq : (⟨t, transition⟩ : Σ u : State n, Step s u) = expected) : Output expected where
  next := a.realizeWith palette members hp hm
  step := (a.realizeWith_eq palette members hp hm).symm ▸ transition
  access := a.rebasedWith palette members hp hm
  actual := by
    have hr := a.realizeWith_eq palette members hp hm
    calc
      (⟨a.realizeWith palette members hp hm, hr.symm ▸ transition⟩ : Σ u : State n, Step s u) = ⟨t, transition⟩ :=
        sigma_transport (fun u => Step s u) hr.symm transition
      _ = expected := heq
  cached := a.rebasedWith_bound palette members hp hm h

def execute (a : LocalAccess s) (p : WidthParameters) (hB : ComparableBound s p.B)
    (move : EarlyMove s p.W₀ p.L) : Result (Output (move.execute p hB)) :=
  match move with
  | .cheap v incident narrow =>
    let chosen := CentralChoiceWork.colour a v
    let charge := WidthScalarWork.cheap p
    have hc : s.pool.system.effectiveLower v ≤ chosen.value ∧
        chosen.value ≤ s.pool.system.effectiveUpper v := by
      rw [CentralChoiceWork.colour_value]
      exact s.centralColour_window v
    have retained : (s.pool.system.count : ℚ) ≤ charge.value *
        (Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v
          (s.nonisolated_free incident) chosen.value hc).system.count := by
      exact cheap_retained s p hB v incident narrow chosen.value hc
        (CentralChoiceWork.colour_value a v) charge.value (WidthScalarWork.cheap_value p)
    let pin := MeasuredPin.pin a v (s.nonisolated_free incident) chosen.value hc
      (s.nonisolated_mate incident) charge.value retained
    have heq : pin.value.update = s.cheapUpdate p hB v incident narrow := by
      apply pin.value.exact.trans
      apply MeasuredPin.update_ext
      · rfl
      · exact CentralChoiceWork.colour_value a v
      · exact WidthScalarWork.cheap_value p
    let result := package (.pin pin.value.update) pin.value.access
      pin.value.update.result.palette s.pool.members rfl rfl pin.value.bounded
      ((EarlyMove.cheap v incident narrow).execute p hB)
        (congrArg (fun update : PinUpdate s => (⟨update.next, .pin update⟩ : Σ t : State n, Step s t)) heq)
    ⟨result, chosen.work + charge.work + pin.work + 24⟩
  | .lower u v live steep =>
    let ratio := (Nat.mul_le_mul_right (s.width v) p.two_le_L).trans_lt steep
    let charge := WidthScalarWork.cut p
    have retained : (s.pool.system.count : ℚ) ≤ charge.value * (s.lowerCut u v live ratio).pool.system.count := by
      rw [WidthScalarWork.cut_value]
      exact s.lower_cut_charge p hB u v live steep ratio
    let transition := Step.lowerCut s u v live ratio charge.value retained
    let updated := a.lowerCutCached u v live ratio
    ⟨package transition updated.value s.pool.palette s.pool.members rfl rfl
        (a.lowerCutCached_access u v live ratio)
        ((EarlyMove.lower u v live steep).execute p hB) (by
          simp only [transition, charge, WidthScalarWork.cut_value, EarlyMove.execute]),
      charge.work + updated.work + 24⟩
  | .upper u v live steep =>
    let ratio := (Nat.mul_le_mul_right (s.width u) p.two_le_L).trans_lt steep
    let charge := WidthScalarWork.cut p
    have retained : (s.pool.system.count : ℚ) ≤ charge.value * (s.upperCut u v live ratio).pool.system.count := by
      rw [WidthScalarWork.cut_value]
      exact s.upper_cut_charge p hB u v live steep ratio
    let transition := Step.upperCut s u v live ratio charge.value retained
    let updated := a.upperCutCached u v live ratio
    ⟨package transition updated.value s.pool.palette s.pool.members rfl rfl
        (a.upperCutCached_access u v live ratio)
        ((EarlyMove.upper u v live steep).execute p hB) (by
          simp only [transition, charge, WidthScalarWork.cut_value, EarlyMove.execute]),
      charge.work + updated.work + 24⟩

def workBound (n palette A : ℕ) (p : WidthParameters) : ℕ :=
  CentralChoiceWork.workBound n A + 1 + (2 * p.B + 4) +
    WidthScalarWork.cutBound p + MeasuredPin.workBound n palette A + 24

theorem execute_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (p : WidthParameters) (hB : ComparableBound s p.B) (move : EarlyMove s p.W₀ p.L) :
    (execute a p hB move).work ≤ workBound n s.pool.palette A p := by
  cases move with
  | cheap v incident narrow =>
    have hc := CentralChoiceWork.colour_work_le a h v
    have hp := MeasuredPin.pin_work_le a h v (s.nonisolated_free incident)
      (CentralChoiceWork.colour a v).value
      (by rw [CentralChoiceWork.colour_value]; exact s.centralColour_window v)
      (s.nonisolated_mate incident) (WidthScalarWork.cheap p).value
      (cheap_retained s p hB v incident narrow (CentralChoiceWork.colour a v).value
        (by rw [CentralChoiceWork.colour_value]; exact s.centralColour_window v)
        (CentralChoiceWork.colour_value a v) _ (WidthScalarWork.cheap_value p))
    simp only [execute, WidthScalarWork.cheap_work]
    unfold workBound
    omega
  | lower u v live steep =>
    let ratio := (Nat.mul_le_mul_right (s.width v) p.two_le_L).trans_lt steep
    have hu := a.lowerCutCached_work_le h u v live ratio
    have hc := WidthScalarWork.cut_work_le p
    have hm := LocalAccess.cacheBound_mono (n := n) (A := 2 * A + 16)
      (Nat.le_succ s.pool.palette) le_rfl
    simp only [execute]
    unfold workBound MeasuredPin.workBound
    simp only [Nat.succ_eq_add_one] at hm
    omega
  | upper u v live steep =>
    let ratio := (Nat.mul_le_mul_right (s.width u) p.two_le_L).trans_lt steep
    have hu := a.upperCutCached_work_le h u v live ratio
    have hc := WidthScalarWork.cut_work_le p
    have hm := LocalAccess.cacheBound_mono (n := n) (A := 2 * A + 16)
      (Nat.le_succ s.pool.palette) le_rfl
    simp only [execute]
    unfold workBound MeasuredPin.workBound
    simp only [Nat.succ_eq_add_one] at hm
    omega

theorem workBound_mono {n K L A : ℕ} (p : WidthParameters) (hK : K ≤ L) :
    workBound n K A p ≤ workBound n L A p := by
  unfold workBound MeasuredPin.workBound
  have h := LocalAccess.cacheBound_mono (n := n) (A := 2 * A + 16) (Nat.succ_le_succ hK) le_rfl
  simp only [Nat.succ_eq_add_one] at h
  omega

end SortingAdversary.Optimal.MeasuredEarlyMove
