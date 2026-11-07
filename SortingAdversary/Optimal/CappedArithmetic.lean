import SortingAdversary.Optimal.Parameters
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Capped arithmetic for uniform parameter construction

Rejected stages must not construct their enormous reference integers. These
routines stop as soon as a checked intermediate exceeds the budget. Powers
use repeated squaring, and every multiplication has two already bounded
operands. The counters describe this actual evaluator, including failures.
-/

namespace SortingAdversary.Optimal.CappedArithmetic

structure Run where
  value : Option ℕ
  work : ℕ
  peak : ℕ
  deriving Repr

def checked (cap value : ℕ) : Option ℕ := if value ≤ cap then some value else none

@[simp] theorem checked_some {cap value answer : ℕ} :
    checked cap value = some answer ↔ value = answer ∧ value ≤ cap := by
  unfold checked
  split_ifs <;> simp_all <;> omega

/-- Repeated squaring with a cap check before an odd final multiplication.
No call constructs `a^e` as an unbounded intermediate. -/
def power (cap a : ℕ) (e : ℕ) : Run :=
  if he : e = 0 then ⟨checked cap 1, 1, 1⟩ else
    let half := power cap a (e / 2)
    match half.value with
    | none => ⟨none, half.work + 1, half.peak⟩
    | some b =>
      let square := b * b
      if square ≤ cap then
        if e % 2 = 0 then ⟨some square, half.work + 4, max half.peak square⟩
        else ⟨checked cap (square * a), half.work + 5, max half.peak (max square (square * a))⟩
      else ⟨none, half.work + 3, max half.peak square⟩
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide)

private theorem even_power (a e : ℕ) (he : e % 2 = 0) : a ^ e = a ^ (e / 2) * a ^ (e / 2) := by
  have h : e = e / 2 + e / 2 := by omega
  conv_lhs => rw [h, pow_add]

private theorem odd_power (a e : ℕ) (he : e % 2 ≠ 0) : a ^ e = (a ^ (e / 2) * a ^ (e / 2)) * a := by
  have hm : e % 2 < 2 := Nat.mod_lt _ (by decide)
  have h : e = e / 2 + e / 2 + 1 := by omega
  conv_lhs => rw [h, pow_succ, pow_add]

theorem power_sound (cap a e : ℕ) {answer : ℕ} (h : (power cap a e).value = some answer) :
    answer = a ^ e ∧ answer ≤ cap := by
  induction e using Nat.strong_induction_on generalizing answer with
  | h e ih =>
    rw [power] at h
    split at h
    · rename_i he
      subst e
      have hc := checked_some.mp h
      exact ⟨hc.1.symm, hc.1 ▸ hc.2⟩
    · rename_i he
      dsimp only at h
      split at h
      · contradiction
      · rename_i b hb
        have hs := ih (e / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide)) hb
        split at h
        · rename_i hsq
          split at h
          · rename_i heven
            have ha : b * b = answer := Option.some.inj h
            exact ⟨ha.symm.trans (by rw [hs.1, ← even_power a e heven]), ha ▸ hsq⟩
          · rename_i hodd
            have hc := checked_some.mp h
            exact ⟨hc.1.symm.trans (by rw [hs.1, ← odd_power a e hodd]), hc.1 ▸ hc.2⟩
        · contradiction

private theorem small_power {cap a e k : ℕ} (hcap : 1 ≤ cap) (hk : k ≤ e) (he : a ^ e ≤ cap) :
    a ^ k ≤ cap := by
  by_cases ha : a = 0
  · subst a
    by_cases hk0 : k = 0
    · simpa [hk0] using hcap
    · simp [zero_pow hk0]
  · exact (Nat.pow_le_pow_right (Nat.pos_of_ne_zero ha) hk).trans he

theorem power_complete (cap a e : ℕ) (hcap : 1 ≤ cap) (he : a ^ e ≤ cap) :
    (power cap a e).value = some (a ^ e) := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    rw [power]
    split
    · rename_i hz
      subst e
      simp [checked, hcap]
    · rename_i hz
      have hh := small_power hcap (Nat.div_le_self e 2) he
      dsimp only
      rw [ih (e / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hz) (by decide)) hh]
      have hs : a ^ (e / 2) * a ^ (e / 2) ≤ cap := by
        rw [← pow_add]
        exact small_power hcap (by omega) he
      simp only [if_pos hs]
      by_cases hp : e % 2 = 0
      · simp only [if_pos hp, even_power a e hp]
      · simp only [if_neg hp, checked]
        rw [← odd_power a e hp]
        simp only [if_pos he]

theorem power_work (cap a e : ℕ) : (power cap a e).work ≤ 5 * (e + 1) := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    rw [power]
    split
    · dsimp only; omega
    · rename_i he
      have hh := ih (e / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide))
      dsimp only
      split <;> (try split_ifs) <;> dsimp only <;> omega

/-- Every multiplication result checked by the power routine has at most
the square of the cap as its magnitude. -/
theorem power_peak (cap a e : ℕ) (ha : a ≤ cap) : (power cap a e).peak ≤ max 1 (cap * cap) := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    rw [power]
    split
    · exact le_max_left _ _
    · rename_i he
      have hh := ih (e / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide))
      dsimp only
      split
      · exact hh
      · rename_i b hb
        have hbc := (power_sound cap a (e / 2) hb).2
        have hs := (Nat.mul_le_mul hbc hbc).trans (le_max_right 1 (cap * cap))
        split
        · rename_i hsq
          split
          · exact max_le hh hs
          · exact max_le hh (max_le hs ((Nat.mul_le_mul hsq ha).trans (le_max_right _ _)))
        · exact max_le hh hs

/-- A fixed arithmetic recipe. The only varying leaf is the stage index. -/
inductive Expr where
  | input
  | lit (n : ℕ)
  | add (a b : Expr)
  | mul (a b : Expr)
  | maximum (a b : Expr)
  | pow (a b : Expr)
  deriving Repr

namespace Expr

def value (j : ℕ) : Expr → ℕ
  | .input => j
  | .lit a => a
  | .add a b => a.value j + b.value j
  | .mul a b => a.value j * b.value j
  | .maximum a b => max (a.value j) (b.value j)
  | .pow a b => a.value j ^ b.value j

def nodes : Expr → ℕ
  | .input | .lit _ => 1
  | .add a b | .mul a b | .maximum a b | .pow a b => a.nodes + b.nodes + 1

def literalMax : Expr → ℕ
  | .input => 0
  | .lit a => a
  | .add a b | .mul a b | .maximum a b | .pow a b => max a.literalMax b.literalMax

/-- A reference bound includes every subtree, not just the final answer.
It appears only in specifications and in the eventual-affordability proof. -/
def need (j : ℕ) : Expr → ℕ
  | .input => max 1 j
  | .lit a => max 1 a
  | .add a b => max (a.need j) (max (b.need j) (a.value j + b.value j))
  | .mul a b => max (a.need j) (max (b.need j) (a.value j * b.value j))
  | .maximum a b => max (a.need j) (b.need j)
  | .pow a b => max (a.need j) (max (b.need j) (a.value j ^ b.value j))

theorem value_le_need (j : ℕ) (e : Expr) : e.value j ≤ e.need j := by
  induction e with
  | input => exact le_max_right _ _
  | lit a => exact le_max_right _ _
  | add a b _ _ | mul a b _ _ | pow a b _ _ => exact (le_max_right _ _).trans (le_max_right _ _)
  | maximum a b ha hb => exact max_le_max ha hb

theorem one_le_need (j : ℕ) (e : Expr) : 1 ≤ e.need j := by
  induction e with
  | input => exact le_max_left _ _
  | lit a => exact le_max_left _ _
  | add a b ha _ | mul a b ha _ | pow a b ha _ | maximum a b ha _ => exact ha.trans (le_max_left _ _)

/-- Sequential evaluation short-circuits after an overflowing subtree. -/
def eval (cap j : ℕ) : Expr → Run
  | .input => ⟨checked cap j, 1, j⟩
  | .lit a => ⟨checked cap a, 1, a⟩
  | .add a b =>
    let left := a.eval cap j
    match left.value with
    | none => left
    | some x =>
      let right := b.eval cap j
      match right.value with
      | none => ⟨none, left.work + right.work, max left.peak right.peak⟩
      | some y => ⟨checked cap (x + y), left.work + right.work + 2, max (max left.peak right.peak) (x + y)⟩
  | .mul a b =>
    let left := a.eval cap j
    match left.value with
    | none => left
    | some x =>
      let right := b.eval cap j
      match right.value with
      | none => ⟨none, left.work + right.work, max left.peak right.peak⟩
      | some y => ⟨checked cap (x * y), left.work + right.work + 2, max (max left.peak right.peak) (x * y)⟩
  | .maximum a b =>
    let left := a.eval cap j
    match left.value with
    | none => left
    | some x =>
      let right := b.eval cap j
      match right.value with
      | none => ⟨none, left.work + right.work, max left.peak right.peak⟩
      | some y => ⟨some (max x y), left.work + right.work + 1, max left.peak right.peak⟩
  | .pow a b =>
    let left := a.eval cap j
    match left.value with
    | none => left
    | some x =>
      let right := b.eval cap j
      match right.value with
      | none => ⟨none, left.work + right.work, max left.peak right.peak⟩
      | some y =>
        let out := power cap x y
        ⟨out.value, left.work + right.work + out.work, max (max left.peak right.peak) out.peak⟩

theorem eval_sound (cap j : ℕ) (e : Expr) (hcap : 1 ≤ cap) {answer : ℕ}
    (h : (e.eval cap j).value = some answer) : answer = e.value j ∧ e.need j ≤ cap := by
  induction e generalizing answer with
  | input | lit _ =>
    have hc := checked_some.mp h
    exact ⟨hc.1.symm, max_le hcap hc.2⟩
  | add a b iha ihb | mul a b iha ihb | maximum a b iha ihb | pow a b iha ihb =>
    dsimp only [eval] at h
    cases ha : (a.eval cap j).value with
    | none => simp only [ha] at h; contradiction
    | some x =>
      simp only [ha] at h
      have hx := iha ha
      cases hb : (b.eval cap j).value with
      | none => simp only [hb] at h; contradiction
      | some y =>
        simp only [hb] at h
        have hy := ihb hb
        first
        | have ho := checked_some.mp h
          refine ⟨ho.1.symm.trans ?_, max_le hx.2 (max_le hy.2 ?_)⟩
          · simp only [value, hx.1, hy.1]
          · simpa only [hx.1, hy.1] using ho.2
        | have ho := power_sound cap x y h
          refine ⟨ho.1.trans ?_, max_le hx.2 (max_le hy.2 ?_)⟩
          · simp only [value, hx.1, hy.1]
          · simpa only [← hx.1, ← hy.1, ← ho.1] using ho.2
        | have ho := Option.some.inj h
          exact ⟨ho.symm.trans (by simp only [value, hx.1, hy.1]), max_le hx.2 hy.2⟩

theorem eval_complete (cap j : ℕ) (e : Expr) (hneed : e.need j ≤ cap) :
    (e.eval cap j).value = some (e.value j) := by
  have hcap := (e.one_le_need j).trans hneed
  induction e with
  | input | lit _ =>
    exact checked_some.mpr ⟨rfl, (le_max_right _ _).trans hneed⟩
  | add a b iha ihb | mul a b iha ihb | maximum a b iha ihb | pow a b iha ihb =>
    have ha : a.need j ≤ cap := (le_max_left _ _).trans hneed
    have hb : b.need j ≤ cap := by
      first
      | exact (le_max_left _ _).trans ((le_max_right _ _).trans hneed)
      | exact (le_max_right _ _).trans hneed
    simp only [eval, iha ha, ihb hb]
    first
    | exact checked_some.mpr ⟨rfl, (le_max_right _ _).trans ((le_max_right _ _).trans hneed)⟩
    | exact power_complete cap _ _ hcap ((le_max_right _ _).trans ((le_max_right _ _).trans hneed))
    | rfl

theorem eval_some_iff (cap j : ℕ) (e : Expr) (hcap : 1 ≤ cap) (answer : ℕ) :
    (e.eval cap j).value = some answer ↔ answer = e.value j ∧ e.need j ≤ cap := by
  constructor
  · exact e.eval_sound cap j hcap
  · rintro ⟨rfl, hneed⟩
    exact e.eval_complete cap j hneed

theorem eval_isSome (cap j : ℕ) (e : Expr) (hcap : 1 ≤ cap) :
    (e.eval cap j).value.isSome = true ↔ e.need j ≤ cap := by
  cases he : (e.eval cap j).value with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    intro hneed
    have h := e.eval_complete cap j hneed
    rw [he] at h
    contradiction
  | some value =>
    simp only [Option.isSome_some, true_iff]
    exact (e.eval_sound cap j hcap he).2

theorem eval_work (cap j : ℕ) (e : Expr) (hcap : 1 ≤ cap) :
    (e.eval cap j).work ≤ e.nodes * (5 * (cap + 1) + 2) := by
  induction e with
  | input | lit _ => simp only [eval, nodes]; omega
  | add a b iha ihb | mul a b iha ihb | maximum a b iha ihb | pow a b iha ihb =>
    dsimp only [eval, nodes]
    cases ha : (a.eval cap j).value with
    | none => simp only [ha]; nlinarith
    | some x =>
      simp only [ha]
      cases hb : (b.eval cap j).value with
      | none => simp only [hb]; nlinarith
      | some y =>
        simp only [hb]
        first
        | nlinarith
        | have hy := (b.value_le_need j).trans (b.eval_sound cap j hcap hb).2
          have hyeq := (b.eval_sound cap j hcap hb).1
          have hp := power_work cap x y
          rw [← hyeq] at hy
          nlinarith

theorem eval_peak (cap j M : ℕ) (e : Expr) (hcap : 1 ≤ cap)
    (hj : j ≤ cap) (hM : e.literalMax ≤ M) :
    (e.eval cap j).peak ≤ (cap + M + 1) ^ 2 := by
  have hc : cap ≤ (cap + M + 1) ^ 2 := by nlinarith
  have hmul : cap * cap ≤ (cap + M + 1) ^ 2 := by nlinarith
  have hadd : cap + cap ≤ (cap + M + 1) ^ 2 := by nlinarith
  induction e with
  | input => exact hj.trans hc
  | lit a =>
    change a ≤ _
    change a ≤ M at hM
    nlinarith
  | add a b iha ihb | mul a b iha ihb | maximum a b iha ihb | pow a b iha ihb =>
    have hl := iha ((le_max_left _ _).trans hM)
    have hr := ihb ((le_max_right _ _).trans hM)
    dsimp only [eval]
    cases ha : (a.eval cap j).value with
    | none => simpa only [ha] using hl
    | some x =>
      simp only [ha]
      have hx : x ≤ cap := by
        have hs := a.eval_sound cap j hcap ha
        exact hs.1 ▸ ((a.value_le_need j).trans hs.2)
      cases hb : (b.eval cap j).value with
      | none => simpa only [hb] using max_le hl hr
      | some y =>
        simp only [hb]
        have hy : y ≤ cap := by
          have hs := b.eval_sound cap j hcap hb
          exact hs.1 ▸ ((b.value_le_need j).trans hs.2)
        first
        | exact max_le (max_le hl hr) ((Nat.add_le_add hx hy).trans hadd)
        | exact max_le (max_le hl hr) ((Nat.mul_le_mul hx hy).trans hmul)
        | exact max_le hl hr
        | exact max_le (max_le hl hr) ((power_peak cap x y hx).trans
            (max_le (by nlinarith) hmul))

theorem eval_bits (cap j M : ℕ) (e : Expr) (hcap : 1 ≤ cap)
    (hj : j ≤ cap) (hM : e.literalMax ≤ M) :
    Nat.size (e.eval cap j).peak ≤ Nat.size ((cap + M + 1) ^ 2) :=
  Nat.size_le_size (e.eval_peak cap j M hcap hj hM)

end Expr

end SortingAdversary.Optimal.CappedArithmetic
