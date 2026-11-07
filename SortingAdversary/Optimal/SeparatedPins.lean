import SortingAdversary.Optimal.PoolState

/-!
# Every moved label retains a separated comparison mate

A promotion is charged only when it has a comparable distinct member in its
pool, either currently incident or retained by a path reservation. The
interior-admission certificate prevents those two labels from entering the
same child. This invariant is preserved through all later promotions and
fresh admissions; it supplies the unary-node retention argument in the tree.
-/

namespace SortingAdversary.Optimal.SeparatedPins

open PoolState

variable {n : ℕ}

def Comparable (p : Pool n) (x y : Fin n) : Prop :=
  p.system.edge x y = true ∨ p.system.edge y x = true

/-- Every physical pin has a comparable member outside its child. -/
def Separated (p : Pool n) : Prop :=
  ∀ x ∈ p.members, ∀ c, p.pins x = some c →
    ∃ y ∈ p.members, Comparable p x y ∧ p.pins y ≠ some c

/-- The actual comparison witness needed when moving a free label. -/
def HasMate (p : Pool n) (v : Fin n) : Prop :=
  ∃ w ∈ p.members, w ≠ v ∧ Comparable p v w

theorem option_map_ne {α β : Type*} (e : α → β) (he : Function.Injective e)
    (x : Option α) (c : α) (h : x ≠ some c) : x.map e ≠ some (e c) := by
  cases x with
  | none => simp
  | some d =>
      intro hd
      have heq : e d = e c := Option.some.inj hd
      exact h (congrArg some (he heq))

theorem admission_separated (p : Pool n) (v : Fin n) (hv : v ∉ p.members)
    (a : p.Admission v) (h : Separated p) : Separated a.next := by
  intro x hx c hpin
  have hxv : x ≠ v := by
    rintro rfl
    rw [a.pin_new] at hpin
    contradiction
  have hxm : x ∈ p.members := by
    rw [a.members_eq] at hx
    exact (Finset.mem_insert.mp hx).resolve_left hxv
  rw [a.pin_old x hxv] at hpin
  cases hp : p.pins x with
  | none => simp [hp] at hpin
  | some d =>
      have hc : a.embed d = c := by simpa [hp] using hpin
      subst c
      obtain ⟨y, hym, hcomp, hother⟩ := h x hxm d hp
      have hyv : y ≠ v := fun heq => hv (heq ▸ hym)
      refine ⟨y, a.members_eq ▸ Finset.mem_insert_of_mem hym, ?_, ?_⟩
      · simpa only [Comparable, a.edges] using hcomp
      · rw [a.pin_old y hyv]
        exact option_map_ne a.embed a.embed_strict.injective _ _ hother

/-- The promotion's independence certificate excludes an equal-colour mate
on either side of an already known comparison. -/
theorem new_pin_ne_old (p : Pool n) (v : Fin n) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c) {w : Fin n} {d : Fin (p.palette + 1)}
    (hw : p.pins w = some d) (hcomp : Comparable p v w) : r.embed d ≠ r.destination := by
  intro heq
  have hi := r.independent w d hw heq
  exact hcomp.elim hi.2 hi.1

/-- A checked promotion with a real comparison mate preserves separation for
the new pin and every older pin, including an older pin whose mate just moved. -/
theorem promotion_separated (p : Pool n) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (h : Separated p) (hm : HasMate p v) : Separated (p.installPromotion v hv c r) := by
  change ∀ x ∈ p.members, ∀ d : Fin (r.palette + 1), r.newPins x = some d →
    ∃ y ∈ p.members, (r.system.edge x y = true ∨ r.system.edge y x = true) ∧
      r.newPins y ≠ some d
  intro x hx d hpin
  change r.newPins x = some d at hpin
  by_cases hxv : x = v
  · subst x
    have hd : r.destination = d := by
      rw [Promotion.promoted_pin] at hpin
      exact Option.some.inj hpin
    subst d
    obtain ⟨w, hwm, hwv, hcomp⟩ := hm
    refine ⟨w, hwm, ?_, ?_⟩
    · simpa only [Comparable, Pool.installPromotion, r.edges] using hcomp
    · rw [Promotion.other_pin p.system p.pins v c r hwv]
      cases hpw : p.pins w with
      | none => simp
      | some e =>
          simp only [Option.map_some, ne_eq, Option.some.injEq]
          exact new_pin_ne_old p v c r hpw hcomp
  · rw [Promotion.other_pin p.system p.pins v c r hxv] at hpin
    cases hpx : p.pins x with
    | none => simp [hpx] at hpin
    | some e =>
        have hd : r.embed e = d := Option.some.inj (by
          simpa only [hpx, Option.map_some] using hpin)
        subst d
        obtain ⟨w, hwm, hcomp, hother⟩ := h x hx e hpx
        refine ⟨w, hwm, ?_, ?_⟩
        · simpa only [Comparable, Pool.installPromotion, r.edges] using hcomp
        · by_cases hwv : w = v
          · subst w
            rw [Promotion.promoted_pin]
            simp only [ne_eq, Option.some.injEq]
            exact (new_pin_ne_old p v c r hpx (hcomp.symm)).symm
          · rw [Promotion.other_pin p.system p.pins v c r hwv]
            exact option_map_ne r.embed r.embed_strict.injective _ _ hother

theorem empty_separated (n : ℕ) : Separated (emptyPool n) := by
  intro x hx
  simp [emptyPool] at hx

theorem root_separated (N : ℕ) : Separated (initialRoot N) := by
  intro x hx c hc
  simp [initialRoot] at hc

end SortingAdversary.Optimal.SeparatedPins
