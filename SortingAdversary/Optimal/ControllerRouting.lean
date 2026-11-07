import SortingAdversary.Optimal.Safety

/-!
# A certified executable routing decision

The finite decision procedure below implements both safety tests. It returns
an all-retaining safe answer, a genuine same-colour delegation, or two feasible
safe branches for the probability oracle to compare. Its certificate is proved
from the weak-map invariant; no safety result is supplied by an oracle.

This is the routing part of the controller. Recursive pool storage, repairs,
and the approximation algorithm are separate components.
-/

namespace SortingAdversary.Optimal.ControllerRouting

open WeakMaps WeakMaps.WeakSystem Safety

variable {α : Type*} [Fintype α] {K : ℕ}

/-- The local invariant used when a physical comparison arrives. -/
structure Invariant (S : WeakSystem α (K + 1)) (pins : α → Option (Fin (K + 1))) : Prop where
  closed : S.Closed
  antisymm : ∀ u v, S.edge u v = true → S.edge v u = true → u = v
  feasible : ∃ f, S.Valid f
  pins_valid : ∀ f, S.Valid f → Routing.ExtendsPins pins f
  free_window : ∀ v, pins v = none → S.effectiveLower v < S.effectiveUpper v

def Inner (S : WeakSystem α (K + 1)) (pins : α → Option (Fin (K + 1)))
    (a b : α) : Prop :=
  Routing.InnerWitness (fun u v => S.edge u v = true) pins a b

instance innerDecidable (S : WeakSystem α (K + 1))
    (pins : α → Option (Fin (K + 1))) (a b : α) : Decidable (Inner S pins a b) := by
  unfold Inner Routing.InnerWitness
  infer_instance

/-- The window test runs on the actual closed branch. -/
def SingletonTest (S : WeakSystem α (K + 1)) (pins : α → Option (Fin (K + 1)))
    (a b : α) : Prop :=
  ∃ v, pins v = none ∧ (closedAdd S a b).effectiveLower v =
    (closedAdd S a b).effectiveUpper v

instance singletonDecidable (S : WeakSystem α (K + 1))
    (pins : α → Option (Fin (K + 1))) (a b : α) :
    Decidable (SingletonTest S pins a b) := by
  unfold SingletonTest
  infer_instance

def RetainsAll (S : WeakSystem α (K + 1)) (a b : α) : Prop :=
  ∀ f, S.Valid f → f a ≤ f b

/-- A stopping sign preserves all old inner orders and keeps each free
coordinate nonconstant. -/
def Safe (S : WeakSystem α (K + 1)) (pins : α → Option (Fin (K + 1)))
    (a b : α) : Prop :=
  ¬ Inner S pins a b ∧
    ∀ v, pins v = none →
      (closedAdd S a b).effectiveLower v < (closedAdd S a b).effectiveUpper v

theorem pin_complete {S : WeakSystem α (K + 1)} {pins : α → Option (Fin (K + 1))}
    (h : Invariant S pins) : Routing.PinComplete {f | S.Valid f} pins := by
  have hw := (S.feasible_iff_windows h.closed).mp h.feasible
  apply Routing.pin_complete_of_two_values h.feasible
    (fun f hf => h.pins_valid f hf)
  intro v hv
  exact ⟨S.effectiveLower, S.effectiveLower_valid h.closed hw,
    S.effectiveUpper, S.effectiveUpper_valid h.closed hw, ne_of_lt (h.free_window v hv)⟩

theorem inner_reverse {S : WeakSystem α (K + 1)} {pins : α → Option (Fin (K + 1))}
    (h : Invariant S pins) {a b : α} (hi : Inner S pins a b) : RetainsAll S b a := by
  intro f hf
  exact Routing.inner_witness_reverse hi hf.2 (h.pins_valid f hf)

theorem both_inner_delegate {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins) {a b : α}
    (hab : Inner S pins a b) (hba : Inner S pins b a) :
    ∃ c, pins a = some c ∧ pins b = some c := by
  exact Routing.both_inner_witnesses_delegate
    (fun f hf => ⟨hf.2, h.pins_valid f hf⟩) (pin_complete h) hab hba

theorem retaining_safe {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins) {a b : α}
    (hr : RetainsAll S a b) (hi : ¬ Inner S pins a b) : Safe S pins a b := by
  refine ⟨hi, ?_⟩
  intro v hv
  obtain ⟨hl, hu⟩ := retained_windows S h.closed h.feasible hr v
  rw [hl, hu]
  exact h.free_window v hv

theorem retaining_feasible {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins) {a b : α}
    (hr : RetainsAll S a b) : ∃ f, (closedAdd S a b).Valid f := by
  obtain ⟨f, hf⟩ := h.feasible
  exact ⟨f, (closedAdd_valid S h.closed a b f).mpr ⟨hf, hr f hf⟩⟩

theorem strict_reverse_excludes_inner {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins) {a b : α}
    (hw : ∃ f, S.Valid f ∧ f b < f a) : ¬ Inner S pins b a := by
  obtain ⟨f, hf, hs⟩ := hw
  exact Routing.strict_witness_excludes_inner hf.2 (h.pins_valid f hf) hs

theorem empty_reverse [DecidableEq α] {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins) {a b : α}
    (hz : (closedAdd S a b).count = 0) :
    RetainsAll S b a ∧ Safe S pins b a := by
  have hs : ∀ f, S.Valid f → f b < f a := by
    intro f hf
    apply lt_of_not_ge
    intro hle
    have hpos := (count_pos_iff (closedAdd S a b)).mpr
      ⟨f, (closedAdd_valid S h.closed a b f).mpr ⟨hf, hle⟩⟩
    omega
  have hr : RetainsAll S b a := fun f hf => (hs f hf).le
  refine ⟨hr, retaining_safe h hr (strict_reverse_excludes_inner h ?_)⟩
  obtain ⟨f, hf⟩ := h.feasible
  exact ⟨f, hf, hs f hf⟩

/-- Window infeasibility gives an all-retaining opposite without enumerating maps. -/
theorem infeasible_reverse {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins) {a b : α}
    (hn : ¬ ∀ v, (closedAdd S a b).effectiveLower v ≤
      (closedAdd S a b).effectiveUpper v) :
    RetainsAll S b a ∧ Safe S pins b a := by
  have hs : ∀ f, S.Valid f → f b < f a := by
    intro f hf
    apply lt_of_not_ge
    intro hle
    apply hn
    exact ((closedAdd S a b).feasible_iff_windows (closedAdd_closed S h.closed a b)).mp
      ⟨f, (closedAdd_valid S h.closed a b f).mpr ⟨hf, hle⟩⟩
  have hr : RetainsAll S b a := fun f hf => (hs f hf).le
  refine ⟨hr, retaining_safe h hr (strict_reverse_excludes_inner h ?_)⟩
  obtain ⟨f, hf⟩ := h.feasible
  exact ⟨f, hf, hs f hf⟩

theorem singleton_reverse {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins) {a b : α}
    (hba : S.edge b a ≠ true) (ht : SingletonTest S pins a b) :
    RetainsAll S b a ∧ Safe S pins b a := by
  obtain ⟨v, hv, he⟩ := ht
  obtain ⟨hr, hs⟩ := new_singleton_reverse S h.closed hba h.feasible
    (h.free_window v hv) he
  exact ⟨hr, retaining_safe h hr (strict_reverse_excludes_inner h hs)⟩

theorem safe_of_tests {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins) {a b : α}
    (hne : ∃ f, (closedAdd S a b).Valid f)
    (hi : ¬ Inner S pins a b) (hs : ¬ SingletonTest S pins a b) : Safe S pins a b := by
  refine ⟨hi, ?_⟩
  have hw := ((closedAdd S a b).feasible_iff_windows
    (closedAdd_closed S h.closed a b)).mp hne
  intro v hv
  rcases lt_or_eq_of_le (hw v) with hlt | heq
  · exact hlt
  · exact (hs ⟨v, hv, heq⟩).elim

/-- Taking either certified safe stopping branch preserves the complete
local invariant. Unknown public pairs are the only pairs passed here. -/
theorem safe_update {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins) {a b : α}
    (hba : S.edge b a ≠ true) (hs : Safe S pins a b)
    (hne : ∃ f, (closedAdd S a b).Valid f) : Invariant (closedAdd S a b) pins := by
  refine ⟨closedAdd_closed S h.closed a b, ?_, hne, ?_, hs.2⟩
  · intro u v huv hvu
    exact Routing.adjoin_antisymmetric
      (fun {x y z} hxy hyz => h.closed.trans x y z hxy hyz) h.antisymm hba u v
      ((closedAdd_edge S a b u v).mp huv) ((closedAdd_edge S a b v u).mp hvu)
  · intro f hf
    exact h.pins_valid f ((closedAdd_valid S h.closed a b f).mp hf).1

inductive Action where
  | forward
  | reverse
  | delegate
  | compareMasses
  deriving DecidableEq, Repr

/-- Each possible output carries the exact obligation needed by the caller. -/
def Specification (S : WeakSystem α (K + 1)) (pins : α → Option (Fin (K + 1)))
    (a b : α) : Action → Prop
  | .forward => RetainsAll S a b ∧ Safe S pins a b
  | .reverse => RetainsAll S b a ∧ Safe S pins b a
  | .delegate => ∃ c, pins a = some c ∧ pins b = some c
  | .compareMasses => Safe S pins a b ∧ Safe S pins b a ∧
      (∃ f, (closedAdd S a b).Valid f) ∧ (∃ f, (closedAdd S b a).Valid f)

/-- Executable finite routing with a kernel-checked certificate. The
certificate is erased by compilation. The two public-order tests have already
determined that the queried pair is incomparable.

Every test scans only vertices, pins, colours, and effective interval ends.
No test enumerates the set of feasible colour assignments.
-/
def chooseRoute (S : WeakSystem α (K + 1)) (pins : α → Option (Fin (K + 1)))
    (h : Invariant S pins) (a b : α) (hab : S.edge a b ≠ true) (hba : S.edge b a ≠ true) :
    { action : Action // Specification S pins a b action } :=
  if hf : ¬ ∀ v, (closedAdd S a b).effectiveLower v ≤
      (closedAdd S a b).effectiveUpper v then
    ⟨.reverse, infeasible_reverse h hf⟩
  else if hr : ¬ ∀ v, (closedAdd S b a).effectiveLower v ≤
      (closedAdd S b a).effectiveUpper v then
    ⟨.forward, infeasible_reverse h hr⟩
  else if hi : Inner S pins a b then
    if hj : Inner S pins b a then
      ⟨.delegate, both_inner_delegate h hi hj⟩
    else
      ⟨.reverse, inner_reverse h hi, retaining_safe h (inner_reverse h hi) hj⟩
  else if hj : Inner S pins b a then
    ⟨.forward, inner_reverse h hj, retaining_safe h (inner_reverse h hj) hi⟩
  else if hs : SingletonTest S pins a b then
    ⟨.reverse, singleton_reverse h hba hs⟩
  else if ht : SingletonTest S pins b a then
    ⟨.forward, singleton_reverse h hab ht⟩
  else
    have hnf : ∃ f, (closedAdd S a b).Valid f :=
      ((closedAdd S a b).feasible_iff_windows (closedAdd_closed S h.closed a b)).mpr
        (of_not_not hf)
    have hnr : ∃ f, (closedAdd S b a).Valid f :=
      ((closedAdd S b a).feasible_iff_windows (closedAdd_closed S h.closed b a)).mpr
        (of_not_not hr)
    ⟨.compareMasses, safe_of_tests h hnf hi hs, safe_of_tests h hnr hj ht, hnf, hnr⟩

end SortingAdversary.Optimal.ControllerRouting
