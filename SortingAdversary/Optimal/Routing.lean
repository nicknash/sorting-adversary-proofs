import Mathlib.Data.Set.Basic

/-!
# The order-theoretic safety rules for recursive colour pools

These are the routing lemmas in sections 1–2 of the 7 November 2026 manuscript.
`R` is the reflexive public order, whereas a represented colour map need only
respect `R` weakly.  A physical pin keeps its original colour identity.

The statements below are local lemmas, not a construction of the complete
recursive adversary.  In particular the non-singleton and pin-completeness
invariants are hypotheses here, rather than an asserted controller invariant.
-/

namespace SortingAdversary.Optimal.Routing

variable {α β : Type*}

/-- The closed relation after adjoining `a ≤ b` to an already closed relation.
The second disjunct describes a path using the new edge exactly once. -/
def adjoin (R : α → α → Prop) (a b x y : α) : Prop :=
  R x y ∨ (R x a ∧ R b y)

theorem adjoin_old {R : α → α → Prop} {a b x y : α} (h : R x y) :
    adjoin R a b x y := Or.inl h

theorem adjoin_edge {R : α → α → Prop} (hrefl : ∀ x, R x x) (a b : α) :
    adjoin R a b a b := Or.inr ⟨hrefl a, hrefl b⟩

theorem adjoin_reflexive {R : α → α → Prop} (hrefl : ∀ x, R x x) (a b : α) :
    ∀ x, adjoin R a b x x := fun x => Or.inl (hrefl x)

/-- Repeated uses of the same inserted edge do not create additional pairs. -/
theorem adjoin_transitive {R : α → α → Prop}
    (htrans : ∀ ⦃x y z⦄, R x y → R y z → R x z) (a b : α) :
    ∀ ⦃x y z⦄, adjoin R a b x y → adjoin R a b y z → adjoin R a b x z := by
  intro x y z hxy hyz
  rcases hxy with hxy | ⟨hxa, hby⟩
  · rcases hyz with hyz | ⟨hya, hbz⟩
    · exact Or.inl (htrans hxy hyz)
    · exact Or.inr ⟨htrans hxy hya, hbz⟩
  · rcases hyz with hyz | ⟨_, hbz⟩
    · exact Or.inr ⟨hxa, htrans hby hyz⟩
    · exact Or.inr ⟨hxa, hbz⟩

/-- This explicit formula is the least transitive relation containing the old
order and the new comparison. -/
theorem adjoin_minimal {R S : α → α → Prop} {a b : α}
    (htrans : ∀ ⦃x y z⦄, S x y → S y z → S x z)
    (hcontains : ∀ x y, R x y → S x y)
    (hab : S a b) : ∀ x y, adjoin R a b x y → S x y := by
  intro x y h
  rcases h with hxy | ⟨hxa, hby⟩
  · exact hcontains x y hxy
  · exact htrans (hcontains x a hxa) (htrans hab (hcontains b y hby))

/-- A previously unknown forward comparison preserves antisymmetry. -/
theorem adjoin_antisymmetric {R : α → α → Prop}
    (htrans : ∀ ⦃x y z⦄, R x y → R y z → R x z)
    (hanti : ∀ x y, R x y → R y x → x = y)
    {a b : α} (hba : ¬ R b a) :
    ∀ x y, adjoin R a b x y → adjoin R a b y x → x = y := by
  intro x y hxy hyx
  rcases hxy with hxy | ⟨hxa, hby⟩
  · rcases hyx with hyx | ⟨hya, hbx⟩
    · exact hanti x y hxy hyx
    · exact (hba (htrans (htrans hbx hxy) hya)).elim
  · rcases hyx with hyx | ⟨hya, _⟩
    · exact (hba (htrans (htrans hby hyx) hxa)).elim
    · exact (hba (htrans hby hya)).elim

/-- A newly acquired relation has the single-new-edge path witnesses. -/
theorem new_relation_witness {R : α → α → Prop} {a b x y : α}
    (hnew : adjoin R a b x y) (hold : ¬ R x y) : R x a ∧ R b y := by
  exact hnew.resolve_left hold

section Colours

variable [LinearOrder β]

/-- Weak colour inequalities represent the public order. -/
def Respects (R : α → α → Prop) (f : α → β) : Prop :=
  ∀ x y, R x y → f x ≤ f y

/-- Physical pins are equalities at their immutable colours. -/
def ExtendsPins (pins : α → Option β) (f : α → β) : Prop :=
  ∀ x c, pins x = some c → f x = c

/-- A new path would compare two old pins at the same colour. -/
def InnerWitness (R : α → α → Prop) (pins : α → Option β) (a b : α) : Prop :=
  ∃ i j c, pins i = some c ∧ pins j = some c ∧
    R i a ∧ R b j ∧ ¬ R i j

/-- A new same-colour inner relation gives the reverse weak inequality in
every represented map, with the witnessing pinned colour between its ends. -/
theorem inner_witness_bounds {R : α → α → Prop} {pins : α → Option β}
    {a b : α} (hw : InnerWitness R pins a b) :
    ∃ c, ∀ f : α → β, Respects R f → ExtendsPins pins f →
      f b ≤ c ∧ c ≤ f a := by
  obtain ⟨i, j, c, hi, hj, hia, hbj, _⟩ := hw
  refine ⟨c, ?_⟩
  intro f hf hp
  constructor
  · simpa only [hp j c hj] using hf b j hbj
  · simpa only [hp i c hi] using hf i a hia

theorem inner_witness_reverse {R : α → α → Prop} {pins : α → Option β}
    {a b : α} (hw : InnerWitness R pins a b) {f : α → β}
    (hf : Respects R f) (hp : ExtendsPins pins f) : f b ≤ f a := by
  obtain ⟨c, hc⟩ := inner_witness_bounds hw
  exact le_trans (hc f hf hp).1 (hc f hf hp).2

/-- The weak models of an adjoining operation are exactly the old models
satisfying the weak answer. -/
theorem respects_adjoin_iff {R : α → α → Prop} (hrefl : ∀ x, R x x)
    {a b : α} {f : α → β} :
    Respects (adjoin R a b) f ↔ Respects R f ∧ f a ≤ f b := by
  constructor
  · intro h
    exact ⟨fun x y hxy => h x y (Or.inl hxy), h a b (adjoin_edge hrefl a b)⟩
  · rintro ⟨h, hab⟩ x y (hxy | ⟨hxa, hby⟩)
    · exact h x y hxy
    · exact le_trans (h x a hxa) (le_trans hab (h b y hby))

/-- A fibre that is constant across all represented maps is already a physical
pin. This is the precise local invariant used by the delegation argument. -/
def PinComplete (models : Set (α → β)) (pins : α → Option β) : Prop :=
  ∀ x c, (∀ f ∈ models, f x = c) → pins x = some c

/-- If both physical answers would change an old same-colour inner order,
the queried endpoints are actual pins in one and the same child. -/
theorem both_inner_witnesses_delegate {R : α → α → Prop}
    {models : Set (α → β)} {pins : α → Option β} {a b : α}
    (hmodels : ∀ f ∈ models, Respects R f ∧ ExtendsPins pins f)
    (hcomplete : PinComplete models pins)
    (hab : InnerWitness R pins a b) (hba : InnerWitness R pins b a) :
    ∃ c, pins a = some c ∧ pins b = some c := by
  obtain ⟨c, hc⟩ := inner_witness_bounds hab
  have heq : ∀ f ∈ models, f a = c ∧ f b = c := by
    intro f hfm
    obtain ⟨hf, hp⟩ := hmodels f hfm
    have hbounds := hc f hf hp
    have hreverse := inner_witness_reverse hba hf hp
    exact ⟨le_antisymm (le_trans hreverse hbounds.1) hbounds.2,
      le_antisymm hbounds.1 (le_trans hbounds.2 hreverse)⟩
  exact ⟨c, hcomplete a c (fun f hf => (heq f hf).1),
    hcomplete b c (fun f hf => (heq f hf).2)⟩

/-- An actually strict reverse witness rules out a reverse inner obstruction.
This is the compatibility argument used by the newly-singleton safety test. -/
theorem strict_witness_excludes_inner {R : α → α → Prop}
    {pins : α → Option β} {a b : α} {f : α → β}
    (hf : Respects R f) (hp : ExtendsPins pins f) (hstrict : f b < f a) :
    ¬ InnerWitness R pins b a := by
  intro hw
  exact (not_le_of_gt hstrict) (inner_witness_reverse hw hf hp)

/-- Restricting a set by a relation which all its maps satisfy changes nothing. -/
theorem all_retaining {models : Set (α → β)} {a b : α}
    (h : ∀ f ∈ models, f b ≤ f a) :
    {f ∈ models | f b ≤ f a} = models := by
  ext f
  exact ⟨fun hf => hf.1, fun hf => ⟨hf, h f hf⟩⟩

omit [LinearOrder β] in
/-- The non-singleton invariant implies completeness of physical pins. -/
theorem pin_complete_of_two_values {models : Set (α → β)}
    {pins : α → Option β}
    (hnonempty : models.Nonempty)
    (hpins : ∀ f ∈ models, ExtendsPins pins f)
    (hfree : ∀ x, pins x = none →
      ∃ f ∈ models, ∃ g ∈ models, f x ≠ g x) : PinComplete models pins := by
  intro x c hconstant
  cases hpx : pins x with
  | none =>
    obtain ⟨f, hf, g, hg, hne⟩ := hfree x hpx
    exact (hne ((hconstant f hf).trans (hconstant g hg).symm)).elim
  | some d =>
    obtain ⟨f, hf⟩ := hnonempty
    have hdc : d = c := (hpins f hf x d hpx).symm.trans (hconstant f hf)
    exact congrArg some hdc

/-- A pin strictly between two attainable values is publicly incomparable to
every old pin of that colour. This is the free-birth argument. -/
theorem interior_pin_incomparable {R : α → α → Prop}
    {pins : α → Option β} {v p : α} {c : β} {f g : α → β}
    (hf : Respects R f) (hg : Respects R g)
    (hfp : ExtendsPins pins f) (hgp : ExtendsPins pins g)
    (hp : pins p = some c) (hlo : f v < c) (hhi : c < g v) :
    ¬ R p v ∧ ¬ R v p := by
  constructor
  · intro hpv
    have h := hf p v hpv
    rw [hfp p c hp] at h
    exact (not_le_of_gt hlo) h
  · intro hvp
    have h := hg v p hvp
    rw [hgp p c hp] at h
    exact (not_le_of_gt hhi) h

end Colours

end SortingAdversary.Optimal.Routing
