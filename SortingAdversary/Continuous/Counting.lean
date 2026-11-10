import SortingAdversary.Basic
import SortingAdversary.Continuous.Weights
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Order.Fin.Basic
import Mathlib.Logic.Equiv.Fintype

/-!
# Transcript counts, free insertion, and partial-order production

The counting object is the set of all rankings compatible with the actual
comparison transcript, not just the orders represented by a stored tree.
Fresh, unqueried labels can be inserted at arbitrary ranks.  The finite
sampling reduction and the production reduction are stated against this
same semantic count.
-/

namespace SortingAdversary.Continuous

open scoped BigOperators

noncomputable def compatibleOrders {n : ℕ} (h : History n) : Finset (Ranking n) := by
  classical
  exact Finset.univ.filter (fun π => Compatible π h)

noncomputable def transcriptCount {n : ℕ} (h : History n) : ℕ := (compatibleOrders h).card

@[simp] theorem mem_compatibleOrders {n : ℕ} (h : History n) (π : Ranking n) :
    π ∈ compatibleOrders h ↔ Compatible π h := by
  classical
  simp [compatibleOrders]

theorem transcriptCount_eq_card {n : ℕ} (h : History n) :
    transcriptCount h = Nat.card {π : Ranking n // Compatible π h} := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp [transcriptCount, compatibleOrders, Fintype.card_subtype]

@[simp] theorem transcriptCount_nil (n : ℕ) : transcriptCount ([] : History n) = n.factorial := by
  classical
  simp [transcriptCount, compatibleOrders, Fintype.card_perm]

theorem transcriptCount_pos {n : ℕ} (h : History n) (π : Ranking n)
    (hπ : Compatible π h) : 0 < transcriptCount h := by
  apply Finset.card_pos.mpr
  exact ⟨π, (mem_compatibleOrders h π).mpr hπ⟩

/-- The set of labels that the transcript has actually queried. -/
def queriedLabels {n : ℕ} : History n → Finset (Item n)
  | [] => ∅
  | o :: h => insert o.query.left (insert o.query.right (queriedLabels h))

theorem queriedLabels_card_le {n : ℕ} (h : History n) :
    (queriedLabels h).card ≤ 2 * h.length := by
  induction h with
  | nil => simp [queriedLabels]
  | cons o h ih =>
    have h₁ := Finset.card_insert_le o.query.left (insert o.query.right (queriedLabels h))
    have h₂ := Finset.card_insert_le o.query.right (queriedLabels h)
    simp only [queriedLabels, List.length_cons]
    omega

/-- Both endpoints of every recorded comparison belong to the queried set. -/
theorem queriedLabels_members {n : ℕ} (h : History n) (o : Observation n) (ho : o ∈ h) :
    o.query.left ∈ queriedLabels h ∧ o.query.right ∈ queriedLabels h := by
  induction h with
  | nil => simp at ho
  | cons a h ih =>
    rcases List.mem_cons.mp ho with rfl | ho
    · simp [queriedLabels]
    · obtain ⟨hl, hr⟩ := ih ho
      simp [queriedLabels, hl, hr]

/-- Map a transcript along an injection of its labels. -/
def mapQuery {s n : ℕ} (e : Item s ↪ Item n) (q : Query s) : Query n where
  left := e q.left
  right := e q.right
  distinct := fun h => q.distinct (e.injective h)

def mapObservation {s n : ℕ} (e : Item s ↪ Item n) (o : Observation s) : Observation n :=
  ⟨mapQuery e o.query, o.answer⟩

def mapHistory {s n : ℕ} (e : Item s ↪ Item n) (h : History s) : History n :=
  h.map (mapObservation e)

theorem mapHistory_comp {s n m : ℕ} (e : Item s ↪ Item n) (f : Item n ↪ Item m)
    (h : History s) : mapHistory f (mapHistory e h) = mapHistory (e.trans f) h := by
  simp only [mapHistory, List.map_map]
  rfl

/-- Relabelling a transcript is a bijection on its compatible rankings. -/
theorem relabel_count {n : ℕ} (σ : Ranking n) (h : History n) :
    transcriptCount (mapHistory σ.toEmbedding h) = transcriptCount h := by
  classical
  have hcompat (π : Ranking n) :
      Compatible π (mapHistory σ.toEmbedding h) ↔ Compatible (σ.trans π) h := by
    induction h with
    | nil => simp [mapHistory]
    | cons o h ih =>
      have ho : (mapObservation σ.toEmbedding o).Holds π ↔ o.Holds (σ.trans π) := by
        cases o with
        | mk q a => cases a <;> rfl
      simpa only [mapHistory, List.map_cons, compatible_cons] using and_congr ho ih
  let E : {π : Ranking n // Compatible π (mapHistory σ.toEmbedding h)} ≃
      {π : Ranking n // Compatible π h} :=
    (show Ranking n ≃ Ranking n from
      { toFun := fun π => σ.trans π
        invFun := fun π => σ.symm.trans π
        left_inv := by intro π; ext x; simp
        right_inv := by intro π; ext x; simp }).subtypeEquiv hcompat
  rw [transcriptCount_eq_card, transcriptCount_eq_card]
  exact Nat.card_congr E

/-- Every transcript supported on an embedded label set is the image of a
transcript on that set. No comparisons with an unqueried label are introduced. -/
theorem exists_compressed_history {s n : ℕ} (e : Item s ↪ Item n) (h : History n)
    (hsupport : ∀ o ∈ h, o.query.left ∈ Set.range e ∧ o.query.right ∈ Set.range e) :
    ∃ h' : History s, mapHistory e h' = h := by
  induction h with
  | nil => exact ⟨[], rfl⟩
  | cons o h ih =>
    obtain ⟨h', hh'⟩ := ih (fun o' ho' => hsupport o' (by simp [ho']))
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hsupport o (by simp)
    have hxy : x ≠ y := by
      intro heq
      apply o.query.distinct
      rw [← hx, ← hy, heq]
    let o' : Observation s := ⟨⟨x, y, hxy⟩, o.answer⟩
    refine ⟨o' :: h', ?_⟩
    have ho : mapObservation e o' = o := by
      cases o with
      | mk q a => cases q; simp_all [mapObservation, mapQuery, o']
    simp only [mapHistory, List.map_cons] at hh' ⊢
    rw [ho, hh']

/-- Rename an old query to leave the new label `0` untouched. -/
def liftQuery {n : ℕ} (q : Query n) : Query (n + 1) where
  left := q.left.succ
  right := q.right.succ
  distinct := fun h => q.distinct (Fin.succ_injective n h)

def liftObservation {n : ℕ} (o : Observation n) : Observation (n + 1) :=
  ⟨liftQuery o.query, o.answer⟩

def liftHistory {n : ℕ} (h : History n) : History (n + 1) := h.map liftObservation

/-- Insert the new label `0` at any chosen rank. All old relative comparisons
are preserved by the increasing map `rank.succAbove`. -/
def insertRanking {n : ℕ} (rank : Fin (n + 1)) (π : Ranking n) : Ranking (n + 1) :=
  (finSuccEquiv n).trans ((Equiv.optionCongr π).trans (finSuccEquiv' rank).symm)

@[simp] theorem insertRanking_zero {n : ℕ} (rank : Fin (n + 1)) (π : Ranking n) :
    insertRanking rank π 0 = rank := by
  simp [insertRanking]

@[simp] theorem insertRanking_succ {n : ℕ} (rank : Fin (n + 1)) (π : Ranking n)
    (x : Fin n) : insertRanking rank π x.succ = rank.succAbove (π x) := by
  simp [insertRanking]

theorem insertRanking_injective {n : ℕ} :
    Function.Injective (fun p : Fin (n + 1) × Ranking n => insertRanking p.1 p.2) := by
  rintro ⟨r, π⟩ ⟨s, σ⟩ heq
  have hrs : r = s := by
    simpa using congrArg (fun e : Ranking (n + 1) => e 0) heq
  subst s
  have hπ : π = σ := by
    ext x
    have hx := congrArg (fun e : Ranking (n + 1) => e x.succ) heq
    exact congrArg Fin.val (by simpa using hx)
  simp [hπ]

@[simp] theorem liftObservation_holds {n : ℕ} (rank : Fin (n + 1)) (π : Ranking n)
    (o : Observation n) :
    (liftObservation o).Holds (insertRanking rank π) ↔ o.Holds π := by
  cases o with
  | mk q a => cases a <;> simp [liftObservation, liftQuery, Observation.Holds]

@[simp] theorem liftHistory_compatible {n : ℕ} (rank : Fin (n + 1)) (π : Ranking n)
    (h : History n) :
    Compatible (insertRanking rank π) (liftHistory h) ↔ Compatible π h := by
  induction h with
  | nil => simp [liftHistory]
  | cons o h ih =>
    simpa only [liftHistory, List.map_cons, compatible_cons] using
      (and_congr (liftObservation_holds rank π o) ih)

/-- An unqueried label contributes all `n+1` insertion positions. This is a
semantic count of compatible rankings, so positions inside old child blocks
are included as required in the revised paper. -/
theorem fresh_insertion_count {n : ℕ} (h : History n) :
    (n + 1) * transcriptCount h ≤ transcriptCount (liftHistory h) := by
  classical
  let f : Fin (n + 1) × {π : Ranking n // Compatible π h} →
      {π : Ranking (n + 1) // Compatible π (liftHistory h)} := fun p =>
    ⟨insertRanking p.1 p.2.1, (liftHistory_compatible p.1 p.2.1 h).mpr p.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨r, π⟩ ⟨s, σ⟩ heq
    have hv : insertRanking r π.val = insertRanking s σ.val := by
      simpa [f] using congrArg Subtype.val heq
    have hp := insertRanking_injective (n := n) (a₁ := (r, π.val)) (a₂ := (s, σ.val)) hv
    have hrs : r = s := congrArg Prod.fst hp
    have hπ : π = σ := Subtype.ext (congrArg Prod.snd hp)
    simp [hrs, hπ]
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  simpa [transcriptCount_eq_card, Nat.card_eq_fintype_card] using hc

/-- Repeatedly add fresh, unqueried labels. -/
def extendHistory {s : ℕ} (h : History s) : (r : ℕ) → History (s + r)
  | 0 => h
  | r + 1 => liftHistory (extendHistory h r)

/-- The exact free-insertion factor, without division of natural numbers. -/
theorem free_insertion_count {s : ℕ} (h : History s) (r : ℕ) :
    (s + r).factorial * transcriptCount h ≤
      s.factorial * transcriptCount (extendHistory h r) := by
  induction r with
  | zero => simp [extendHistory]
  | succ r ih =>
    have hf := fresh_insertion_count (extendHistory h r)
    calc
      (s + (r + 1)).factorial * transcriptCount h =
          (s + r + 1) * ((s + r).factorial * transcriptCount h) := by
        rw [show s + (r + 1) = (s + r) + 1 by omega, Nat.factorial_succ]
        ring
      _ ≤ (s + r + 1) * (s.factorial * transcriptCount (extendHistory h r)) :=
        Nat.mul_le_mul_left _ ih
      _ = s.factorial * ((s + r + 1) * transcriptCount (extendHistory h r)) := by ring
      _ ≤ s.factorial * transcriptCount (extendHistory h (r + 1)) :=
        Nat.mul_le_mul_left _ hf

theorem extendHistory_eq_map {s : ℕ} (h : History s) (r : ℕ) :
    extendHistory h r = mapHistory (Fin.addNatEmb r) h := by
  induction r with
  | zero =>
    simp only [extendHistory, mapHistory]
    apply (List.map_id h).symm.trans
    apply List.map_congr_left
    intro o ho
    cases o with
    | mk q a => cases q; rfl
  | succ r ih =>
    rw [extendHistory, ih]
    simp only [liftHistory, mapHistory, List.map_map]
    apply List.map_congr_left
    intro o ho
    cases o with
    | mk q a => cases q; rfl

/-- Free insertion is independent of the names of the queried labels. -/
theorem embedded_history_count {s : ℕ} (h : History s) (r : ℕ)
    (e : Item s ↪ Item (s + r)) :
    (s + r).factorial * transcriptCount h ≤ s.factorial * transcriptCount (mapHistory e h) := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (Fin.addNatEmb r) e (Fin.addNatEmb r).injective e.injective
  have hmaps : (Fin.addNatEmb r).trans σ.toEmbedding = e := by
    ext x
    exact congrArg Fin.val (hσ x)
  have heq : transcriptCount (extendHistory h r) = transcriptCount (mapHistory e h) := by
    rw [extendHistory_eq_map]
    rw [← relabel_count σ, mapHistory_comp, hmaps]
  simpa [heq] using free_insertion_count h r

/-- The unrestricted-insertion inequality with an arbitrary ambient size. -/
theorem embedded_history_count_general {s n : ℕ} (h : History s) (e : Item s ↪ Item n) :
    n.factorial * transcriptCount h ≤ s.factorial * transcriptCount (mapHistory e h) := by
  have hsn : s ≤ n := by
    simpa using Fintype.card_le_of_injective e e.injective
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hsn
  exact embedded_history_count h r e

/-- Relabel slots by a fixed key assignment. This equivalence makes precise
the statement that every fixed production output admits exactly `e(R)` orders. -/
def assignmentEquiv {n : ℕ} (assignment : Ranking n) : Ranking n ≃ Ranking n where
  toFun π := assignment.trans π
  invFun π := assignment.symm.trans π
  left_inv π := by ext x; simp
  right_inv π := by ext x; simp

def Respects {n : ℕ} (R : Item n → Item n → Prop) (π : Ranking n) : Prop :=
  ∀ u v, R u v → π u < π v

noncomputable def extensionOrders {n : ℕ} (R : Item n → Item n → Prop) :
    Finset (Ranking n) := by
  classical
  exact Finset.univ.filter (Respects R)

noncomputable def extensionCount {n : ℕ} (R : Item n → Item n → Prop) : ℕ :=
  (extensionOrders R).card

def Produces {n : ℕ} (R : Item n → Item n → Prop) (assignment π : Ranking n) : Prop :=
  Respects R (assignmentEquiv assignment π)

theorem production_count_le {n : ℕ} (h : History n)
    (R : Item n → Item n → Prop) (assignment : Ranking n)
    (hcorrect : ∀ π, Compatible π h → Produces R assignment π) :
    transcriptCount h ≤ extensionCount R := by
  classical
  apply Finset.card_le_card_of_injOn (assignmentEquiv assignment)
  · intro π hπ
    simp only [extensionOrders, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hcorrect π ((mem_compatibleOrders h π).mp hπ)
  · exact (assignmentEquiv assignment).injective.injOn

/-- A finite probability distribution on rankings, invariant under relabelling,
assigns the same mass to every order. The symmetry and normalization are
explicit hypotheses; the continuous tree sampling law must establish them. -/
theorem symmetric_rank_mass {n : ℕ} (mass : Ranking n → ℝ)
    (hnormalized : ∑ π, mass π = 1)
    (hsymmetry : ∀ σ π : Ranking n, mass (σ.trans π) = mass π)
    (π : Ranking n) : mass π = 1 / (n.factorial : ℝ) := by
  have hconst : ∀ ρ : Ranking n, mass ρ = mass π := by
    intro ρ
    have hs := hsymmetry (ρ.trans π.symm) π
    have heq : (ρ.trans π.symm).trans π = ρ := by ext x; simp
    rw [heq] at hs
    exact hs
  have hsum : (n.factorial : ℝ) * mass π = 1 := by
    simpa [hconst, Fintype.card_perm] using hnormalized
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hn).mpr
  simpa [mul_comm] using hsum

/-- The finite symmetry-to-counting step in the sampling argument. -/
theorem transcript_count_of_symmetric_sample {n : ℕ} (h : History n)
    (mass : Ranking n → ℝ) (p : ℝ)
    (hnormalized : ∑ π, mass π = 1)
    (hsymmetry : ∀ σ π : Ranking n, mass (σ.trans π) = mass π)
    (hcompatible : p ≤ ∑ π ∈ compatibleOrders h, mass π) :
    (n.factorial : ℝ) * p ≤ transcriptCount h := by
  have huniform := symmetric_rank_mass mass hnormalized hsymmetry
  simp_rw [huniform] at hcompatible
  simp only [Finset.sum_const, nsmul_eq_mul] at hcompatible
  have hn : (0 : ℝ) < n.factorial := by positivity
  have hm := mul_le_mul_of_nonneg_left hcompatible hn.le
  have heq : (n.factorial : ℝ) * ((compatibleOrders h).card * (1 / n.factorial)) =
      (compatibleOrders h).card := by
    field_simp
  rw [heq] at hm
  exact hm

/-- Applying a prefix estimate to a successful partial-order production
output. This statement is uniform in the target relation `R`. -/
theorem production_bound_of_prefix {n : ℕ} (h : History n)
    (R : Item n → Item n → Prop) (assignment : Ranking n) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hlegal : ∃ π, Compatible π h)
    (hcorrect : ∀ π, Compatible π h → Produces R assignment π)
    (hprefix : log2 (n.factorial : ℝ) - (1 + δ) * h.length ≤
      log2 (transcriptCount h : ℝ)) :
    (log2 (n.factorial : ℝ) - log2 (extensionCount R : ℝ)) / (1 + δ) ≤ h.length := by
  obtain ⟨π, hπ⟩ := hlegal
  have hpos : (0 : ℝ) < transcriptCount h := by
    exact_mod_cast transcriptCount_pos h π hπ
  have hcount : (transcriptCount h : ℝ) ≤ extensionCount R := by
    exact_mod_cast production_count_le h R assignment hcorrect
  have hlog := log2_mono hpos hcount
  apply (div_le_iff₀ (show 0 < 1 + δ by linarith)).mpr
  nlinarith

end SortingAdversary.Continuous
