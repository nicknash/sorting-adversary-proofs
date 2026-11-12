import SortingAdversary.Continuous.ControllerAsymptotics
import Mathlib.Data.Sigma.Order

/-!
# Independent continuous adversaries in ordered antichain layers

An ordered partition is represented by an actual bijection of labels with
the disjoint union of its layers. Interactions below use the actual local
controller in each layer and the fixed layer order between layers. We prove
legality by concatenating local rankings, and derive local uniqueness from
global sorting correctness before summing the prefix bounds.

The final theorem takes the entropy retention of the ordered partition as
an explicit input. The polynomial-time Cardinal weak-order extension theorem
used to obtain that partition is an external dependency of the manuscript;
it is not introduced here as an axiom or bundled with the desired comparison
lower bound.
-/

namespace SortingAdversary.Continuous.LayerReduction

open scoped BigOperators

variable {n t : ℕ}

structure Layering (n t : ℕ) where
  size : Fin t → ℕ
  index : Fin n ≃ Σ i : Fin t, Fin (size i)

namespace Layering

def vertex (L : Layering n t) (i : Fin t) (x : Fin (L.size i)) : Fin n := L.index.symm ⟨i, x⟩

def embedding (L : Layering n t) (i : Fin t) : Fin (L.size i) ↪ Fin n where
  toFun := L.vertex i
  inj' := by
    intro x y hxy
    have hh := L.index.symm.injective hxy
    exact Sigma.mk.inj_iff.mp hh |>.2 |> eq_of_heq

@[simp] theorem index_vertex (L : Layering n t) (i : Fin t) (x : Fin (L.size i)) :
    L.index (L.vertex i x) = ⟨i, x⟩ := L.index.apply_symm_apply _

theorem size_sum (L : Layering n t) : ∑ i, L.size i = n := by
  have h := Fintype.card_congr L.index
  simpa only [Fintype.card_fin, Fintype.card_sigma] using h.symm

theorem size_le (L : Layering n t) (i : Fin t) : L.size i ≤ n := by
  exact (Finset.single_le_sum (s := Finset.univ) (f := L.size)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)).trans_eq L.size_sum

def position (L : Layering n t) (ρ : ∀ i, Ranking (L.size i)) (x : Fin n) :
    Lex (Σ i : Fin t, Fin (L.size i)) :=
  ⟨(L.index x).1, ρ (L.index x).1 (L.index x).2⟩

theorem position_injective (L : Layering n t) (ρ : ∀ i, Ranking (L.size i)) :
    Function.Injective (L.position ρ) := by
  intro x y hxy
  apply L.index.injective
  apply (Equiv.sigmaCongrRight ρ).injective
  exact hxy

theorem position_vertex (L : Layering n t) (ρ : ∀ i, Ranking (L.size i))
    (i : Fin t) (x : Fin (L.size i)) :
    L.position ρ (L.vertex i x) = (⟨i, ρ i x⟩ : Lex (Σ j : Fin t, Fin (L.size j))) := by
  change (Equiv.sigmaCongrRight ρ) (L.index (L.vertex i x)) = _
  rw [L.index_vertex]
  rfl

noncomputable def ranking (L : Layering n t) (ρ : ∀ i, Ranking (L.size i)) : Ranking n :=
  Classical.choose (exists_orderCell (L.position ρ) (L.position_injective ρ))

theorem ranking_order (L : Layering n t) (ρ : ∀ i, Ranking (L.size i)) (x y : Fin n) :
    L.ranking ρ x < L.ranking ρ y ↔ L.position ρ x < L.position ρ y :=
  Classical.choose_spec (exists_orderCell (L.position ρ) (L.position_injective ρ)) x y

theorem ranking_same (L : Layering n t) (ρ : ∀ i, Ranking (L.size i)) (i : Fin t)
    (x y : Fin (L.size i)) :
    L.ranking ρ (L.vertex i x) < L.ranking ρ (L.vertex i y) ↔ ρ i x < ρ i y := by
  rw [L.ranking_order, L.position_vertex, L.position_vertex]
  change Sigma.Lex (fun a b : Fin t => a < b)
    (fun j (a b : Fin (L.size j)) => a < b) ⟨i, ρ i x⟩ ⟨i, ρ i y⟩ ↔ _
  constructor
  · intro h
    cases h with
    | left a b hlt => exact (lt_irrefl i hlt).elim
    | right a b hlt => exact hlt
  · intro h
    exact Sigma.Lex.right _ _ h

theorem ranking_before (L : Layering n t) (ρ : ∀ i, Ranking (L.size i))
    {i j : Fin t} (hij : i < j) (x : Fin (L.size i)) (y : Fin (L.size j)) :
    L.ranking ρ (L.vertex i x) < L.ranking ρ (L.vertex j y) := by
  rw [L.ranking_order, L.position_vertex, L.position_vertex]
  exact Sigma.Lex.left _ _ hij

theorem ranking_injective (L : Layering n t) : Function.Injective L.ranking := by
  intro ρ σ heq
  funext i
  apply orderCell_unique (π := ρ i) (σ := σ i) (x := fun x => ρ i x)
  · intro x y
    rfl
  · intro x y
    rw [← L.ranking_same σ i x y, ← heq, L.ranking_same ρ i x y]

theorem within_holds (L : Layering n t) (ρ : ∀ i, Ranking (L.size i))
    (i : Fin t) (o : Observation (L.size i)) :
    (mapObservation (L.embedding i) o).Holds (L.ranking ρ) ↔ o.Holds (ρ i) := by
  cases o with
  | mk q a =>
    cases a <;> exact L.ranking_same ρ i _ _

def crossingQuery (L : Layering n t) {i j : Fin t} (hne : i ≠ j)
    (x : Fin (L.size i)) (y : Fin (L.size j)) : Query n where
  left := L.vertex i x
  right := L.vertex j y
  distinct := by
    intro h
    have he := congrArg (fun v => (L.index v).1) h
    exact hne (by simpa only [index_vertex] using he)

def crossingObservation (L : Layering n t) {i j : Fin t} (hne : i ≠ j)
    (x : Fin (L.size i)) (y : Fin (L.size j)) : Observation n :=
  ⟨L.crossingQuery hne x y, if i < j then .less else .greater⟩

theorem crossing_holds (L : Layering n t) (ρ : ∀ i, Ranking (L.size i))
    {i j : Fin t} (hne : i ≠ j) (x : Fin (L.size i)) (y : Fin (L.size j)) :
    (L.crossingObservation hne x y).Holds (L.ranking ρ) := by
  by_cases hij : i < j
  · simpa only [crossingObservation, if_pos hij, Observation.Holds, crossingQuery] using
      L.ranking_before ρ hij x y
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) hne.symm
    simpa only [crossingObservation, if_neg hij, Observation.Holds, crossingQuery] using
      L.ranking_before ρ hji y x

/-- Every initial strict relation points forward between layers. -/
def Extends (L : Layering n t) (P : Item n → Item n → Prop) : Prop :=
  ∀ x y, P x y → (L.index x).1 < (L.index y).1

theorem ranking_respects (L : Layering n t) (P : Item n → Item n → Prop)
    (hP : L.Extends P) (ρ : ∀ i, Ranking (L.size i)) : Respects P (L.ranking ρ) := by
  intro x y hxy
  rw [L.ranking_order]
  exact Sigma.Lex.left _ _ (hP x y hxy)

theorem horizon_sum_le (L : Layering n t) :
    (∑ i, Controller.horizon (L.size i)) ≤ Controller.horizon n := by
  calc
    _ ≤ ∑ i, L.size i * Nat.clog 2 n := Finset.sum_le_sum (fun i _ =>
      Nat.mul_le_mul_left _ (Nat.clog_mono_right 2 (L.size_le i)))
    _ = Controller.horizon n := by rw [← Finset.sum_mul, L.size_sum]; rfl

private theorem query_ext {q r : Query n} (hl : q.left = r.left) (hr : q.right = r.right) :
    q = r := by
  cases q
  cases r
  cases hl
  cases hr
  rfl

theorem query_cases (L : Layering n t) (q : Query n) :
    (∃ (i : Fin t) (p : Query (L.size i)), mapQuery (L.embedding i) p = q) ∨
    (∃ (i j : Fin t) (hne : i ≠ j) (x : Fin (L.size i)) (y : Fin (L.size j)),
      L.crossingQuery hne x y = q) := by
  cases hl : L.index q.left with
  | mk i x =>
    cases hr : L.index q.right with
    | mk j y =>
      have hleft : L.vertex i x = q.left := by
        change L.index.symm ⟨i, x⟩ = q.left
        rw [← hl, L.index.symm_apply_apply]
      have hright : L.vertex j y = q.right := by
        change L.index.symm ⟨j, y⟩ = q.right
        rw [← hr, L.index.symm_apply_apply]
      by_cases hij : i = j
      · subst j
        have hxy : x ≠ y := by
          intro he
          apply q.distinct
          rw [← hleft, ← hright, he]
        exact Or.inl ⟨i, ⟨x, y, hxy⟩, query_ext hleft hright⟩
      · exact Or.inr ⟨i, j, hij, x, y, query_ext hleft hright⟩

/-- Routing after the two concrete layer positions have been read. -/
def advancePositions (L : Layering n t) (k : ℕ) (locals : ∀ i, History (L.size i))
    (left right : Σ i : Fin t, Fin (L.size i)) (hne : left ≠ right) :
    (∀ i, History (L.size i)) × Answer := by
  cases left with
  | mk i x =>
    cases right with
    | mk j y =>
      by_cases hij : i = j
      · let y' : Fin (L.size i) := Fin.cast (congrArg L.size hij.symm) y
        have hxy : x ≠ y' := by
          intro he
          subst j
          have he' : x = y := by simpa only [y', Fin.cast_eq_self] using he
          exact hne (by rw [he'])
        let p : Query (L.size i) := ⟨x, y', hxy⟩
        let a := Controller.strategy k (locals i) p
        exact (Function.update locals i (⟨p, a⟩ :: locals i), a)
      · exact (locals, if i < j then .less else .greater)

/-- Executable routing of a global query to its unique layer, or to the
fixed order between two layers. All stored histories are local histories. -/
def advance (L : Layering n t) (k : ℕ) (locals : ∀ i, History (L.size i)) (q : Query n) :
    (∀ i, History (L.size i)) × Answer :=
  L.advancePositions k locals (L.index q.left) (L.index q.right)
    (fun h => q.distinct (L.index.injective h))

theorem advance_within (L : Layering n t) (k : ℕ) (locals : ∀ i, History (L.size i))
    (i : Fin t) (q : Query (L.size i)) :
    L.advance k locals (mapQuery (L.embedding i) q) =
      (Function.update locals i (⟨q, Controller.strategy k (locals i) q⟩ :: locals i),
        Controller.strategy k (locals i) q) := by
  have hl : L.index (mapQuery (L.embedding i) q).left = ⟨i, q.left⟩ := L.index_vertex i q.left
  have hr : L.index (mapQuery (L.embedding i) q).right = ⟨i, q.right⟩ := L.index_vertex i q.right
  unfold advance
  simp only [hl, hr]
  simp [advancePositions]

theorem advance_crossing (L : Layering n t) (k : ℕ) (locals : ∀ i, History (L.size i))
    {i j : Fin t} (hne : i ≠ j) (x : Fin (L.size i)) (y : Fin (L.size j)) :
    L.advance k locals (L.crossingQuery hne x y) =
      (locals, if i < j then .less else .greater) := by
  simp [advance, crossingQuery, vertex, advancePositions, hne]

def replay (L : Layering n t) (k : ℕ) (past : History n) : ∀ i, History (L.size i) :=
  past.reverse.foldl (fun locals o => (L.advance k locals o.query).1) (fun _ => [])

def strategy (L : Layering n t) (k : ℕ) : Strategy n :=
  fun past q => (L.advance k (L.replay k past) q).2

@[simp] theorem replay_cons (L : Layering n t) (k : ℕ) (o : Observation n) (past : History n) :
    L.replay k (o :: past) = (L.advance k (L.replay k past) o.query).1 := by
  simp [replay, List.foldl_append]

end Layering

/-- An arbitrary interleaving of local comparisons and fixed inter-layer
comparisons. Each local answer is the actual continuous controller's answer. -/
inductive Play (L : Layering n t) (k : ℕ) :
    (∀ i, History (L.size i)) → History n → Prop
  | nil : Play L k (fun _ => []) []
  | within {locals : ∀ i, History (L.size i)} {global : History n}
      (past : Play L k locals global) (i : Fin t) (q : Query (L.size i)) :
      Play L k
        (Function.update locals i (⟨q, Controller.strategy k (locals i) q⟩ :: locals i))
        (mapObservation (L.embedding i) ⟨q, Controller.strategy k (locals i) q⟩ :: global)
  | between {locals : ∀ i, History (L.size i)} {global : History n}
      (past : Play L k locals global) {i j : Fin t} (hne : i ≠ j)
      (x : Fin (L.size i)) (y : Fin (L.size j)) :
      Play L k locals (L.crossingObservation hne x y :: global)

namespace Play

variable {L : Layering n t} {k : ℕ} {locals : ∀ i, History (L.size i)} {global : History n}

theorem advance (h : Play L k locals global) (q : Query n) :
    Play L k (L.advance k locals q).1 (⟨q, (L.advance k locals q).2⟩ :: global) := by
  rcases L.query_cases q with ⟨i, p, rfl⟩ | ⟨i, j, hne, x, y, rfl⟩
  · rw [L.advance_within]
    exact Play.within h i p
  · rw [L.advance_crossing]
    exact Play.between h hne x y

theorem of_follows (h : History n) (hf : Follows (L.strategy k) h) :
    Play L k (L.replay k h) h := by
  induction hf with
  | nil => exact Play.nil
  | @cons h q hf ih => simpa only [Layering.replay_cons, Layering.strategy] using ih.advance q

theorem local_follows (h : Play L k locals global) :
    ∀ i, Follows (Controller.strategy k) (locals i) := by
  induction h with
  | nil => exact fun _ => Follows.nil
  | @within locals global past i q ih =>
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [Function.update_self] using Follows.cons q (ih i)
    · simpa only [Function.update_of_ne hj] using ih j
  | between past hne x y ih => exact ih

theorem comparison_count (h : Play L k locals global) :
    (∑ i, (locals i).length) ≤ global.length := by
  induction h with
  | nil => simp
  | @within locals global past i q ih =>
    have heq : (∑ j, (Function.update locals i
        (⟨q, Controller.strategy k (locals i) q⟩ :: locals i) j).length) =
        (∑ j, (locals j).length) + 1 := by
      calc
        _ = ∑ j, ((locals j).length + if j = i then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hji : j = i
          · subst j
            simp
          · simp [Function.update_of_ne hji, hji]
        _ = _ := by simp [Finset.sum_add_distrib]
    simp only [List.length_cons]
    rw [heq]
    omega
  | between past hne x y ih => simpa only [List.length_cons] using ih.trans (Nat.le_succ _)

theorem compatible (h : Play L k locals global) (ρ : ∀ i, Ranking (L.size i))
    (hρ : ∀ i, Compatible (ρ i) (locals i)) : Compatible (L.ranking ρ) global := by
  induction h generalizing ρ with
  | nil => exact compatible_nil _
  | @within locals global past i q ih =>
    have hi : (Observation.mk q (Controller.strategy k (locals i) q)).Holds (ρ i) ∧
        Compatible (ρ i) (locals i) :=
      (compatible_cons _ _ _).mp (by simpa only [Function.update_self] using hρ i)
    rw [compatible_cons]
    refine ⟨(L.within_holds ρ i _).mpr hi.1, ih ρ ?_⟩
    intro j
    by_cases hji : j = i
    · subst j
      exact hi.2
    · simpa only [Function.update_of_ne hji] using hρ j
  | between past hne x y ih =>
    exact (compatible_cons _ _ _).mpr ⟨L.crossing_holds ρ hne x y, ih ρ hρ⟩

theorem legal (h : Play L k locals global) (hk : 64 ≤ k)
    (hcompare : ∀ m, Controller.CompareGuarantee m k)
    (P : Item n → Item n → Prop) (hP : L.Extends P) :
    ∃ π : Ranking n, Compatible π global ∧ Respects P π := by
  have hlocal : ∀ i, ∃ π : Ranking (L.size i), Compatible π (locals i) := fun i =>
    (Controller.follows_prefixSound hk (hcompare (L.size i)) _ (h.local_follows i)).1.compatible
  choose ρ hρ using hlocal
  exact ⟨L.ranking ρ, h.compatible ρ hρ, L.ranking_respects P hP ρ⟩

/-- Global uniqueness forces uniqueness in each layer: replacing one local
ranking gives another genuine global ranking unless that layer is unique. -/
theorem local_unique (h : Play L k locals global) (hk : 64 ≤ k)
    (hcompare : ∀ m, Controller.CompareGuarantee m k)
    (P : Item n → Item n → Prop) (hP : L.Extends P) (output : Ranking n)
    (hunique : ∀ π, Compatible π global → Respects P π → π = output)
    (i : Fin t) (π σ : Ranking (L.size i))
    (hπ : Compatible π (locals i)) (hσ : Compatible σ (locals i)) : π = σ := by
  classical
  have hlocal : ∀ j, ∃ ρ : Ranking (L.size j), Compatible ρ (locals j) := fun j =>
    (Controller.follows_prefixSound hk (hcompare (L.size j)) _ (h.local_follows j)).1.compatible
  choose ρ hρ using hlocal
  have hupdate (τ : Ranking (L.size i)) (hτ : Compatible τ (locals i)) :
      ∀ j, Compatible (Function.update ρ i τ j) (locals j) := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [Function.update_self] using hτ
    · simpa only [Function.update_of_ne hj] using hρ j
  have heq : L.ranking (Function.update ρ i π) = L.ranking (Function.update ρ i σ) :=
    (hunique _ (h.compatible _ (hupdate π hπ)) (L.ranking_respects P hP _)).trans
      (hunique _ (h.compatible _ (hupdate σ hσ)) (L.ranking_respects P hP _)).symm
  have hf := L.ranking_injective heq
  simpa only [Function.update_self] using congrArg (fun f => f i) hf

theorem local_count_one (h : Play L k locals global) (hk : 64 ≤ k)
    (hcompare : ∀ m, Controller.CompareGuarantee m k)
    (P : Item n → Item n → Prop) (hP : L.Extends P) (output : Ranking n)
    (hunique : ∀ π, Compatible π global → Respects P π → π = output)
    (i : Fin t) : transcriptCount (locals i) = 1 := by
  have hle : transcriptCount (locals i) ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro π hπ σ hσ
    exact h.local_unique hk hcompare P hP output hunique i π σ
      ((mem_compatibleOrders _ _).mp hπ) ((mem_compatibleOrders _ _).mp hσ)
  obtain ⟨π, hπ⟩ :=
    (Controller.follows_prefixSound hk (hcompare (L.size i)) _ (h.local_follows i)).1.compatible
  have hpos := transcriptCount_pos (locals i) π hπ
  omega

/-- All layer copies use the same parameter `k`, including small layers. -/
theorem comparison_lower (h : Play L k locals global) (hk : 64 ≤ k)
    (hcompare : ∀ m, Controller.CompareGuarantee m k)
    (P : Item n → Item n → Prop) (hP : L.Extends P) (output : Ranking n)
    (hunique : ∀ π, Compatible π global → Respects P π → π = output) :
    (∑ i, log2 ((L.size i).factorial : ℝ)) / (1 + prefixOverhead k) ≤ global.length := by
  have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : 0 < 1 + prefixOverhead k := by linarith [prefixOverhead_nonneg hkR]
  have hb (i : Fin t) : log2 ((L.size i).factorial : ℝ) ≤
      (1 + prefixOverhead k) * (locals i).length := by
    have hp := Controller.prefix_of_compare_guarantee hk (hcompare (L.size i))
      (locals i) (h.local_follows i)
    rw [h.local_count_one hk hcompare P hP output hunique i] at hp
    simp only [Nat.cast_one, log2_one] at hp
    linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hb i)
  rw [← Finset.mul_sum] at hs
  have hc : (∑ i, ((locals i).length : ℝ)) ≤ global.length := by
    exact_mod_cast h.comparison_count
  apply (div_le_iff₀ hden).mpr
  have hh := hs.trans (mul_le_mul_of_nonneg_left hc hden.le)
  simpa only [mul_comm] using hh

/-- The only external ingredient is the entropy retained by the supplied
ordered partition. In the manuscript this premise is obtained from Cardinal
et al.'s weak-order extension algorithm with `loss = C₀ n log log n`. -/
theorem supplied_information_bound (h : Play L k locals global) (hk : 64 ≤ k)
    (hcompare : ∀ m, Controller.CompareGuarantee m k)
    (P : Item n → Item n → Prop) (hP : L.Extends P) (output : Ranking n)
    (hunique : ∀ π, Compatible π global → Respects P π → π = output)
    (loss : ℝ) (hretained : log2 (extensionCount P : ℝ) - loss ≤
      ∑ i, log2 ((L.size i).factorial : ℝ)) :
    (log2 (extensionCount P : ℝ) - loss) / (1 + prefixOverhead k) ≤ global.length := by
  have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
  exact (div_le_div_of_nonneg_right hretained (by linarith [prefixOverhead_nonneg hkR])).trans
    (h.comparison_lower hk hcompare P hP output hunique)

/-- The paper's multiplicative error and additive entropy loss are uniform
in the supplied partial order. -/
theorem supplied_information_error (h : Play L k locals global) (hk : 64 ≤ k)
    (hcompare : ∀ m, Controller.CompareGuarantee m k)
    (P : Item n → Item n → Prop) (hP : L.Extends P) (output : Ranking n)
    (hunique : ∀ π, Compatible π global → Respects P π → π = output)
    (loss : ℝ) (hloss : 0 ≤ loss) (hretained : log2 (extensionCount P : ℝ) - loss ≤
      ∑ i, log2 ((L.size i).factorial : ℝ)) :
    (1 - Controller.productionError k) * log2 (extensionCount P : ℝ) - loss ≤ global.length := by
  have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
  have hδ := prefixOverhead_nonneg hkR
  have hden : 0 < 1 + prefixOverhead k := by linarith
  have hb := (div_le_iff₀ hden).mp
    (h.supplied_information_bound hk hcompare P hP output hunique loss hretained)
  have heq : (1 + prefixOverhead k) * (1 - Controller.productionError k) = 1 := by
    unfold Controller.productionError
    field_simp [ne_of_gt hden]
    ring
  apply (mul_le_mul_iff_right₀ hden).mp
  nlinarith [mul_nonneg hδ hloss, congrArg (fun z : ℝ => z * log2 (extensionCount P : ℝ)) heq]

end Play

/-- Sorting correctness restricted to the supplied strict relations. -/
def CorrectFor (tree : DecisionTree n) (P : Item n → Item n → Prop) : Prop :=
  ∀ π : Ranking n, Respects P π → tree.evaluate π = π

theorem run_legal (L : Layering n t) (k : ℕ) (hk : 64 ≤ k)
    (hcompare : ∀ m, Controller.CompareGuarantee m k)
    (P : Item n → Item n → Prop) (hP : L.Extends P) (tree : DecisionTree n) :
    ∃ π : Ranking n, Compatible π (tree.run (L.strategy k) []).observations ∧ Respects P π := by
  have hf := run_follows (L.strategy k) tree [] Follows.nil
  simp only [List.append_nil] at hf
  obtain ⟨π, hπ, hp⟩ := (Play.of_follows _ hf).legal hk hcompare P hP
  exact ⟨π, (compatible_reverse π _).mp hπ, hp⟩

/-- The supplied-information bound for the executable layered strategy and
the repository's actual decision-tree execution. -/
theorem run_comparison_bound (L : Layering n t) (k : ℕ) (hk : 64 ≤ k)
    (hcompare : ∀ m, Controller.CompareGuarantee m k)
    (P : Item n → Item n → Prop) (hP : L.Extends P)
    (tree : DecisionTree n) (hcorrect : CorrectFor tree P)
    (loss : ℝ) (hretained : log2 (extensionCount P : ℝ) - loss ≤
      ∑ i, log2 ((L.size i).factorial : ℝ)) :
    (log2 (extensionCount P : ℝ) - loss) / (1 + prefixOverhead k) ≤
      (tree.run (L.strategy k) []).comparisons := by
  have hf := run_follows (L.strategy k) tree [] Follows.nil
  simp only [List.append_nil] at hf
  have hplay := Play.of_follows _ hf
  have hu : ∀ π, Compatible π (tree.run (L.strategy k) []).observations.reverse →
      Respects P π → π = (tree.run (L.strategy k) []).output := by
    intro π hπ hp
    have hm := tree.run_matches_compatible_ranking (L.strategy k) [] π
      ((compatible_reverse π _).mp hπ)
    exact (hcorrect π hp).symm.trans hm.1
  have hb := hplay.supplied_information_bound hk hcompare P hP _ hu loss hretained
  simpa only [List.length_reverse, tree.run_observations_length] using hb

theorem run_comparison_error (L : Layering n t) (k : ℕ) (hk : 64 ≤ k)
    (hcompare : ∀ m, Controller.CompareGuarantee m k)
    (P : Item n → Item n → Prop) (hP : L.Extends P)
    (tree : DecisionTree n) (hcorrect : CorrectFor tree P)
    (loss : ℝ) (hloss : 0 ≤ loss) (hretained : log2 (extensionCount P : ℝ) - loss ≤
      ∑ i, log2 ((L.size i).factorial : ℝ)) :
    (1 - Controller.productionError k) * log2 (extensionCount P : ℝ) - loss ≤
      (tree.run (L.strategy k) []).comparisons := by
  have hf := run_follows (L.strategy k) tree [] Follows.nil
  simp only [List.append_nil] at hf
  have hplay := Play.of_follows _ hf
  have hu : ∀ π, Compatible π (tree.run (L.strategy k) []).observations.reverse →
      Respects P π → π = (tree.run (L.strategy k) []).output := by
    intro π hπ hp
    have hm := tree.run_matches_compatible_ranking (L.strategy k) [] π
      ((compatible_reverse π _).mp hπ)
    exact (hcorrect π hp).symm.trans hm.1
  have hb := hplay.supplied_information_error hk hcompare P hP _ hu loss hloss hretained
  simpa only [List.length_reverse, tree.run_observations_length] using hb

/-- The layered interaction yields a genuine input satisfying the supplied
partial order with the same comparison lower bound. -/
theorem worst_case (L : Layering n t) (k : ℕ) (hk : 64 ≤ k)
    (hcompare : ∀ m, Controller.CompareGuarantee m k)
    (P : Item n → Item n → Prop) (hP : L.Extends P)
    (tree : DecisionTree n) (hcorrect : CorrectFor tree P)
    (loss : ℝ) (hloss : 0 ≤ loss) (hretained : log2 (extensionCount P : ℝ) - loss ≤
      ∑ i, log2 ((L.size i).factorial : ℝ)) :
    ∃ π : Ranking n, Respects P π ∧
      (1 - Controller.productionError k) * log2 (extensionCount P : ℝ) - loss ≤ tree.cost π := by
  obtain ⟨π, hπ, hp⟩ := run_legal L k hk hcompare P hP tree
  refine ⟨π, hp, ?_⟩
  rw [(tree.run_matches_compatible_ranking (L.strategy k) [] π hπ).2]
  exact run_comparison_error L k hk hcompare P hP tree hcorrect loss hloss hretained

end SortingAdversary.Continuous.LayerReduction
