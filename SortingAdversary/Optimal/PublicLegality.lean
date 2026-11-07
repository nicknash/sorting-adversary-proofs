import SortingAdversary.Optimal.PublicOrder
import SortingAdversary.Optimal.ComparisonBound

/-!
# A polynomial public-order guard and online legality

The guard computes the Boolean public closure, answers implied queries, and
passes incomparable queries to the supplied policy. Whatever that policy does,
every resulting finite interaction has a compatible strict ranking. This
separates legality from the numerical accounting of a particular controller.
-/

namespace SortingAdversary.Optimal.PublicLegality

open SparseClosure PublicOrder

def earlier {n : ℕ} (o : Observation n) : Fin n :=
  match o.answer with | .less => o.query.left | .greater => o.query.right

def later {n : ℕ} (o : Observation n) : Fin n :=
  match o.answer with | .less => o.query.right | .greater => o.query.left

theorem earlier_ne_later {n : ℕ} (o : Observation n) : earlier o ≠ later o := by
  cases ha : o.answer
  · simpa [earlier, later, ha] using o.query.distinct
  · simpa [earlier, later, ha] using o.query.distinct.symm

@[simp] theorem holds_iff {n : ℕ} (π : Ranking n) (o : Observation n) :
    o.Holds π ↔ π (earlier o) < π (later o) := by
  cases ha : o.answer <;> simp [Observation.Holds, earlier, later, ha]

def historyRows {n : ℕ} (past : History n) : Rows (Fin n) :=
  fun u v => past.any (fun o => decide (u = earlier o ∧ v = later o))

@[simp] theorem historyRows_true {n : ℕ} (past : History n) (u v : Fin n) :
    historyRows past u v = true ↔
      ∃ o ∈ past, u = earlier o ∧ v = later o := by
  simp [historyRows]

theorem respects_history_iff {n : ℕ} (past : History n) (π : Ranking n) :
    Respects (historyRows past) π ↔ Compatible π past := by
  constructor
  · intro h
    apply List.forall_iff_forall_mem.mpr
    intro o ho
    apply (holds_iff π o).mpr
    have hle := h (earlier o) (later o) ((historyRows_true past _ _).mpr
      ⟨o, ho, rfl, rfl⟩)
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact (earlier_ne_later o (π.injective heq)).elim
  · intro h u v huv
    obtain ⟨o, ho, rfl, rfl⟩ := (historyRows_true past u v).mp huv
    exact ((holds_iff π o).mp (List.forall_iff_forall_mem.mp h o ho)).le

/-- Materialize the public closure once for this query. -/
def publicRows {n : ℕ} (past : History n) : Rows (Fin n) :=
  lookup (tableClosure (historyRows past))

@[simp] theorem publicRows_eq {n : ℕ} (past : History n) :
    publicRows past = closure (historyRows past) := lookup_tableClosure _

@[simp] theorem respects_public_iff {n : ℕ} (past : History n) (π : Ranking n) :
    Respects (publicRows past) π ↔ Compatible π past := by
  rw [publicRows_eq, respects_closure, respects_history_iff]

theorem publicRows_order {n : ℕ} {past : History n}
    (h : ∃ π : Ranking n, Compatible π past) : IsOrder (publicRows past) := by
  obtain ⟨π, hπ⟩ := h
  have hr := (respects_public_iff past π).mpr hπ
  refine ⟨?_, ?_, ?_⟩
  · intro v
    rw [publicRows_eq]
    exact closure_refl _ v
  · intro u v w huv hvw
    rw [publicRows_eq] at *
    exact closure_trans _ u v w huv hvw
  · intro u v huv hvu
    exact π.injective (le_antisymm (hr u v huv) (hr v u hvu))

def guardedAnswer {n : ℕ} (R : Rows (Fin n)) (q : Query n) (proposal : Answer) : Answer :=
  if R q.left q.right = true then .less
  else if R q.right q.left = true then .greater
  else proposal

def guard {n : ℕ} (proposal : Strategy n) : Strategy n :=
  fun past q => guardedAnswer (publicRows past) q (proposal past q)

theorem strict_of_row {n : ℕ} {R : Rows (Fin n)} {π : Ranking n}
    (hr : Respects R π) {u v : Fin n} (huv : R u v = true) (hne : u ≠ v) :
    π u < π v := by
  rcases lt_or_eq_of_le (hr u v huv) with hlt | heq
  · exact hlt
  · exact (hne (π.injective heq)).elim

/-- Any previously unknown oriented comparison has a concrete compatible
ranking after it is adjoined to the public order. -/
theorem extend_unknown {n : ℕ} {past : History n}
    (h : ∃ π : Ranking n, Compatible π past) (a b : Fin n)
    (hba : publicRows past b a ≠ true) (hne : a ≠ b) :
    ∃ π : Ranking n, Compatible π past ∧ π a < π b := by
  let R' : Rows (Fin n) := fun u v => publicRows past u v ||
    (publicRows past u a && publicRows past b v)
  have hR := publicRows_order h
  have hR' : IsOrder R' := adjoin_order hR a b hba
  let π := rankingExtension R'
  have hp : Respects R' π := rankingExtension_respects hR'
  refine ⟨π, (respects_public_iff past π).mp ?_, ?_⟩
  · intro u v huv
    apply hp u v
    simp only [R', Bool.or_eq_true, Bool.and_eq_true]
    exact Or.inl huv
  · apply strict_of_row hp _ hne
    simp only [R', Bool.or_eq_true, Bool.and_eq_true]
    exact Or.inr ⟨hR.refl a, hR.refl b⟩

theorem guard_extends {n : ℕ} (proposal : Strategy n) (past : History n) (q : Query n)
    (h : ∃ π : Ranking n, Compatible π past) :
    ∃ π : Ranking n, Compatible π (⟨q, guard proposal past q⟩ :: past) := by
  by_cases hf : publicRows past q.left q.right = true
  · obtain ⟨π, hπ⟩ := h
    refine ⟨π, (compatible_cons _ _ _).mpr ⟨?_, hπ⟩⟩
    have hs := strict_of_row ((respects_public_iff past π).mpr hπ) hf q.distinct
    simpa [guard, guardedAnswer, hf, Observation.Holds] using hs
  · by_cases hr : publicRows past q.right q.left = true
    · obtain ⟨π, hπ⟩ := h
      refine ⟨π, (compatible_cons _ _ _).mpr ⟨?_, hπ⟩⟩
      have hs := strict_of_row ((respects_public_iff past π).mpr hπ) hr q.distinct.symm
      simpa [guard, guardedAnswer, hf, hr, Observation.Holds] using hs
    · cases hp : proposal past q with
      | less =>
          obtain ⟨π, hπ, hs⟩ := extend_unknown h q.left q.right hr q.distinct
          refine ⟨π, (compatible_cons _ _ _).mpr ⟨?_, hπ⟩⟩
          simpa [guard, guardedAnswer, hf, hr, hp, Observation.Holds] using hs
      | greater =>
          obtain ⟨π, hπ, hs⟩ := extend_unknown h q.right q.left hf q.distinct.symm
          refine ⟨π, (compatible_cons _ _ _).mpr ⟨?_, hπ⟩⟩
          simpa [guard, guardedAnswer, hf, hr, hp, Observation.Holds] using hs

/-- A local extension property suffices for all finite adaptive interactions. -/
theorem run_consistent_of_extension {n : ℕ} (strategy : Strategy n)
    (hext : ∀ past q, (∃ π : Ranking n, Compatible π past) →
      ∃ π : Ranking n, Compatible π (⟨q, strategy past q⟩ :: past))
    (t : DecisionTree n) (past : History n)
    (hpast : ∃ π : Ranking n, Compatible π past) :
    ∃ π : Ranking n, Compatible π past ∧ Compatible π (t.run strategy past).observations := by
  induction t generalizing past with
  | leaf output =>
      obtain ⟨π, hπ⟩ := hpast
      exact ⟨π, hπ, compatible_nil π⟩
  | compare q onLess onGreater ihLess ihGreater =>
      have hnext := hext past q hpast
      cases ha : strategy past q with
      | less =>
          have hnext' : ∃ π : Ranking n, Compatible π (⟨q, .less⟩ :: past) := by
            simpa [ha] using hnext
          obtain ⟨π, hπ, hs⟩ := ihLess _ hnext'
          obtain ⟨ho, hp⟩ := (compatible_cons _ _ _).mp hπ
          refine ⟨π, hp, ?_⟩
          simpa [DecisionTree.run, ha] using (compatible_cons π ⟨q, .less⟩ _).mpr ⟨ho, hs⟩
      | greater =>
          have hnext' : ∃ π : Ranking n, Compatible π (⟨q, .greater⟩ :: past) := by
            simpa [ha] using hnext
          obtain ⟨π, hπ, hs⟩ := ihGreater _ hnext'
          obtain ⟨ho, hp⟩ := (compatible_cons _ _ _).mp hπ
          refine ⟨π, hp, ?_⟩
          simpa [DecisionTree.run, ha] using (compatible_cons π ⟨q, .greater⟩ _).mpr ⟨ho, hs⟩

/-- This is the actual repository's online legality target, for any supplied
family of proposed numerical answers. It asserts no comparison lower bound. -/
theorem guard_consistent (proposal : ∀ n, Strategy n) :
    ConsistentFamily (fun n => guard (proposal n)) := by
  intro n t
  obtain ⟨π, _, hπ⟩ := run_consistent_of_extension (guard (proposal n))
    (guard_extends (proposal n)) t [] ⟨Equiv.refl _, compatible_nil _⟩
  exact ⟨π, hπ⟩

end SortingAdversary.Optimal.PublicLegality
