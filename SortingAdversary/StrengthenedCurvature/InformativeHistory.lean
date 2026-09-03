import SortingAdversary.Knowledge
import SortingAdversary.StrengthenedCurvature.AdversaryPotential

/-!
# Retaining only informative comparisons

The paper's history DAG acquires a row only when a comparison is not already
implied by transitive closure.  Algorithms may repeat comparisons, so this
distinction is essential: blindly adding duplicate rows would change the
Hessian and would not formalize the stated adversary.

Histories supplied to a `Strategy` are reverse chronological.  Recursing on
the tail therefore reconstructs the knowledge available immediately before
the head observation was answered.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

/-- Lower endpoint of an oriented answered comparison. -/
def lower (o : Observation n) : Item n :=
  match o.answer with
  | .less => o.query.left
  | .greater => o.query.right

/-- Upper endpoint of an oriented answered comparison. -/
def upper (o : Observation n) : Item n :=
  match o.answer with
  | .less => o.query.right
  | .greater => o.query.left

@[simp] theorem holds_iff_lower_lt_upper
    (π : Ranking n) (o : Observation n) :
    o.Holds π ↔ π (lower o) < π (upper o) := by
  cases o with
  | mk q answer => cases answer <;> rfl

/-- Whether the current transitive closure already contains an observation. -/
def EntailedBy (o : Observation n) (h : History n) : Prop :=
  (Knowledge.ofHistory h).rel (lower o) (upper o)

/-- Remove observations which were already entailed at the time they were
answered.  The result remains reverse chronological. -/
noncomputable def retainedHistory : History n → History n
  | [] => []
  | o :: past =>
      let retainedPast := retainedHistory past
      @ite (History n) (EntailedBy o retainedPast) (Classical.propDecidable _)
        retainedPast (o :: retainedPast)

@[simp] theorem retainedHistory_nil :
    retainedHistory ([] : History n) = [] := rfl

/-- Dropping entailed observations never destroys compatibility. -/
theorem compatible_retainedHistory (π : Ranking n) :
    ∀ h : History n, Compatible π h → Compatible π (retainedHistory h)
  | [], _ => compatible_nil π
  | o :: past, hcompat => by
      have hparts := (compatible_cons π o past).1 hcompat
      simp only [retainedHistory]
      split
      · exact compatible_retainedHistory π past hparts.2
      · exact (compatible_cons π o (retainedHistory past)).2
          ⟨hparts.1, compatible_retainedHistory π past hparts.2⟩

/-- Retained histories have exactly the same ranking semantics as the full
transcript: every removed observation was already implied by rows which remain. -/
theorem compatible_of_retainedHistory (π : Ranking n) :
    ∀ h : History n, Compatible π (retainedHistory h) → Compatible π h
  | [], _ => compatible_nil π
  | o :: past, hcompat => by
      by_cases hentails : EntailedBy o (retainedHistory past)
      · have hpastRetained : Compatible π (retainedHistory past) := by
          simpa [retainedHistory, hentails] using hcompat
        exact (compatible_cons π o past).2
          ⟨(holds_iff_lower_lt_upper π o).2
              (Knowledge.realizes_ofHistory π (retainedHistory past) hpastRetained hentails),
            compatible_of_retainedHistory π past hpastRetained⟩
      · have hparts : o.Holds π ∧ Compatible π (retainedHistory past) := by
          simpa [retainedHistory, hentails] using hcompat
        exact (compatible_cons π o past).2
          ⟨hparts.1, compatible_of_retainedHistory π past hparts.2⟩

theorem compatible_retainedHistory_iff (π : Ranking n) (h : History n) :
    Compatible π (retainedHistory h) ↔ Compatible π h :=
  ⟨compatible_of_retainedHistory π h, compatible_retainedHistory π h⟩

/-- In particular, a feasible transcript has a feasible retained history. -/
theorem feasible_retainedHistory {h : History n} (hh : Feasible h) :
    Feasible (retainedHistory h) := by
  obtain ⟨π, hπ⟩ := hh
  exact ⟨π, compatible_retainedHistory π h hπ⟩

/-- Semantic soundness of the entailment test. -/
theorem holds_of_entailed (π : Ranking n) (o : Observation n) (h : History n)
    (hcompat : Compatible π h) (hentails : EntailedBy o h) : o.Holds π := by
  rw [holds_iff_lower_lt_upper]
  exact Knowledge.realizes_ofHistory π h hcompat hentails

/-- Adding an already entailed answer preserves feasibility. -/
theorem feasible_answerHistory_of_entailed (h : History n) (q : Query n)
    (a : Answer) (hh : Feasible h)
    (hentails : EntailedBy (Observation.mk q a) h) :
    Feasible (answerHistory h q a) := by
  obtain ⟨π, hπ⟩ := hh
  refine ⟨π, (compatible_cons π ⟨q, a⟩ h).2 ⟨?_, hπ⟩⟩
  exact holds_of_entailed π ⟨q, a⟩ h hπ hentails

/-- The retained state is unchanged by adjoining an entailed answer. -/
theorem retainedHistory_answerHistory_of_entailed (h : History n) (q : Query n)
    (a : Answer) (hentails : EntailedBy (Observation.mk q a) (retainedHistory h)) :
    retainedHistory (answerHistory h q a) = retainedHistory h := by
  simp [answerHistory, retainedHistory, hentails]

/-- An unentailed answer contributes exactly one retained history row. -/
theorem retainedHistory_answerHistory_of_not_entailed (h : History n) (q : Query n)
    (a : Answer) (hnot : ¬EntailedBy (Observation.mk q a) (retainedHistory h)) :
    retainedHistory (answerHistory h q a) =
      Observation.mk q a :: retainedHistory h := by
  simp [answerHistory, retainedHistory, hnot]

end StrengthenedCurvature
end SortingAdversary
