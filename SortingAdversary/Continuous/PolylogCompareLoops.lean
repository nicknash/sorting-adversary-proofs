import SortingAdversary.Continuous.PolylogCompare
import SortingAdversary.Continuous.PolylogPrecision

/-!
# Simulation of selection and repair loops

Failed trials advance the depth by one. A successful selection therefore
leaves at least one of its trial slots unused for allocation. A repair
consumes one slot for each label in the reserved list.
-/

namespace SortingAdversary.Continuous.PolylogCompare

open Controller (Ready Admissible totalDepth makeMove applyMove)
open PolylogActive (Decision)
attribute [local instance] PolylogOracle.choices PolylogOracle.choices_valid
variable {n t b D k B : ℕ}

/-- Simulation of the concrete selection loop under its one-trial specifications. -/
theorem select_simulates (R : Memory n t b → Controller.Memory n → Prop)
    (hk : 64 ≤ k) (q : Query n)
    (test : ∀ m M, R m M → Ready k M → totalDepth M ≤ B →
      (check D k m q).value.realize M = PolylogOracle.attempt M k q)
    (step : ∀ m M, R m M → Ready k M → totalDepth M ≤ B → ∀ x,
      PolylogOracle.attempt M k q = .refine x (PolylogOracle.prefixAnchor M x) →
      R (move k m x (writePrefix D m x)).value
        (applyMove M (makeMove M x (PolylogOracle.prefixAnchor M x))))
    (fuel : ℕ) (m : Memory n t b) (M : Controller.Memory n) (rep : R m M)
    (ready : Ready k M) (room : totalDepth M + (fuel-1) ≤ B)
    {r : Controller.Result n} (ref : Controller.selectLoop k q fuel M = some r) :
    ∃ u, (select D k q fuel m).value = some (u,r.answer) ∧ R u r.memory ∧
      totalDepth r.memory ≤ totalDepth M + (fuel-1) := by
  induction fuel generalizing m M r with
  | zero => simp [Controller.selectLoop] at ref
  | succ fuel ih =>
    have current : totalDepth M ≤ B := by omega
    have eval := test m M rep ready current
    cases hd : (check D k m q).value with
    | answer a =>
      have part : PolylogOracle.attempt M k q = .answer a := by
        simpa only [hd,Decision.realize] using eval.symm
      change (match PolylogOracle.attempt M k q with
        | .answer a => some ⟨M,a,[]⟩
        | .refine x c => _) = some r at ref
      simp only [part, Option.some.injEq] at ref
      subst r
      exact ⟨m, by simp only [select, hd], rep, by simp⟩
    | refine x =>
      let c := PolylogOracle.prefixAnchor M x
      let N := applyMove M (makeMove M x c)
      let p := (move k m x (writePrefix D m x)).value
      have part : PolylogOracle.attempt M k q = .refine x c := by
        simpa only [hd,Decision.realize,c] using eval.symm
      have here : R p N := step m M rep ready current x part
      have nextReady := Controller.attempt_refine_ready M k hk ready q x c part
      change (match PolylogOracle.attempt M k q with
        | .answer a => some ⟨M,a,[]⟩
        | .refine y v => (Controller.selectLoop k q fuel (applyMove M (makeMove M y v))).map
          fun s => ⟨s.memory,s.answer,.selection (makeMove M y v)::s.actions⟩) = some r at ref
      rw [part] at ref
      change (Controller.selectLoop k q fuel N).map _ = some r at ref
      cases left : Controller.selectLoop k q fuel N with
      | none => simp [left] at ref
      | some s =>
        have positive : 0 < fuel := by
          by_contra! zero
          obtain rfl : fuel = 0 := by omega
          simp [Controller.selectLoop] at left
        have depth : totalDepth N = totalDepth M + 1 := Controller.totalDepth_applyMove ..
        have room' : totalDepth N + (fuel-1) ≤ B := by omega
        obtain ⟨u,hu,hs,ds⟩ := ih p N here nextReady room' left
        simp only [left,Option.map_some,Option.some.injEq] at ref
        subst r
        exact ⟨u, by simpa only [select,hd,p] using hu, hs, by dsimp only; omega⟩

/-- Simulation of a reserved list, in its original order after graph deletions. -/
theorem repairList_simulates (R : Memory n t b → Controller.Memory n → Prop)
    (hk : 64 ≤ k)
    (step : ∀ m M, R m M → Admissible k M → totalDepth M ≤ B → ∀ x,
      R (repairMove D k m x).value (applyMove M (makeMove M x (PolylogOracle.anchor M k x))))
    (xs : List (Fin n)) (m : Memory n t b) (M : Controller.Memory n) (rep : R m M)
    (adm : Admissible k M) (room : totalDepth M + xs.length ≤ B) :
    R (repairList D k xs m).value (Controller.pathBatch k M xs).1 := by
  induction xs generalizing m M with
  | nil => exact rep
  | cons x xs ih =>
    let N := applyMove M (makeMove M x (PolylogOracle.anchor M k x))
    have nextRep := step m M rep adm (by simp only [List.length_cons] at room; omega) x
    have nextAdm := (PolylogOracle.anchor_move_spec M k hk adm x).2.2.2.1
    have depth : totalDepth N = totalDepth M+1 := Controller.totalDepth_applyMove ..
    exact ih _ N nextRep nextAdm (by simp only [List.length_cons] at room; omega)

/-- Both the path and the singleton degree repair are the same ordered sequence
of moves as the controller's repair. -/
theorem reserved_repair (M : Controller.Memory n) (k : ℕ) :
    (Controller.pathBatch k M (PolylogRepair.reserved M.tree.system.edge k)).1 =
      (Controller.repair k M).1 := by
  cases hp : GraphPaths.firstPath M.tree.system.edge (2^k) with
  | some path => simp only [PolylogRepair.reserved,Controller.repair,hp]
  | none =>
    simp only [PolylogRepair.reserved,Controller.repair,hp]
    change (Controller.pathBatch k M (Controller.degreeChoice M k).toList).1 = _
    cases hd : Controller.degreeChoice M k <;> rfl

theorem reserved_length (M : Controller.Memory n) (k : ℕ) :
    (PolylogRepair.reserved M.tree.system.edge k).length ≤ 2^k := by
  unfold PolylogRepair.reserved
  cases hp : GraphPaths.firstPath M.tree.system.edge (2^k) with
  | some path => exact (GraphPaths.firstPath_some _ _ _ hp).1.le
  | none =>
    change (Controller.degreeChoice M k).toList.length ≤ _
    cases Controller.degreeChoice M k <;> simp [Nat.one_le_pow]

end SortingAdversary.Continuous.PolylogCompare
