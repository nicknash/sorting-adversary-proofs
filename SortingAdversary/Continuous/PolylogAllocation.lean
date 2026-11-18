import SortingAdversary.Continuous.PolylogResources
import SortingAdversary.Continuous.PolylogCompare

/-!
# Allocation on the stored comparison path

Evaluate the allocation invariant on the actual outputs of the heap writers,
selector, record operation, and path repair. The count carried by the invariant
is the number of committed refinements. Query and graph updates outside a
refinement leave it fixed.
-/

namespace SortingAdversary.Continuous.PolylogCompare

open PolylogBits PolylogResources
open Optimal.Parameters (logCap)

variable {n t b : ℕ}

abbrev Memory.Sized (m : Memory n t b) (moves : ℕ) : Prop :=
  PolylogResources.Sized (logCap n) b moves m.spatial.directory m.heap

theorem initialize_sized (n t b D : ℕ) : (initialMemory n t b D).Sized 0 :=
  PolylogResources.initialized blockStore (logCap n) b D t

theorem prefix_growth (D : ℕ) (m : Memory n t b) (x : Fin n) :
    (writePrefix D m x).out.heap.next ≤ m.heap.next + perMove (logCap n) b :=
  (PolylogRawAnchor.growth_bound D (D-2) m.valid m.typed m.cache (le_refl b)
    (m.spatial.walls.lower.get x.val).value (m.spatial.walls.upper.get x.val).value).trans
      (Nat.add_le_add_left (le_max_left ..) _)

theorem mint_growth (D : ℕ) (m : Memory n t b) (x : Fin n) (test : Option ℚ) :
    (mint D m x test).out.heap.next ≤ m.heap.next + perMove (logCap n) b := by
  cases test with
  | none => exact prefix_growth D m x
  | some q =>
    let z := PolylogAnchorWrite.numerator q (logCap n)
    let w := PolylogEmbed.embedAddr D (logCap n) z m.valid m.cache (le_refl b)
    exact w.allocated.trans (Nat.add_le_add_left
      ((PolylogEmbed.embedAddr_work D (logCap n) z m.valid m.cache (le_refl b)).trans (le_max_right ..)) _)

theorem move_sized (k : ℕ) (m : Memory n t b) {i : ℕ} (sz : m.Sized i)
    (x : Fin n) (writer : WriteResult m) (hw : writer.out.heap.next ≤ m.heap.next+perMove (logCap n) b) :
    (move k m x writer).value.Sized (i+1) :=
  PolylogResources.sized_move sz x writer.out.addr hw

theorem record_sized (k : ℕ) (m : Memory n t b) {i : ℕ} (sz : m.Sized i)
    (q : Query n) (a : Answer) : (record k m q a).value.1.Sized i := sz

theorem repairMove_sized (D k : ℕ) (m : Memory n t b) {i : ℕ} (sz : m.Sized i)
    (x : Fin n) : (repairMove D k m x).value.Sized (i+1) :=
  move_sized k m sz x _ (mint_growth D m x _)

theorem repairList_sized (D k : ℕ) (xs : List (Fin n)) (m : Memory n t b)
    {i : ℕ} (sz : m.Sized i) : (repairList D k xs m).value.Sized (i+xs.length) := by
  induction xs generalizing m i with
  | nil => exact sz
  | cons x xs ih =>
    simpa only [repairList, List.length_cons, Nat.succ_add, Nat.add_succ] using
      ih _ (repairMove_sized D k m sz x)

theorem select_sized (D k : ℕ) (q : Query n) (fuel : ℕ) (m : Memory n t b)
    {i : ℕ} (sz : m.Sized i) {u : Memory n t b} {a : Answer}
    (ok : (select D k q fuel m).value = some (u,a)) :
    ∃ j < fuel, u.Sized (i+j) := by
  induction fuel generalizing m i with
  | zero => simp [select] at ok
  | succ fuel ih =>
    cases ht : (check D k m q).value with
    | answer ans =>
      simp only [select, ht, Option.some.injEq, Prod.mk.injEq] at ok
      exact ⟨0,Nat.zero_lt_succ _, ok.1 ▸ sz⟩
    | refine x =>
      simp only [select, ht] at ok
      obtain ⟨j, hf, sj⟩ := ih _ (move_sized k m sz x _ (prefix_growth D m x)) ok
      exact ⟨j+1, Nat.succ_lt_succ hf, by simpa only [Nat.succ_add, Nat.add_succ] using sj⟩

/-- Allocation for the stored comparison, in terms of its actual reserved list. -/
theorem compare_sized (D k : ℕ) (m : Memory n t b) (q : Query n)
    {i : ℕ} (sz : m.Sized i) {out : Memory n t b} {a : Answer}
    (ok : (compare D k m q).value = some (out,a)) :
    ∃ u j, j ≤ 2 ∧ (select D k q 3 m).value = some (u,a) ∧
      let r := (record k u q a).value
      let path := (PolylogRepair.choose r.1.spatial.graph k r.2).value
      out.Sized (i+j+path.length) := by
  cases hs : (select D k q 3 m).value with
  | none => simp [compare,hs] at ok
  | some z =>
    obtain ⟨u,ans⟩ := z
    obtain ⟨j,hj,us⟩ := select_sized D k q 3 m sz hs
    simp only [compare,hs,Option.some.injEq,Prod.mk.injEq] at ok
    obtain ⟨rfl, rfl⟩ := ok
    refine ⟨u,j,by omega,rfl, ?_⟩
    exact repairList_sized D k _ _ (record_sized k u us q ans)

end SortingAdversary.Continuous.PolylogCompare
