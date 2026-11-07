import SortingAdversary.Optimal.IndexedHubHistory
import SortingAdversary.Optimal.TreePriceBudget

/-!
# Hub counts on the actual finite destination palette

The global dictionary uses natural immutable colour names; the actual tree
uses bounded palette identities. This file identifies their sums exactly,
including empty fibres, and bounds each count by its real child population.
-/

namespace SortingAdversary.Optimal.SlotHubHistory

open scoped BigOperators
open WidthRepair PoolState StoredStateIndex RepairPricing IndexedHubHistory
open TreePriceBudget

variable {n H : ℕ}

def key (tree : StoredTree n) (slot : Slot tree) : StateIndex tree × ℕ := (slot.1, slot.2.val)

theorem key_injective (tree : StoredTree n) : Function.Injective (key tree) := by
  rintro ⟨i, c⟩ ⟨j, d⟩ he
  have hi := congrArg Prod.fst he
  dsimp only [key] at hi
  cases hi
  have hc : c = d := Fin.ext (congrArg Prod.snd he)
  cases hc
  rfl

def count (tree : StoredTree n) (history : GlobalHistory.Events (StateIndex tree) n H)
    (slot : Slot tree) : ℕ := GlobalHistory.countAt history (key tree slot)

theorem count_le_population (tree : StoredTree n) (history : GlobalHistory.Events (StateIndex tree) n H)
    (fits : ∀ i, (history i).2.Fits (stateAt tree (history i).1))
    (unique : Function.Injective (fun i => ((history i).1, (history i).2.vertex))) (slot : Slot tree) :
    count tree history slot ≤ population tree slot :=
  countAt_le_pinFiber (stateAt tree) history fits unique slot.1 slot.2

theorem count_zero_of_not_destination {Node : Type*} [DecidableEq Node]
    (history : GlobalHistory.Events Node n H) (destination : Node × ℕ)
    (absent : destination ∉ GlobalHistory.destinations history) : GlobalHistory.countAt history destination = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact absent (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)

theorem destinations_subset_keys (tree : StoredTree n) (history : GlobalHistory.Events (StateIndex tree) n H)
    (fits : ∀ i, (history i).2.Fits (stateAt tree (history i).1)) :
    GlobalHistory.destinations history ⊆ Finset.univ.image (key tree) := by
  intro destination hd
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
  exact Finset.mem_image.mpr ⟨⟨(history i).1, ⟨(history i).2.identity, fits_identity_lt (fits i)⟩⟩,
    Finset.mem_univ _, rfl⟩

theorem sum_keys {M : Type*} [AddCommMonoid M] (tree : StoredTree n)
    (history : GlobalHistory.Events (StateIndex tree) n H)
    (fits : ∀ i, (history i).2.Fits (stateAt tree (history i).1))
    (f : StateIndex tree × ℕ → ℕ → M) (zero : ∀ c, f c 0 = 0) :
    (∑ c ∈ GlobalHistory.destinations history, f c (GlobalHistory.countAt history c)) =
      ∑ c : Slot tree, f (key tree c) (count tree history c) := by
  have hsum : (∑ c ∈ GlobalHistory.destinations history, f c (GlobalHistory.countAt history c)) =
      ∑ c ∈ Finset.univ.image (key tree), f c (GlobalHistory.countAt history c) := by
    apply Finset.sum_subset (destinations_subset_keys tree history fits)
    intro c hc absent
    rw [count_zero_of_not_destination history c absent, zero]
  rw [hsum, Finset.sum_image]
  · rfl
  · exact fun _ _ _ _ he => key_injective tree he

theorem countAt_sum {Node : Type*} [DecidableEq Node] (history : GlobalHistory.Events Node n H) :
    (∑ c ∈ GlobalHistory.destinations history, GlobalHistory.countAt history c) = H := by
  simpa only [GlobalHistory.destinations, GlobalHistory.countAt, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_eq_sum_card_image (fun i => ((history i).1, (history i).2.identity)) Finset.univ).symm

theorem count_sum (tree : StoredTree n) (history : GlobalHistory.Events (StateIndex tree) n H)
    (fits : ∀ i, (history i).2.Fits (stateAt tree (history i).1)) :
    (∑ c : Slot tree, count tree history c) = H := by
  rw [← sum_keys tree history fits (fun _ k => k) (fun _ => rfl)]
  exact countAt_sum history

theorem occupied_sum {M : Type*} [AddCommMonoid M] (tree : StoredTree n)
    (history : GlobalHistory.Events (StateIndex tree) n H)
    (bounded : ∀ c, count tree history c ≤ population tree c) (f : ℕ → M) (zero : f 0 = 0) :
    (∑ c ∈ TreePriceBudget.destinations tree, f (count tree history c)) =
      ∑ c : Slot tree, f (count tree history c) := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro c hc absent
  have hp : population tree c = 0 := by
    by_contra h
    exact absent (Finset.mem_filter.mpr ⟨hc, Nat.pos_of_ne_zero h⟩)
  have hz : count tree history c = 0 := Nat.eq_zero_of_le_zero (by simpa only [hp] using bounded c)
  rw [hz, zero]

theorem factorial_sum_keys (tree : StoredTree n) (history : GlobalHistory.Events (StateIndex tree) n H)
    (fits : ∀ i, (history i).2.Fits (stateAt tree (history i).1)) :
    (∑ c ∈ GlobalHistory.destinations history, Real.log ((GlobalHistory.countAt history c).factorial : ℝ)) =
      ∑ c : Slot tree, Real.log ((count tree history c).factorial : ℝ) :=
  sum_keys tree history fits (fun _ k => Real.log (k.factorial : ℝ)) (by simp)

theorem entropy_sum_keys (tree : StoredTree n) (history : GlobalHistory.Events (StateIndex tree) n H)
    (fits : ∀ i, (history i).2.Fits (stateAt tree (history i).1)) (exponent : StateIndex tree → ℕ) :
    (∑ c ∈ GlobalHistory.destinations history, (GlobalHistory.countAt history c : ℝ) *
      Real.log ((2 : ℝ) ^ exponent c.1 / GlobalHistory.countAt history c)) =
      ∑ c : Slot tree, (count tree history c : ℝ) * Real.log ((2 : ℝ) ^ exponent c.1 / count tree history c) :=
  sum_keys tree history fits (fun c k => (k : ℝ) * Real.log ((2 : ℝ) ^ exponent c.1 / k)) (by simp)

end SortingAdversary.Optimal.SlotHubHistory
