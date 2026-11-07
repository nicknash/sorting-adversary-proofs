import SortingAdversary.Strategy
import SortingAdversary.Optimal.SparseClosure
import SortingAdversary.Optimal.Routing
import Mathlib.Data.Fintype.Card

/-!
# Public partial orders have concrete ranking extensions

A finite closed antisymmetric Boolean relation can be extended by first sorting
the labels by predecessor count, then breaking ties by label. Counting the keys
strictly below each key gives a permutation of the ranks. This supplies the
actual sorting semantics without counting linear extensions.
-/

namespace SortingAdversary.Optimal.PublicOrder

open SparseClosure

structure IsOrder {n : ℕ} (R : Rows (Fin n)) : Prop where
  refl : ∀ v, R v v = true
  trans : ∀ u v w, R u v = true → R v w = true → R u w = true
  antisymm : ∀ u v, R u v = true → R v u = true → u = v

def predecessorCount {n : ℕ} (R : Rows (Fin n)) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun u => R u v = true)).card

theorem predecessorCount_strict {n : ℕ} {R : Rows (Fin n)} (h : IsOrder R)
    {u v : Fin n} (huv : R u v = true) (hne : u ≠ v) :
    predecessorCount R u < predecessorCount R v := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact h.trans x u v hx huv
  · intro heq
    have hv : v ∈ Finset.univ.filter (fun x => R x v = true) := by simp [h.refl v]
    rw [← heq] at hv
    have hvu : R v u = true := by simpa using hv
    exact hne (h.antisymm u v huv hvu)

/-- The final label coordinate makes keys distinct. -/
def extensionKey {n : ℕ} (R : Rows (Fin n)) (v : Fin n) : ℕ :=
  predecessorCount R v * n + v.val

theorem extensionKey_injective {n : ℕ} (R : Rows (Fin n)) :
    Function.Injective (extensionKey R) := by
  intro u v huv
  have hm := congrArg (fun k => k % n) huv
  simp [extensionKey, Nat.add_mod, Nat.mod_eq_of_lt u.isLt,
    Nat.mod_eq_of_lt v.isLt] at hm
  exact Fin.ext hm

theorem extensionKey_strict {n : ℕ} {R : Rows (Fin n)} (h : IsOrder R)
    {u v : Fin n} (huv : R u v = true) (hne : u ≠ v) :
    extensionKey R u < extensionKey R v := by
  have hc := predecessorCount_strict h huv hne
  have hm := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hc)
  calc
    extensionKey R u < predecessorCount R u * n + n := Nat.add_lt_add_left u.isLt _
    _ = (predecessorCount R u + 1) * n := by simp [Nat.add_mul]
    _ ≤ predecessorCount R v * n := hm
    _ ≤ extensionKey R v := Nat.le_add_right _ _

def lowerKeys {n : ℕ} (key : Fin n → ℕ) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => key u < key v)

theorem lowerKeys_card_lt {n : ℕ} (key : Fin n → ℕ) (v : Fin n) :
    (lowerKeys key v).card < n := by
  have hs : lowerKeys key v ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have hv : v ∈ lowerKeys key v := heq.symm ▸ Finset.mem_univ v
    simp [lowerKeys] at hv
  simpa using Finset.card_lt_card hs

theorem lowerKeys_strict {n : ℕ} (key : Fin n → ℕ) {u v : Fin n}
    (huv : key u < key v) : (lowerKeys key u).card < (lowerKeys key v).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro x hx
    simp only [lowerKeys, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.trans huv
  · intro heq
    have hu : u ∈ lowerKeys key v := by simp [lowerKeys, huv]
    rw [← heq] at hu
    simp [lowerKeys] at hu

/-- Executable rank assignment obtained from predecessor counts. -/
def extensionRank {n : ℕ} (R : Rows (Fin n)) (v : Fin n) : Fin n :=
  ⟨(lowerKeys (extensionKey R) v).card, lowerKeys_card_lt _ _⟩

theorem extensionRank_strict {n : ℕ} {R : Rows (Fin n)} (h : IsOrder R)
    {u v : Fin n} (huv : R u v = true) (hne : u ≠ v) :
    extensionRank R u < extensionRank R v :=
  lowerKeys_strict _ (extensionKey_strict h huv hne)

theorem extensionRank_injective {n : ℕ} (R : Rows (Fin n)) :
    Function.Injective (extensionRank R) := by
  intro u v heq
  by_contra hne
  have hk : extensionKey R u ≠ extensionKey R v := (extensionKey_injective R).ne hne
  have hc := congrArg Fin.val heq
  rcases lt_or_gt_of_ne hk with hlt | hgt
  · have hh := lowerKeys_strict _ hlt
    exact (ne_of_lt hh) hc
  · have hh := lowerKeys_strict _ hgt
    exact (ne_of_lt hh) hc.symm

/-- The inverse permutation is needed only by the semantic `Ranking` type;
the rank values and every query answer are the executable function above. -/
noncomputable def rankingExtension {n : ℕ} (R : Rows (Fin n)) : Ranking n :=
  Equiv.ofBijective (extensionRank R)
    ⟨extensionRank_injective R, Finite.surjective_of_injective (extensionRank_injective R)⟩

@[simp] theorem rankingExtension_apply {n : ℕ} (R : Rows (Fin n)) (v : Fin n) :
    rankingExtension R v = extensionRank R v := rfl

theorem rankingExtension_respects {n : ℕ} {R : Rows (Fin n)} (h : IsOrder R) :
    Respects R (rankingExtension R) := by
  intro u v huv
  by_cases heq : u = v
  · subst v
    exact le_rfl
  · exact (extensionRank_strict h huv heq).le

theorem adjoin_order {n : ℕ} {R : Rows (Fin n)} (h : IsOrder R)
    (a b : Fin n) (hba : R b a ≠ true) :
    IsOrder (fun u v => R u v || (R u a && R b v)) := by
  constructor
  · intro v
    simp [h.refl v]
  · intro u v w huv hvw
    have huv' : Routing.adjoin (fun x y => R x y = true) a b u v := by simpa [Routing.adjoin] using huv
    have hvw' : Routing.adjoin (fun x y => R x y = true) a b v w := by simpa [Routing.adjoin] using hvw
    have hh := Routing.adjoin_transitive (fun {x y z} hxy hyz => h.trans x y z hxy hyz)
      a b huv' hvw'
    simpa [Routing.adjoin] using hh
  · intro u v huv hvu
    apply Routing.adjoin_antisymmetric
      (fun {x y z} hxy hyz => h.trans x y z hxy hyz) h.antisymm hba u v
    · simpa [Routing.adjoin] using huv
    · simpa [Routing.adjoin] using hvu

end SortingAdversary.Optimal.PublicOrder
