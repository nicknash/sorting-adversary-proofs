import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Sym.Card
import Mathlib.Data.Multiset.Sort

/-!
# The terminal count for a pool whose order is known

If the public comparisons have determined the order of the free labels in a
pool, their colours form a nondecreasing tuple. Such tuples correspond exactly
to multisets: sorting recovers the tuple from its multiset of colours. The
stars-and-bars count is therefore `choose (K + r - 1) r` for `r` free labels and
`K` available colours. Individual lists and fixed pins can only reduce it.

The final theorem is stated for an actual finite family of assignments on an
arbitrary label type. It proves the needed injection by restricting to an
enumeration of the free labels; values outside this enumeration are fixed.
It does not assume the desired cardinality bound as a hypothesis.
-/

namespace SortingAdversary.Optimal.Terminal

/-- A tuple of colours in the order already known by the sorter. -/
abbrev MonotoneColorMap (r K : ℕ) := {f : Fin r → Fin K // Monotone f}

/-- Forget the positions in a colour tuple, retaining multiplicities. -/
def tupleMultiset {r K : ℕ} (f : Fin r → Fin K) : Sym (Fin K) r :=
  ⟨(List.ofFn f : Multiset (Fin K)), by simp⟩

/-- Sorting makes the tuple-to-multiset map injective on monotone tuples. -/
theorem monotone_tupleMultiset_injective (r K : ℕ) :
    Function.Injective (fun f : MonotoneColorMap r K => tupleMultiset f.val) := by
  intro f g h
  apply Subtype.ext
  apply List.ofFn_injective
  have hmult : (List.ofFn f.val : Multiset (Fin K)) = List.ofFn g.val :=
    congrArg Subtype.val h
  exact List.Perm.eq_of_sortedLE f.property.sortedLE_ofFn g.property.sortedLE_ofFn
    (Multiset.coe_eq_coe.mp hmult)

/-- Every multiset has a monotone tuple, namely its sorted enumeration. -/
theorem monotone_tupleMultiset_surjective (r K : ℕ) :
    Function.Surjective (fun f : MonotoneColorMap r K => tupleMultiset f.val) := by
  intro s
  rcases s with ⟨s, hs⟩
  let l : List (Fin K) := s.sort (· ≤ ·)
  have hlen : l.length = r := by simpa [l] using hs
  have hl : l.SortedLE := (Multiset.pairwise_sort s (· ≤ ·)).sortedLE
  cases hlen
  refine ⟨⟨l.get, hl.monotone_get⟩, ?_⟩
  apply Subtype.ext
  change (List.ofFn l.get : Multiset (Fin K)) = s
  rw [List.ofFn_get]
  exact Multiset.sort_eq s (· ≤ ·)

/-- Exact stars-and-bars count, including empty tuples and empty palettes. -/
theorem card_monotoneColorMap (r K : ℕ) :
    Fintype.card (MonotoneColorMap r K) = (K + r - 1).choose r := by
  classical
  calc
    Fintype.card (MonotoneColorMap r K) = Fintype.card (Sym (Fin K) r) :=
      Fintype.card_congr (Equiv.ofBijective _
        ⟨monotone_tupleMultiset_injective r K, monotone_tupleMultiset_surjective r K⟩)
    _ = (K + r - 1).choose r := by simp [Sym.card_sym_eq_choose]

/-- Any actual finite family of monotone tuples satisfies the terminal bound.
Additional unary lists or comparison constraints may define this family. -/
theorem card_le_choose_of_monotone {r K : ℕ} (S : Finset (Fin r → Fin K))
    (hmono : ∀ f ∈ S, Monotone f) :
    S.card ≤ (K + r - 1).choose r := by
  classical
  let embed : S → MonotoneColorMap r K := fun f => ⟨f.val, hmono f.val f.property⟩
  have hinj : Function.Injective embed := by
    intro f g h
    exact Subtype.ext (congrArg (fun z : MonotoneColorMap r K => z.val) h)
  have h := Fintype.card_le_of_injective embed hinj
  simpa only [Fintype.card_coe, card_monotoneColorMap] using h

/-- Restricting to the free-label enumeration determines the whole assignment
when all other colours are fixed. Enumerating in the final public order makes
the restriction monotone and proves the same terminal count for the pool.

The enumeration need not be onto all labels, because the remaining labels are
pins. It may be supplied by an equivalence `Fin r ≃ {x // x is free}` followed
by the subtype projection. -/
theorem card_le_choose_of_fixed_pins {α : Type*} {r K : ℕ}
    (S : Finset (α → Fin K)) (enumerate : Fin r → α) (pin : α → Fin K)
    (hmono : ∀ f ∈ S, Monotone (fun i => f (enumerate i)))
    (hpins : ∀ f ∈ S, ∀ x, x ∉ Set.range enumerate → f x = pin x) :
    S.card ≤ (K + r - 1).choose r := by
  classical
  let restrict : S → MonotoneColorMap r K := fun f =>
    ⟨fun i => f.val (enumerate i), hmono f.val f.property⟩
  have hinj : Function.Injective restrict := by
    intro f g h
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ Set.range enumerate
    · obtain ⟨i, rfl⟩ := hx
      exact congrFun (congrArg Subtype.val h) i
    · exact (hpins f.val f.property x hx).trans (hpins g.val g.property x hx).symm
  have h := Fintype.card_le_of_injective restrict hinj
  simpa only [Fintype.card_coe, card_monotoneColorMap] using h

/-- A public-order version: each member of the finite family respects the
known order weakly, and the enumeration follows that order. -/
theorem card_le_choose_of_public_order {α : Type*} {r K : ℕ}
    (S : Finset (α → Fin K)) (R : α → α → Prop)
    (enumerate : Fin r → α) (pin : α → Fin K)
    (hordered : ∀ i j, i ≤ j → R (enumerate i) (enumerate j))
    (hrespect : ∀ f ∈ S, ∀ x y, R x y → f x ≤ f y)
    (hpins : ∀ f ∈ S, ∀ x, x ∉ Set.range enumerate → f x = pin x) :
    S.card ≤ (K + r - 1).choose r := by
  apply card_le_choose_of_fixed_pins S enumerate pin _ hpins
  intro f hf i j hij
  exact hrespect f hf (enumerate i) (enumerate j) (hordered i j hij)

end SortingAdversary.Optimal.Terminal
