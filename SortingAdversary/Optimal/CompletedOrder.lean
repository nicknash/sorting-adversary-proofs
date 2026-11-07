import SortingAdversary.Optimal.PublicLegality
import SortingAdversary.Optimal.Terminal
import Mathlib.Data.Finset.Sort

/-!
# Correct sorting forces a total public order

At the end of a correct sorting-tree interaction, any compatible ranking must
equal the output. If a pair were still incomparable in the public closure,
both orientations would have compatible ranking extensions. Thus the public
order is total. Sorting a pool's actual free-label set by that ranking then
supplies the enumeration required by the terminal count theorem.
-/

namespace SortingAdversary.Optimal.CompletedOrder

open SparseClosure PublicOrder PublicLegality WeakMaps WeakMaps.WeakSystem

theorem compatible_eq_output {n : ℕ} (t : DecisionTree n) (ht : t.Correct)
    (strategy : Strategy n) (past : History n) (π : Ranking n)
    (hπ : Compatible π (t.run strategy past).observations) :
    π = (t.run strategy past).output := by
  exact (ht π).symm.trans (t.run_matches_compatible_ranking strategy past π hπ).1

theorem public_total_of_unique {n : ℕ} {past : History n}
    (hne : ∃ π : Ranking n, Compatible π past)
    (hunique : ∀ π ρ : Ranking n, Compatible π past → Compatible ρ past → π = ρ) :
    ∀ a b, publicRows past a b = true ∨ publicRows past b a = true := by
  intro a b
  by_cases hab : publicRows past a b = true
  · exact Or.inl hab
  · right
    by_contra hba
    have hneab : a ≠ b := by
      rintro rfl
      exact hab ((publicRows_order hne).refl a)
    obtain ⟨π, hπ, hlt⟩ := extend_unknown hne a b hba hneab
    obtain ⟨ρ, hρ, hgt⟩ := extend_unknown hne b a hab hneab.symm
    have heq := hunique π ρ hπ hρ
    rw [← heq] at hgt
    exact lt_asymm hlt hgt

/-- The order inferred from the actual terminal transcript is exactly its
compatible ranking's order. -/
theorem completed_relation_iff {n : ℕ} (t : DecisionTree n) (ht : t.Correct)
    (strategy : Strategy n) (past : History n) (π : Ranking n)
    (hπ : Compatible π (t.run strategy past).observations) (a b : Fin n) :
    publicRows (t.run strategy past).observations a b = true ↔ π a ≤ π b := by
  let transcript := (t.run strategy past).observations
  have hr : Respects (publicRows transcript) π := (respects_public_iff _ _).mpr hπ
  have htotal := public_total_of_unique (past := transcript) ⟨π, hπ⟩ (by
    intro ρ σ hρ hσ
    exact (compatible_eq_output t ht strategy past ρ hρ).trans
      (compatible_eq_output t ht strategy past σ hσ).symm)
  constructor
  · exact hr a b
  · intro hle
    rcases htotal a b with hab | hba
    · exact hab
    · have heq : a = b := π.injective (le_antisymm hle (hr b a hba))
      subst b
      exact (publicRows_order ⟨π, hπ⟩).refl a

/-- Enumerate exactly the free labels in increasing order of an actual
ranking. This finite sorting operation does not enumerate colour maps. -/
noncomputable def freeEnumeration {n : ℕ} (π : Ranking n) (free : Finset (Fin n)) :
    Fin free.card → Fin n :=
  fun i => π.symm ((free.image π).orderEmbOfFin
    (Finset.card_image_of_injective free π.injective) i)

theorem freeEnumeration_mem {n : ℕ} (π : Ranking n) (free : Finset (Fin n))
    (i : Fin free.card) : freeEnumeration π free i ∈ free := by
  have hm := (free.image π).orderEmbOfFin_mem
    (Finset.card_image_of_injective free π.injective) i
  obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hm
  have hh : freeEnumeration π free i = x := by
    simp only [freeEnumeration, ← heq, Equiv.symm_apply_apply]
  exact hh.symm ▸ hx

theorem range_freeEnumeration {n : ℕ} (π : Ranking n) (free : Finset (Fin n)) :
    Set.range (freeEnumeration π free) = (free : Set (Fin n)) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact freeEnumeration_mem π free i
  · intro hx
    have hm : π x ∈ free.image π := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    change π x ∈ (↑(free.image π) : Set (Fin n)) at hm
    rw [← Finset.range_orderEmbOfFin (free.image π)
      (Finset.card_image_of_injective free π.injective)] at hm
    obtain ⟨i, hi⟩ := hm
    refine ⟨i, ?_⟩
    simp [freeEnumeration, hi]

theorem freeEnumeration_ordered {n : ℕ} (π : Ranking n) (free : Finset (Fin n)) :
    Monotone (fun i => π (freeEnumeration π free i)) := by
  intro i j hij
  simp only [freeEnumeration, Equiv.apply_symm_apply]
  exact ((free.image π).orderEmbOfFin
    (Finset.card_image_of_injective free π.injective)).monotone hij

/-- The terminal bound now follows from correctness of the actual sorter,
public-order respect on the free labels, and the fixed colours outside them. -/
theorem terminal_count_of_correct_run {n K : ℕ} (t : DecisionTree n) (ht : t.Correct)
    (strategy : Strategy n) (past : History n) (π : Ranking n)
    (hπ : Compatible π (t.run strategy past).observations)
    (S : WeakSystem (Fin n) K) (free : Finset (Fin n)) (pin : Fin n → Fin K)
    (hrespect : ∀ f, S.Valid f → ∀ x ∈ free, ∀ y ∈ free,
      publicRows (t.run strategy past).observations x y = true → f x ≤ f y)
    (hpins : ∀ f, S.Valid f → ∀ x, x ∉ free → f x = pin x) :
    S.count ≤ (K + free.card - 1).choose free.card := by
  apply Terminal.card_le_choose_of_fixed_pins S.maps (freeEnumeration π free) pin
  · intro f hf i j hij
    have hv := (mem_maps S f).mp hf
    apply hrespect f hv _ (freeEnumeration_mem π free i) _ (freeEnumeration_mem π free j)
    exact (completed_relation_iff t ht strategy past π hπ _ _).mpr
      (freeEnumeration_ordered π free hij)
  · intro f hf x hx
    apply hpins f ((mem_maps S f).mp hf) x
    simpa only [range_freeEnumeration, Finset.mem_coe] using hx

end SortingAdversary.Optimal.CompletedOrder
