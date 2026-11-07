import Mathlib.Order.Fin.Basic

/-! # Total transport of stored natural colour indices -/

namespace SortingAdversary.Optimal.ColourTransport

/-- Extend a finite palette embedding to a total map on natural indices.
Indices outside the old palette map above the entire new palette. This keeps
stored list keys executable without dependent types in the recursive tree. -/
def extend {K L : ℕ} (e : Fin K → Fin L) (k : ℕ) : ℕ :=
  if h : k < K then (e ⟨k, h⟩).val else L + (k - K)

@[simp] theorem extend_at {K L : ℕ} (e : Fin K → Fin L) (c : Fin K) :
    extend e c.val = (e c).val := by simp [extend, c.isLt]

theorem extend_strictMono {K L : ℕ} (e : Fin K → Fin L) (he : StrictMono e) :
    StrictMono (extend e) := by
  intro a b hab
  by_cases ha : a < K
  · by_cases hb : b < K
    · simp only [extend, dif_pos ha, dif_pos hb]
      exact he (show (⟨a, ha⟩ : Fin K) < ⟨b, hb⟩ from hab)
    · simp only [extend, dif_pos ha, dif_neg hb]
      have h := (e ⟨a, ha⟩).isLt
      omega
  · have hb : ¬ b < K := by omega
    simp only [extend, dif_neg ha, dif_neg hb]
    omega

theorem extend_injective {K L : ℕ} (e : Fin K → Fin L) (he : StrictMono e) :
    Function.Injective (extend e) := (extend_strictMono e he).injective

theorem extend_bound {K L : ℕ} (e : Fin K → Fin L) (k : ℕ) (hk : k < K) :
    extend e k < L := by
  simpa only [extend, dif_pos hk] using (e ⟨k, hk⟩).isLt

end SortingAdversary.Optimal.ColourTransport
