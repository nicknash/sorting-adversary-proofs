import SortingAdversary.Optimal.SystematicCoupling

/-!
# Stationarity of the constructed finite-clock sweeps

The proof separates the unused coordinate of the common clock vector. Thus
stationarity holds for the actual deterministic sweep function applied to
uniform independent clocks, not just for an abstract transition kernel.
-/

namespace SortingAdversary.Optimal.ClockStationarity

open WeakMaps LocalCoupling ClockContraction FiniteProbability SystematicCoupling
open scoped BigOperators

variable {n K Q : ℕ}

/-- The explicit conditional interval always fits in the palette. -/
theorem conditionalWidth_le_palette (S : WeakSystem (Fin n) (K + 1))
    (v : Fin n) (f : ColorMap (Fin n) (K + 1)) : conditionalWidth S v f ≤ K + 1 := by
  unfold conditionalWidth
  have := (conditionalUpper S v f).isLt
  omega

/-- A factorial clock alphabet is divisible by every possible nonempty
conditional interval. This very large alphabet is used only by the proof. -/
theorem conditionalWidth_dvd_factorial (S : WeakSystem (Fin n) (K + 1))
    (v : Fin n) (f : State S) : conditionalWidth S v f.val ∣ (K + 1).factorial :=
  Nat.dvd_factorial (conditionalWidth_pos S v f.val f.property) (conditionalWidth_le_palette S v f.val)

/-- Sum over feasible subtypes equals the enumerated weak-map sum. -/
theorem sum_states (S : WeakSystem (Fin n) (K + 1)) (φ : ColorMap (Fin n) (K + 1) → ℚ) :
    (∑ z : State S, φ z.val) = ∑ f ∈ S.maps, φ f :=
  (Finset.sum_subtype S.maps (fun _ => S.mem_maps _) φ).symm

theorem card_states (S : WeakSystem (Fin n) (K + 1)) : Fintype.card (State S) = S.count := by
  rw [Fintype.card_subtype]
  rfl

/-- Exact stationarity of a single refresh for the uniform feasible subtype. -/
theorem mean_refresh_states (S : WeakSystem (Fin n) (K + 1)) (v : Fin n)
    (φ : ColorMap (Fin n) (K + 1) → ℚ) :
    mean (fun z : State S => refreshObservable S v φ z.val) = mean (fun z : State S => φ z.val) := by
  unfold mean
  rw [sum_states, sum_states, refresh_preserves_uniform_sum]

/-- Before time `t`, only the first `t` coordinates of the clock vector can
have affected the constructed state. -/
theorem after_eq_of_prefix (S : WeakSystem (Fin n) (K + 1))
    (r q : Fin n → Fin Q) (z : State S) (t : ℕ)
    (hprefix : ∀ v, v.val < t → r v = q v) : after S r z t = after S q z t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hold := ih (fun v hv => hprefix v (by omega))
    simp only [after]
    split_ifs with ht
    · rw [hold]
      apply Subtype.ext
      unfold SystematicCoupling.update
      simp only [hprefix ⟨t, ht⟩ (by simp)]
    · exact hold

/-- Changing an unused clock has no effect on the partial sweep. -/
theorem after_eq_change_unused (S : WeakSystem (Fin n) (K + 1))
    (r : Fin n → Fin Q) (z : State S) (t : ℕ) (v : Fin n) (c : Fin Q)
    (ht : t ≤ v.val) : after S (Function.update r v c) z t = after S r z t := by
  apply after_eq_of_prefix
  intro x hx
  exact Function.update_of_ne (show x ≠ v by intro h; subst x; omega) _ _

section Fresh
variable [NeZero Q]

/-- Fresh-coordinate averaging for any state-valued function which does not
use that coordinate. The independence condition is later proved for `after`. -/
theorem mean_update_fresh (S : WeakSystem (Fin n) (K + 1)) (v : Fin n)
    (F : (Fin n → Fin Q) → State S)
    (hF : ∀ r c, F (Function.update r v c) = F r)
    (hdiv : ∀ f : State S, conditionalWidth S v f.val ∣ Q)
    (φ : ColorMap (Fin n) (K + 1) → ℚ) :
    mean (fun r => φ (update S r v (F r)).val) =
      mean (fun r => refreshObservable S v φ (F r).val) := by
  let e := Equiv.funSplitAt v (Fin Q)
  let F₀ : ({ x : Fin n // x ≠ v } → Fin Q) → State S := fun q => F (e.symm (0, q))
  have heq (c : Fin Q) (q : { x : Fin n // x ≠ v } → Fin Q) :
      e.symm (c, q) = Function.update (e.symm (0, q)) v c := by
    funext x
    by_cases hx : x = v
    · subst x
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt_symm_apply]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt_symm_apply, hx]
  have hconst (c : Fin Q) (q : { x : Fin n // x ≠ v } → Fin Q) : F (e.symm (c, q)) = F₀ q := by
    rw [heq]
    exact hF _ _
  let L : (Fin n → Fin Q) → ℚ := fun r => φ (update S r v (F r)).val
  let R : (Fin n → Fin Q) → ℚ := fun r => refreshObservable S v φ (F r).val
  change mean L = mean R
  rw [← mean_equiv e.symm L, ← mean_equiv e.symm R, mean_product, mean_product]
  rw [mean_comm, mean_comm (fun c q => R (e.symm (c, q)))]
  apply mean_congr
  intro q
  have hL : (fun c : Fin Q => L (e.symm (c, q))) =
      fun c : Fin Q => φ (Function.update (F₀ q).val v
        (refreshColor S v (F₀ q).val (F₀ q).property (gridClock c) (gridClock_mem c))) := by
    funext c
    unfold L update
    rw [hconst]
    simp [e, Equiv.funSplitAt, Equiv.piSplitAt_symm_apply]
  rw [hL]
  have hkernel := refresh_grid_eq_kernel S v (F₀ q).val (F₀ q).property
    (NeZero.pos Q) (hdiv (F₀ q)) φ
  change mean _ = mean _
  calc
    _ = refreshObservable S v φ (F₀ q).val := by
      simpa only [mean, Fintype.card_fin] using hkernel
    _ = mean (fun _c : Fin Q => refreshObservable S v φ (F₀ q).val) := (mean_const _).symm
    _ = _ := mean_congr (fun c => by unfold R; rw [hconst])


/-- An initial sample has the uniform feasible marginal. This is an equality of
finite expectations, and is verified directly for the independent initial pair. -/
def UniformLaw {Ω : Type*} [Fintype Ω] (S : WeakSystem (Fin n) (K + 1))
    (f : Ω → State S) : Prop :=
  ∀ φ : ColorMap (Fin n) (K + 1) → ℚ,
    mean (fun ω => φ (f ω).val) = mean (fun z : State S => φ z.val)

/-- Every prefix of the actual fresh-clock sweep preserves the uniform law. -/
theorem after_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (S : WeakSystem (Fin n) (K + 1)) (f : Ω → State S) (hf : UniformLaw S f)
    (hdiv : ∀ v (z : State S), conditionalWidth S v z.val ∣ Q) (t : ℕ)
    (φ : ColorMap (Fin n) (K + 1) → ℚ) :
    mean (fun p : Ω × (Fin n → Fin Q) => φ (after S p.2 (f p.1) t).val) =
      mean (fun z : State S => φ z.val) := by
  rw [mean_product]
  induction t generalizing φ with
  | zero => simpa only [after, mean_const] using hf φ
  | succ t ih =>
    by_cases ht : t < n
    · let v : Fin n := ⟨t, ht⟩
      calc
        _ = mean (fun ω => mean (fun r : Fin n → Fin Q =>
            refreshObservable S v φ (after S r (f ω) t).val)) := by
          apply mean_congr
          intro ω
          simpa only [after, dif_pos ht] using
            mean_update_fresh S v (fun r => after S r (f ω) t)
              (fun r c => after_eq_change_unused S r (f ω) t v c (Nat.le_refl t))
              (hdiv v) φ
        _ = mean (fun z : State S => refreshObservable S v φ z.val) := ih _
        _ = mean (fun z : State S => φ z.val) := mean_refresh_states S v φ
    · simpa only [after, dif_neg ht] using ih φ

/-- The constructed sweep, including its finite shared clock vector, has the
uniform weak-map marginal whenever its initial state does. -/
theorem sweep_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (S : WeakSystem (Fin n) (K + 1)) (f : Ω → State S) (hf : UniformLaw S f)
    (hdiv : ∀ v (z : State S), conditionalWidth S v z.val ∣ Q) :
    UniformLaw S (fun p : Ω × (Fin n → Fin Q) => sweep S p.2 (f p.1)) :=
  fun φ => after_uniform S f hf hdiv n φ

end Fresh

end SortingAdversary.Optimal.ClockStationarity
