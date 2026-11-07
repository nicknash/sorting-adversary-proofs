import SortingAdversary.Optimal.WidthRepair

/-!
# Uniqueness of the metadata retained by primitive updates

The chronological permutation is determined by its old identities: a
promotion introduces at most one new identity. These equalities let a
measured implementation construct the concrete updated getters directly,
while the existing proof-carrying trace retains exactly the same state.
-/

namespace SortingAdversary.Optimal.RepresentationWork

open WidthRepair NumericalRepresentation

theorem permutation_eq_of_prefix {K L : ℕ} (hKL : K ≤ L) (hLK : L ≤ K + 1)
    (f g : Equiv.Perm (Fin L))
    (h : ∀ x : Fin K, f (Fin.castLE hKL x) = g (Fin.castLE hKL x)) : f = g := by
  have old : ∀ x : Fin L, x.val < K → f x = g x := by
    intro x hx
    exact h ⟨x.val, hx⟩
  apply Equiv.ext
  intro x
  by_cases hx : x.val < K
  · exact old x hx
  · let y := f.symm (g x)
    have hy : y = x := by
      by_cases hyK : y.val < K
      · apply g.injective
        exact (old y hyK).symm.trans (f.apply_symm_apply (g x))
      · apply Fin.ext
        have hxl := x.isLt
        have hyl := y.isLt
        omega
    have he := congrArg f hy
    simpa only [y, Equiv.apply_symm_apply] using he.symm

theorem sourcePartition_ext {n K : ℕ} {S : WeakMaps.WeakSystem (Fin n) (K + 1)}
    {pins : Fin n → Option (Fin (K + 1))} {a b : SourcePartition S pins}
    (hs : a.source = b.source) (ha : a.active = b.active) : a = b := by
  cases a
  cases b
  cases hs
  cases ha
  rfl

theorem promotionData_unique {n : ℕ} {s : State n} {v : Fin n}
    {c : Fin (s.pool.palette + 1)} {r : Promotion.Result s.pool.system s.pool.pins v c}
    (a b : State.PromotionData s v c r) : a = b := by
  have hr : a.rows = b.rows := sourcePartition_ext
    (a.source_eq.trans b.source_eq.symm) (a.active_eq.trans b.active_eq.symm)
  have ho : a.order = b.order := permutation_eq_of_prefix
    (Nat.succ_le_succ r.palette_bounds.1) (Nat.succ_le_succ r.palette_bounds.2) a.order b.order
    (fun i => (a.order_old i).trans (b.order_old i).symm)
  cases a
  cases b
  cases hr
  cases ho
  rfl

theorem pinUpdate_next_eq_promote {n : ℕ} {s : State n} (update : PinUpdate s) :
    update.next = s.promote update.vertex update.free update.colour update.supported := by
  cases update with
  | mk v hv c hc hm r actual data charge retained =>
    cases actual
    have hd := promotionData_unique data (s.promotionData v hv c hc)
    cases hd
    rfl

end SortingAdversary.Optimal.RepresentationWork
