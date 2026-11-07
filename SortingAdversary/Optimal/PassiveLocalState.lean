import SortingAdversary.Optimal.StoredRouting
import SortingAdversary.Optimal.WidthScale

/-!
# Local invariants under passive tree updates

Delegation adds a public comparison between equal-colour pins. A child birth
changes only an isolated unused label and, when necessary, appends one palette
position. Neither operation changes the active graph or its old nonisolated
windows. Consequently a previously normalized child requires no repair.
-/

namespace SortingAdversary.Optimal.PassiveLocalState

open WeakMaps WeakMaps.WeakSystem ControllerRouting Safety PoolState
open WidthRepair GraphBalls NumericalRepresentation FreshAdmission

variable {n K L : ℕ}

theorem windows_of_values (S : WeakSystem (Fin n) (K + 1))
    (T : WeakSystem (Fin n) (L + 1)) (hS : S.Closed) (hT : T.Closed)
    (hs : ∃ f, S.Valid f) (ht : ∃ g, T.Valid g)
    (e : Fin (K + 1) → Fin (L + 1)) (he : Monotone e) (x : Fin n)
    (forward : ∀ f, S.Valid f → ∃ g, T.Valid g ∧ g x = e (f x))
    (backward : ∀ g, T.Valid g → ∃ f, S.Valid f ∧ g x = e (f x)) :
    T.effectiveLower x = e (S.effectiveLower x) ∧
      T.effectiveUpper x = e (S.effectiveUpper x) := by
  have hsw := (S.feasible_iff_windows hS).mp hs
  have htw := (T.feasible_iff_windows hT).mp ht
  obtain ⟨glo, hglo, eglo⟩ := forward _ (S.effectiveLower_valid hS hsw)
  obtain ⟨ghi, hghi, eghi⟩ := forward _ (S.effectiveUpper_valid hS hsw)
  obtain ⟨flo, hflo, eflo⟩ := backward _ (T.effectiveLower_valid hT htw)
  obtain ⟨fhi, hfhi, efhi⟩ := backward _ (T.effectiveUpper_valid hT htw)
  constructor
  · apply le_antisymm
    · exact ((T.valid_between_windows _ hglo x).1).trans_eq eglo
    · rw [eflo]
      exact he (S.valid_between_windows _ hflo x).1
  · apply le_antisymm
    · rw [efhi]
      exact he (S.valid_between_windows _ hfhi x).2
    · exact eghi ▸ (T.valid_between_windows _ hghi x).2

theorem windows_of_same_valid (S T : WeakSystem (Fin n) (K + 1))
    (hS : S.Closed) (hT : T.Closed) (hs : ∃ f, S.Valid f)
    (h : ∀ f, T.Valid f ↔ S.Valid f) (x : Fin n) :
    T.effectiveLower x = S.effectiveLower x ∧ T.effectiveUpper x = S.effectiveUpper x := by
  have ht : ∃ f, T.Valid f := by obtain ⟨f, hf⟩ := hs; exact ⟨f, (h f).mpr hf⟩
  exact windows_of_values S T hS hT hs ht id monotone_id x
    (fun f hf => ⟨f, (h f).mpr hf, rfl⟩) (fun f hf => ⟨f, (h f).mp hf, rfl⟩)

theorem windows_enlarge (p : Pool n) (x : Fin n) :
    p.append.system.effectiveLower x = (p.system.effectiveLower x).castSucc ∧
      p.append.system.effectiveUpper x = (p.system.effectiveUpper x).castSucc := by
  apply windows_of_values p.system p.append.system p.invariant.closed p.append.invariant.closed
    p.invariant.feasible p.append.invariant.feasible Fin.castSucc (fun _ _ h => h) x
  · intro f hf
    exact ⟨paletteEmbedding f, (valid_enlarge_embedding p.system f).mpr hf, rfl⟩
  · intro g hg
    have hm : g ∈ p.system.enlarge.maps := (mem_maps _ _).mpr hg
    rw [maps_enlarge] at hm
    obtain ⟨f, hf, hfg⟩ := Finset.mem_map.mp hm
    exact ⟨f, (mem_maps _ _).mp hf, (congrFun hfg x).symm⟩

theorem windows_admit (p : Pool n) (v : Fin n) (hv : v ∉ p.members)
    (x : Fin n) (hx : x ≠ v) :
    (admit p.system v).effectiveLower x = p.system.effectiveLower x ∧
      (admit p.system v).effectiveUpper x = p.system.effectiveUpper x := by
  let hu := (p.outside v hv).2
  let hi := admission_invariant p.invariant hu p.positive
  apply windows_of_values p.system (admit p.system v) p.invariant.closed hi.closed
    p.invariant.feasible hi.feasible id monotone_id x
  · intro f hf
    exact ⟨Function.update f v 0, admit_update_valid hu hf 0, by simp [hx]⟩
  · intro g hg
    exact ⟨Function.update g v (p.system.lower v), retract_valid hu hg, by simp [hx]⟩

def state (p : Pool n) (d : LocalData p) : State n := ⟨p, d.rows, d.order⟩

theorem data_mpr_active {p q : Pool n} (hp : p = q) (d : LocalData p)
    (he : LocalData q = LocalData p) : (he.mpr d).rows.active = d.rows.active := by
  cases hp
  rfl

theorem admission_active (p : Pool n) (d : LocalData p) (v : Fin n) (hv : v ∉ p.members) :
    (d.admission p v hv).rows.active = d.rows.active := by
  unfold LocalData.admission
  by_cases hcap : p.members.card + 1 ≤ p.palette + 1
  · have hd : ((p.members.card + 1).decLe (p.palette + 1)) = .isTrue hcap := Subsingleton.elim _ _
    simp only [hd]
    have hp : p.admitSized v hv hcap = (p.admission v hv).next := by
      simp only [Pool.admission, dif_pos hcap]
    let data : LocalData (p.admitSized v hv hcap) :=
      ⟨d.rows.admit v (p.system.lower v) (p.outside v hv).2, d.order⟩
    change ((congrArg LocalData hp.symm).mpr data).rows.active = _
    rw [data_mpr_active hp]
    rfl
  · have hd : ((p.members.card + 1).decLe (p.palette + 1)) = .isFalse hcap := Subsingleton.elim _ _
    simp only [hd]
    have hp : p.append.admitSized v (by simpa only [Pool.append_members] using hv)
        (by exact Nat.succ_le_succ p.capacity) = (p.admission v hv).next := by
      simp only [Pool.admission, dif_neg hcap]
    let data : LocalData (p.append.admitSized v
        (by simpa only [Pool.append_members] using hv) (Nat.succ_le_succ p.capacity)) :=
      ⟨d.rows.append.admit v (p.append.system.lower v)
        (p.append.outside v (by simpa only [Pool.append_members] using hv)).2,
        PaletteBirthOrder.extendTop d.order⟩
    change ((congrArg LocalData hp.symm).mpr data).rows.active = _
    rw [data_mpr_active hp]
    funext x y
    change (d.rows.active x y && decide
      (RefinementTransitions.mapPins Fin.castSucc p.pins x = none ∧
        RefinementTransitions.mapPins Fin.castSucc p.pins y = none)) = d.rows.active x y
    by_cases he : d.rows.active x y = true
    · obtain ⟨hx, hy⟩ := d.rows.active_free x y he
      simp [he, RefinementTransitions.mapPins, hx, hy]
    · simp [Bool.eq_false_iff.mpr he]

theorem admission_width (p : Pool n) (d : LocalData p) (v : Fin n) (hv : v ∉ p.members)
    (x : Fin n) (hx : x ≠ v) :
    (state (p.admission v hv).next (d.admission p v hv)).width x = (state p d).width x := by
  have hpa : v ∉ p.append.members := by simpa using hv
  have hplain := windows_admit p v hv x hx
  have happend := windows_admit p.append v hpa x hx
  have hpal := windows_enlarge p x
  change CutNormalization.width (p.admission v hv).next.system x = CutNormalization.width p.system x
  by_cases hcap : p.members.card + 1 ≤ p.palette + 1
  · have hp : p.admitSized v hv hcap = (p.admission v hv).next := by
      simp only [Pool.admission, dif_pos hcap]
    rw [← hp]
    change ((admit p.system v).effectiveUpper x).val + 1 -
        ((admit p.system v).effectiveLower x).val = _
    rw [hplain.1, hplain.2]
    rfl
  · have hp : p.append.admitSized v hpa (Nat.succ_le_succ p.capacity) = (p.admission v hv).next := by
      simp only [Pool.admission, dif_neg hcap]
    rw [← hp]
    change ((admit p.append.system v).effectiveUpper x).val + 1 -
        ((admit p.append.system v).effectiveLower x).val = _
    rw [happend.1, happend.2, hpal.1, hpal.2]
    rfl

theorem connected_nonisolated {E : Fin n → Fin n → Bool} {x y : Fin n}
    (h : Connected E x y) (hne : y ≠ x) : (neighbors E x).Nonempty := by
  by_contra hn
  have he : neighbors E x = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  obtain ⟨r, hr⟩ := h
  rw [IsolatedCoupling.ball_isolated E x
    ((IsolatedCoupling.isolated_iff_neighbors_empty E x).mpr he) r] at hr
  exact hne (Finset.mem_singleton.mp hr)

theorem widthNormal_transfer {s t : State n} {p : ScaleParameters}
    (normal : WidthNormal s p) (active : t.rows.active = s.rows.active)
    (widths : ∀ x, (neighbors s.rows.active x).Nonempty → t.width x = s.width x) :
    WidthNormal t p where
  wide := by
    intro x hx
    rw [active] at hx
    rw [widths x hx]
    exact normal.wide x hx
  edgeScale := by
    intro x y hxy
    rw [active] at hxy
    have hne := s.rows.proper x y (s.rows.active_source x y hxy)
    have hx : (neighbors s.rows.active x).Nonempty := ⟨y, by simp [hne.symm, hxy]⟩
    have hy : (neighbors s.rows.active y).Nonempty := ⟨x, by simp [hne, hxy]⟩
    rw [widths x hx, widths y hy]
    exact normal.edgeScale x y hxy
  component := by
    intro x y hxy
    rw [active] at hxy
    by_cases he : y = x
    · subst y
      simpa using Nat.mul_le_mul_right (t.width x) p.one_le_R
    · have hx := connected_nonisolated hxy he
      have hy : (neighbors s.rows.active y).Nonempty := by
        obtain ⟨r, hr⟩ := hxy
        exact connected_nonisolated ⟨r, ball_symm s.rows.active hr⟩ (Ne.symm he)
      rw [widths x hx, widths y hy]
      exact normal.component x y hxy

/-- The maintained conditions involve the actual graph and actual windows,
with no oracle error bound or counting conclusion among their fields. -/
structure Ready (p : ScaleParameters) (D H : ℕ) (q : Pool n) (d : LocalData q) : Prop where
  widths : WidthNormal (state q d) p
  degree : ∀ x, (neighbors d.rows.active x).card < D
  paths : ∀ xs : List (Fin n), xs.IsChain (fun x y => Arc d.rows.active y x) → xs.length < H

theorem ready_delegation_stable (p : ScaleParameters) (D H : ℕ) :
    StoredRouting.DelegationStable (Ready (n := n) p D H) := by
  intro q d a b ha hb hab hi same normal
  obtain ⟨c, hca, hcb⟩ := same
  have hp : q.pins a ≠ none := by simp [hca]
  have active := d.rows.add_active_pinned_left a b hab hp
  have windows (x : Fin n) := windows_of_same_valid q.system (closedAdd q.system a b)
    q.invariant.closed hi.closed q.invariant.feasible
    (d.rows.delegated_valid q.pin_bounds a b c hca hcb) x
  refine ⟨widthNormal_transfer normal.widths active ?_, ?_, ?_⟩
  · intro x _
    change ((closedAdd q.system a b).effectiveUpper x).val + 1 -
      ((closedAdd q.system a b).effectiveLower x).val = _
    rw [(windows x).1, (windows x).2]
    rfl
  · intro x
    change (neighbors (d.rows.add a b hab).active x).card < D
    rw [active]
    exact normal.degree x
  · intro xs hx
    change xs.IsChain (fun x y => Arc (d.rows.add a b hab).active y x) at hx
    rw [active] at hx
    exact normal.paths xs hx

theorem ready_admission {p : ScaleParameters} {D H : ℕ} (q : Pool n) (d : LocalData q)
    (normal : Ready p D H q d) (v : Fin n) (hv : v ∉ q.members) :
    Ready p D H (q.admission v hv).next (d.admission q v hv) := by
  have active := admission_active q d v hv
  refine ⟨widthNormal_transfer normal.widths active ?_, ?_, ?_⟩
  · intro x hx
    have hxm := q.free_member ((state q d).nonisolated_free hx)
    exact admission_width q d v hv x (fun he => hv (he ▸ hxm))
  · intro x
    rw [active]
    exact normal.degree x
  · intro xs hx
    rw [active] at hx
    exact normal.paths xs hx

end SortingAdversary.Optimal.PassiveLocalState
