import SortingAdversary.Optimal.RepairPricing
import SortingAdversary.Optimal.PassiveLocalState

/-!
# Historical hub persistence through births and delegated comparisons

A new admission may unpin its previously unused dummy label. Old real members
are therefore explicit in the pin-preservation statement. Every emitted hub
already certifies that membership, so all actual historical records survive.
-/

namespace SortingAdversary.Optimal.RepairPricing

open WeakMaps WeakMaps.WeakSystem WidthRepair PoolState ControllerRouting Safety
open StableBatches HubSelector BatchWindows PassiveLocalState

variable {n : ℕ}

theorem data_mpr_rank {p q : Pool n} (hp : p = q) (d : LocalData p)
    (he : LocalData q = LocalData p) :
    paletteRank (he.mpr d).order = paletteRank d.order := by
  cases hp
  rfl

/-- Appending at the top preserves the numerical rank of every old birth. -/
theorem admission_rank (p : Pool n) (d : LocalData p) (v : Fin n) (hv : v ∉ p.members)
    (a : ℕ) (ha : a < p.palette + 1) :
    paletteRank (d.admission p v hv).order a = paletteRank d.order a := by
  unfold LocalData.admission
  by_cases hcap : p.members.card + 1 ≤ p.palette + 1
  · have hd : ((p.members.card + 1).decLe (p.palette + 1)) = .isTrue hcap := Subsingleton.elim _ _
    simp only [hd]
    have hp : p.admitSized v hv hcap = (p.admission v hv).next := by
      simp only [Pool.admission, dif_pos hcap]
    let data : LocalData (p.admitSized v hv hcap) :=
      ⟨d.rows.admit v (p.system.lower v) (p.outside v hv).2, d.order⟩
    change paletteRank ((congrArg LocalData hp.symm).mpr data).order a = _
    rw [data_mpr_rank hp]
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
    change paletteRank ((congrArg LocalData hp.symm).mpr data).order a = _
    rw [data_mpr_rank hp]
    calc
      _ = (PaletteBirthOrder.extendTop d.order (Fin.castSucc ⟨a, ha⟩)).val :=
        paletteRank_apply (PaletteBirthOrder.extendTop d.order) _
      _ = (d.order ⟨a, ha⟩).val := congrArg Fin.val (PaletteBirthOrder.extendTop_old d.order ⟨a, ha⟩)
      _ = _ := (paletteRank_apply d.order ⟨a, ha⟩).symm

theorem admission_order (p : Pool n) (d : LocalData p) (v : Fin n) (hv : v ∉ p.members) :
    OrderExtension (state p d) (state (p.admission v hv).next (d.admission p v hv)) := by
  refine ⟨Nat.succ_le_succ (p.admission v hv).palette_bounds.1, ?_⟩
  intro a b ha hb
  change paletteRank d.order a ≤ paletteRank d.order b ↔
    paletteRank (d.admission p v hv).order a ≤ paletteRank (d.admission p v hv).order b
  rw [admission_rank p d v hv a ha, admission_rank p d v hv b hb]

theorem admission_embed_val (p : Pool n) (v : Fin n) (hv : v ∉ p.members)
    (c : Fin (p.palette + 1)) : ((p.admission v hv).embed c).val = c.val := by
  by_cases hcap : p.members.card + 1 ≤ p.palette + 1
  · have hr : p.admission v hv = _ := dif_pos hcap
    have h := congrArg (fun a : Pool.Admission p v => ∀ c, (a.embed c).val = c.val) hr
    exact (h.mpr (fun _ => rfl)) c
  · have hr : p.admission v hv = _ := dif_neg hcap
    have h := congrArg (fun a : Pool.Admission p v => ∀ c, (a.embed c).val = c.val) hr
    exact (h.mpr (fun _ => rfl)) c

/-- Only old actual members are asserted to retain physical pins. The new
admission's unused dummy pin is intentionally outside this statement. -/
theorem admission_pin_preserved (p : Pool n) (d : LocalData p) (v : Fin n) (hv : v ∉ p.members)
    {x : Fin n} (hx : x ∈ p.members) {identity : ℕ} (h : ImmutablePin (state p d) x identity) :
    ImmutablePin (state (p.admission v hv).next (d.admission p v hv)) x identity := by
  change ∃ c : Fin (p.palette + 1), p.pins x = some c ∧ (d.order.symm c).val = identity at h
  obtain ⟨c, hc, hid⟩ := h
  have hxv : x ≠ v := fun heq => hv (heq ▸ hx)
  refine ⟨(p.admission v hv).embed c, ?_, ?_⟩
  · change (p.admission v hv).next.pins x = _
    rw [(p.admission v hv).pin_old x hxv, hc]
    rfl
  · let old := d.order.symm c
    have hbound : old.val < (p.admission v hv).next.palette + 1 :=
      old.isLt.trans_le (Nat.succ_le_succ (p.admission v hv).palette_bounds.1)
    have heq : (d.admission p v hv).order ⟨old.val, hbound⟩ = (p.admission v hv).embed c := by
      apply Fin.ext
      calc
        _ = paletteRank (d.admission p v hv).order old.val :=
          (paletteRank_apply (d.admission p v hv).order ⟨old.val, hbound⟩).symm
        _ = paletteRank d.order old.val := admission_rank p d v hv old.val old.isLt
        _ = c.val := by rw [paletteRank_apply d.order old]; simp [old]
        _ = _ := (admission_embed_val p v hv c).symm
    change ((d.admission p v hv).order.symm ((p.admission v hv).embed c)).val = identity
    rw [← heq, Equiv.symm_apply_apply]
    exact hid

theorem HubEvent.Fits.admission {event : HubEvent n} (p : Pool n) (d : LocalData p)
    (v : Fin n) (hv : v ∉ p.members) (h : event.Fits (state p d)) :
    event.Fits (state (p.admission v hv).next (d.admission p v hv)) := by
  have ho := admission_order p d v hv
  refine ⟨h.births.trans ho.births, ?_, admission_pin_preserved p d v hv h.member h.pinned, ?_⟩
  · intro a b ha hb
    exact (h.ranks a b ha hb).trans (ho.ranks a b (ha.trans_le h.births) (hb.trans_le h.births))
  · change event.vertex ∈ (p.admission v hv).next.members
    rw [(p.admission v hv).members_eq]
    exact Finset.mem_insert_of_mem h.member

theorem add_order (p : Pool n) (d : LocalData p) (a b : Fin n)
    (ha : a ∈ p.members) (hb : b ∈ p.members) (hab : a ≠ b)
    (hi : Invariant (closedAdd p.system a b) p.pins) :
    OrderExtension (state p d)
      (state (PoolTree.Tree.addComparison p a b ha hb hi) (d.add p a b ha hb hab hi)) :=
  ⟨le_rfl, fun _ _ _ _ => Iff.rfl⟩

theorem add_pin_preserved (p : Pool n) (d : LocalData p) (a b : Fin n)
    (ha : a ∈ p.members) (hb : b ∈ p.members) (hab : a ≠ b)
    (hi : Invariant (closedAdd p.system a b) p.pins)
    {x : Fin n} {identity : ℕ} (h : ImmutablePin (state p d) x identity) :
    ImmutablePin (state (PoolTree.Tree.addComparison p a b ha hb hi) (d.add p a b ha hb hab hi)) x identity := h

theorem HubEvent.Fits.add {event : HubEvent n} (p : Pool n) (d : LocalData p) (a b : Fin n)
    (ha : a ∈ p.members) (hb : b ∈ p.members) (hab : a ≠ b)
    (hi : Invariant (closedAdd p.system a b) p.pins) (h : event.Fits (state p d)) :
    event.Fits (state (PoolTree.Tree.addComparison p a b ha hb hi) (d.add p a b ha hb hab hi)) :=
  ⟨h.births, h.ranks, h.pinned, h.member⟩

end SortingAdversary.Optimal.RepairPricing
