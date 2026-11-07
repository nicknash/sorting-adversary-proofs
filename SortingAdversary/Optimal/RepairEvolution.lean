import SortingAdversary.Optimal.RepairPersistence
import SortingAdversary.Optimal.StoredEvolution

/-!
# Immutable historical records along actual stored-node evolution

The transition relation is generated only by actual repair steps, admissions
and public insertions. All emitted records therefore retain their final
immutable decoder and actual physical pin at the same stored node identity.
-/

namespace SortingAdversary.Optimal.RepairPricing

open WidthRepair PoolState StoredEvolution

variable {n : ℕ}

theorem evolution_members {s t : State n} (history : LocalEvolution s t) :
    s.pool.members ⊆ t.pool.members := by
  induction history with
  | refl => exact Finset.Subset.refl _
  | step operation => rw [operation.members]
  | admission p d v hv =>
    change p.members ⊆ (p.admission v hv).next.members
    rw [(p.admission v hv).members_eq]
    exact Finset.subset_insert _ _
  | comparison => exact Finset.Subset.refl _
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

theorem evolution_order {s t : State n} (history : LocalEvolution s t) : OrderExtension s t := by
  induction history with
  | refl => exact ⟨le_rfl, fun _ _ _ _ => Iff.rfl⟩
  | step operation => exact step_order operation
  | admission p d v hv => exact admission_order p d v hv
  | comparison p d a b ha hb hne hi => exact add_order p d a b ha hb hne hi
  | trans first second ihFirst ihSecond =>
    exact ⟨ihFirst.births.trans ihSecond.births, fun a b ha hb =>
      (ihFirst.ranks a b ha hb).trans
        (ihSecond.ranks a b (ha.trans_le ihFirst.births) (hb.trans_le ihFirst.births))⟩

/-- Member restriction is essential: an admission removes its new label's
unused dummy pin, while preserving every old actual member's pin. -/
theorem evolution_pin {s t : State n} (history : LocalEvolution s t) :
    ∀ v ∈ s.pool.members, ∀ identity, ImmutablePin s v identity → ImmutablePin t v identity := by
  induction history with
  | refl => exact fun _ _ _ h => h
  | step operation => exact fun _ _ _ h => step_pin_preserved operation h
  | admission p d v hv => exact fun _ hx _ h => admission_pin_preserved p d v hv hx h
  | comparison p d a b ha hb hne hi => exact fun _ _ _ h => add_pin_preserved p d a b ha hb hne hi h
  | trans first second ihFirst ihSecond =>
    exact fun v hv identity h => ihSecond v (evolution_members first hv) identity (ihFirst v hv identity h)

theorem HubEvent.Fits.evolution {s t : State n} {event : HubEvent n}
    (h : event.Fits s) (history : LocalEvolution s t) : event.Fits t := by
  have ho := evolution_order history
  exact ⟨h.births.trans ho.births, fun a b ha hb =>
      (h.ranks a b ha hb).trans (ho.ranks a b (ha.trans_le h.births) (hb.trans_le h.births)),
    evolution_pin history event.vertex h.member event.identity h.pinned, evolution_members history h.member⟩

/-- A record attached to a real node occurrence is transported to a real
occurrence of that same immutable identity in the later stored tree. -/
theorem fits_at_later_node {before after : StoredTree n} (history : Evolves before after)
    {identity : ℕ} {s : State n} (occurs : NodeAt before identity s)
    {event : HubEvent n} (h : event.Fits s) :
    ∃ t, NodeAt after identity t ∧ event.Fits t := by
  obtain ⟨t, ht, hlocal⟩ := history identity s occurs
  exact ⟨t, ht, h.evolution hlocal⟩

end SortingAdversary.Optimal.RepairPricing
