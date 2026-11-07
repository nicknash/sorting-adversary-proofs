import SortingAdversary.Optimal.RepairEvolution
import SortingAdversary.Optimal.RepairDestinations
import SortingAdversary.Optimal.ReservationAnnotations

/-!
# Completed reservation groups at actual stored nodes

A group is attached to a real immutable node occurrence. All its members are
physical pins, and the multiplicity bound uses their actual destinations.
Later repairs, admissions and public comparisons preserve this property.
-/

namespace SortingAdversary.Optimal.ReservationFits

open WidthRepair PoolState RepairPricing StoredEvolution LedgerTreeBridge

variable {n : ℕ}

structure Local (s : State n) (members : Finset (Fin n)) (cap : ℕ) : Prop where
  fixed : members ⊆ s.pool.fixed
  multiplicity : ∀ identity,
    (members.filter (fun v => destination s v = some identity)).card ≤ cap

theorem destination_physical (s : State n) (v : Fin n) (c : Fin (s.pool.palette + 1)) :
    destination s v = some (s.order.symm c).val ↔ s.pool.pins v = some c := by
  cases hp : s.pool.pins v with
  | none => simp [destination, hp]
  | some d =>
    simp only [destination, hp, Option.map_some, Option.some.injEq]
    constructor
    · intro h
      exact s.order.symm.injective (Fin.ext h)
    · rintro rfl
      rfl

theorem Local.physical {s : State n} {members : Finset (Fin n)} {cap : ℕ}
    (h : Local s members cap) (c : Fin (s.pool.palette + 1)) :
    (members.filter (fun v => s.pool.pins v = some c)).card ≤ cap := by
  simpa only [destination_physical] using h.multiplicity (s.order.symm c).val

theorem fixed_destination_preserved {s t : State n} (history : LocalEvolution s t)
    {v : Fin n} (hv : v ∈ s.pool.fixed) : destination t v = destination s v := by
  obtain ⟨hvm, hp⟩ := Finset.mem_filter.mp hv
  cases hc : s.pool.pins v with
  | none => exact False.elim (hp hc)
  | some c =>
    have h := evolution_pin history v hvm (s.order.symm c).val ⟨c, hc, rfl⟩
    simpa only [destination, hc, Option.map_some] using destination_iff.mpr h

theorem Local.evolution {s t : State n} {members : Finset (Fin n)} {cap : ℕ}
    (h : Local s members cap) (history : LocalEvolution s t) : Local t members cap := by
  refine ⟨?_, ?_⟩
  · intro v hv
    have hf := h.fixed hv
    have hvm := (Finset.mem_filter.mp hf).1
    refine Finset.mem_filter.mpr ⟨evolution_members history hvm, ?_⟩
    intro hn
    have he := fixed_destination_preserved history hf
    rw [destination, hn, Option.map_none] at he
    have hold : s.pool.pins v = none := Option.map_eq_none_iff.mp he.symm
    exact (Finset.mem_filter.mp hf).2 hold
  · intro identity
    have he : members.filter (fun v => destination t v = some identity) =
        members.filter (fun v => destination s v = some identity) := by
      apply Finset.filter_congr
      intro v hv
      rw [fixed_destination_preserved history (h.fixed hv)]
    rw [he]
    exact h.multiplicity identity

def Fits (tree : StoredTree n) (group : Finset (IncidenceLedger.Location n)) (cap : ℕ) : Prop :=
  ∃ identity state members, NodeAt tree identity state ∧
    group = nodeLocations identity members ∧ Local state members cap

theorem Fits.evolution {before after : StoredTree n}
    {group : Finset (IncidenceLedger.Location n)} {cap : ℕ}
    (h : Fits before group cap) (history : Evolves before after) : Fits after group cap := by
  obtain ⟨identity, state, members, occurs, heq, hlocal⟩ := h
  obtain ⟨next, hn, evolution⟩ := history identity state occurs
  exact ⟨identity, next, members, hn, heq, hlocal.evolution evolution⟩

/-- This is the final-tree property used by the entropy telescope: every
destination is read from the physical pin in the actual stored pool. -/
theorem Fits.physical {tree : StoredTree n}
    {group : Finset (IncidenceLedger.Location n)} {cap : ℕ} (h : Fits tree group cap) :
    ∃ identity state members, NodeAt tree identity state ∧
      group = nodeLocations identity members ∧ members ⊆ state.pool.fixed ∧
      ∀ c, (members.filter (fun v => state.pool.pins v = some c)).card ≤ cap := by
  obtain ⟨identity, state, members, hn, he, hl⟩ := h
  exact ⟨identity, state, members, hn, he, hl.fixed, hl.physical⟩

theorem of_completed {s : State n} (members : Finset (Fin n)) (cap : ℕ)
    (hm : members ⊆ s.pool.members) (hdone : ∀ v ∈ members, v ∉ s.pool.free)
    (hcap : ∀ identity, (members.filter (fun v => destination s v = some identity)).card ≤ cap) :
    Local s members cap := by
  refine ⟨?_, hcap⟩
  intro v hv
  exact Finset.mem_filter.mpr ⟨hm hv, fun hn => hdone v hv ((s.pool.free_iff v).mpr hn)⟩

end SortingAdversary.Optimal.ReservationFits
