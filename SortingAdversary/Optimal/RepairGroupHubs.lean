import SortingAdversary.Optimal.RepairPricing

/-!
# Complete actual scale-group hub records

Every group output position is the corresponding real chronological block.
Block-index injectivity transfers the proved dictionary multiplicity bound
to the executed group, whose immutable identities survive later repairs.
-/

namespace SortingAdversary.Optimal.RepairPricing

open scoped BigOperators
open WidthRepair StructuralNormalize StableBatches HubSelector BatchWindows

variable {n : ℕ}

theorem scale_block_injective {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) : Function.Injective (trigger.block normal) := by
  intro i j h
  apply Fin.ext
  exact trigger.blocks_nodup.getElem_inj_iff.mp h

/-- The actual reserved scale labels send at most two promotions to one
immutable destination, with the real chronological block vetoes. -/
theorem scale_destination_multiplicity {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) (identity : ℕ) :
    (Finset.univ.filter (fun i : Fin p.J => (scaleEvent trigger normal i).identity = identity)).card ≤ 2 := by
  let indices := Finset.univ.filter (fun i : Fin p.J => (scaleEvent trigger normal i).identity = identity)
  have hc : (indices.image (trigger.block normal)).card = indices.card :=
    Finset.card_image_iff.mpr (fun _ _ _ _ h => scale_block_injective trigger normal h)
  have hsub : indices.image (trigger.block normal) ⊆ trigger.blocks.toFinset.filter (fun block =>
      hubColour (paletteRank s.order) (paletteRank_injective s.order) block = identity) := by
    intro block hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.getElem_mem _), ?_⟩
    exact (Finset.mem_filter.mp hi).2
  exact hc.symm.trans_le ((Finset.card_le_card hsub).trans (trigger.colour_multiplicity identity))

namespace Summary

/-- The actual scale executor emits exactly the reserved index order. -/
theorem fromScale_hubs (p : Parameters) (start : State n) (trigger : ScaleTrigger start p.scale)
    (normal : EarlyNormal start p.scale.width.W₀ p.scale.width.L)
    {s t : State n} {trace : Trace s t} {indices : List (Fin p.scale.J)}
    (events : ScaleEvents start p.scale trigger normal trace indices) :
    ∀ view : ScaleView start s,
      (fromScale p start trigger normal events view).hubs = indices.map (scaleEvent trigger normal) := by
  induction events with
  | nil => intro view; rfl
  | cons i update vertex colour interior palette charge rest events ih =>
    intro view
    change scaleEvent trigger normal i ::
      (fromScale p start trigger normal events (view.advance update interior palette)).hubs = _
    rw [ih]
    rfl

theorem fromScale_hub_count (p : Parameters) (start : State n) (trigger : ScaleTrigger start p.scale)
    (normal : EarlyNormal start p.scale.width.W₀ p.scale.width.L)
    {s t : State n} {trace : Trace s t} {indices : List (Fin p.scale.J)}
    (events : ScaleEvents start p.scale trigger normal trace indices) (view : ScaleView start s) :
    (fromScale p start trigger normal events view).hubs.length = indices.length := by
  rw [fromScale_hubs, List.length_map]

end Summary

end SortingAdversary.Optimal.RepairPricing
