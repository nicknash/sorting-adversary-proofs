import SortingAdversary.Optimal.HubSelector
import Mathlib.Order.Interval.Finset.Fin

/-!
# Actual palette windows for the executable hub selector

The bounds supplied to `HubSelector` are computed here from the sorted members
of the actual stable batches. A threshold is represented by the number of
batch colours below it. Monotonicity of the sorted palette ranks proves that
these counts are exactly the endpoints of a contiguous interval of positions.

The batch partition then proves that the sum of these interval lengths is
the number of colours in the global palette window. Thus the selector's
quantitative guarantee is instantiated from a real palette permutation.
-/

namespace SortingAdversary.Optimal.BatchWindows

open scoped BigOperators
open StableBatches HubSelector

/-- The actual colour at a sorted position of an immutable batch. -/
def colourAt (rank : ℕ → ℕ) (hinj : Function.Injective rank) (b : Batch) (i : Fin b.size) : ℕ :=
  (orderedMembers rank hinj b).get ⟨i.val, by rw [orderedMembers_length]; exact i.isLt⟩

def rankAt (rank : ℕ → ℕ) (hinj : Function.Injective rank) (b : Batch) : Fin b.size → ℕ :=
  fun i => rank (colourAt rank hinj b i)

theorem colourAt_mem (rank : ℕ → ℕ) (hinj : Function.Injective rank) (b : Batch)
    (i : Fin b.size) : colourAt rank hinj b i ∈ b.members := by
  rw [← mem_orderedMembers rank hinj b]
  exact List.get_mem _ _

theorem colourAt_injective (rank : ℕ → ℕ) (hinj : Function.Injective rank) (b : Batch) :
    Function.Injective (colourAt rank hinj b) := by
  intro i j heq
  have h := (orderedMembers_nodup rank hinj b).injective_get heq
  exact Fin.ext (congrArg (@Fin.val (orderedMembers rank hinj b).length) h)

theorem colourAt_surjective (rank : ℕ → ℕ) (hinj : Function.Injective rank) (b : Batch)
    {colour : ℕ} (hcolour : colour ∈ b.members) :
    ∃ i : Fin b.size, colourAt rank hinj b i = colour := by
  have hm := (mem_orderedMembers rank hinj b colour).mpr hcolour
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
  refine ⟨⟨i.val, by simpa using i.isLt⟩, ?_⟩
  exact hi

theorem rankAt_monotone (rank : ℕ → ℕ) (hinj : Function.Injective rank) (b : Batch) :
    Monotone (rankAt rank hinj b) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hij | rfl
  · exact (orderedMembers_pairwise rank hinj b).rel_get_of_lt hij
  · exact le_rfl

/-- An executable lower-bound search, expressed as a finite count. -/
def countBelow {N : ℕ} (f : Fin N → ℕ) (threshold : ℕ) : ℕ :=
  (Finset.univ.filter fun i => f i < threshold).card

theorem countBelow_le {N : ℕ} (f : Fin N → ℕ) (threshold : ℕ) : countBelow f threshold ≤ N := by
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem countBelow_mono {N : ℕ} (f : Fin N → ℕ) {lower upper : ℕ} (h : lower ≤ upper) :
    countBelow f lower ≤ countBelow f upper := by
  apply Finset.card_le_card
  intro i hi
  have hi' := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hi'.1, hi'.2.trans_le h⟩

/-- For a monotone array the counted prefix is exactly an initial interval
of its positions; ties would be harmless for this lemma. -/
theorem index_lt_countBelow_iff {N : ℕ} (f : Fin N → ℕ) (hmono : Monotone f)
    (threshold : ℕ) (i : Fin N) : i.val < countBelow f threshold ↔ f i < threshold := by
  constructor
  · intro hi
    by_contra hfi
    have hsubset : (Finset.univ.filter (fun j => f j < threshold)) ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra hji
      have hij : i ≤ j := le_of_not_gt hji
      have hmon := hmono hij
      have hj' := (Finset.mem_filter.mp hj).2
      omega
    have hcard := Finset.card_le_card hsubset
    rw [Fin.card_Iio] at hcard
    exact Nat.not_lt_of_ge hcard hi
  · intro hfi
    have hsubset : Finset.Iic i ⊆ Finset.univ.filter (fun j => f j < threshold) := by
      intro j hj
      have hji := Finset.mem_Iic.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmono hji).trans_lt hfi⟩
    have hcard := Finset.card_le_card hsubset
    rw [Fin.card_Iic] at hcard
    exact hcard

theorem index_window_iff {N : ℕ} (f : Fin N → ℕ) (hmono : Monotone f)
    (lower upper : ℕ) (i : Fin N) :
    countBelow f lower ≤ i.val ∧ i.val < countBelow f upper ↔ lower ≤ f i ∧ f i < upper := by
  have hl := index_lt_countBelow_iff f hmono lower i
  have hu := index_lt_countBelow_iff f hmono upper i
  omega

/-- Endpoints in each sorted batch for one global palette threshold. -/
def batchThreshold (rank : ℕ → ℕ) (hinj : Function.Injective rank) (threshold : ℕ) (b : Batch) : ℕ :=
  countBelow (rankAt rank hinj b) threshold

theorem batchThreshold_le (rank : ℕ → ℕ) (hinj : Function.Injective rank) (threshold : ℕ) (b : Batch) :
    batchThreshold rank hinj threshold b ≤ b.size := countBelow_le _ _

theorem batchThreshold_mono (rank : ℕ → ℕ) (hinj : Function.Injective rank)
    {lower upper : ℕ} (h : lower ≤ upper) (b : Batch) :
    batchThreshold rank hinj lower b ≤ batchThreshold rank hinj upper b := countBelow_mono _ h

theorem batch_window_spec (rank : ℕ → ℕ) (hinj : Function.Injective rank)
    (lower upper : ℕ) (b : Batch) (i : Fin b.size) :
    batchThreshold rank hinj lower b ≤ i.val ∧ i.val < batchThreshold rank hinj upper b ↔
      lower ≤ rank (colourAt rank hinj b i) ∧ rank (colourAt rank hinj b i) < upper :=
  index_window_iff _ (rankAt_monotone rank hinj b) lower upper i

theorem batch_window_card (rank : ℕ → ℕ) (hinj : Function.Injective rank)
    (lower upper : ℕ) (b : Batch) :
    (b.members.filter (fun colour => lower ≤ rank colour ∧ rank colour < upper)).card =
      batchThreshold rank hinj upper b - batchThreshold rank hinj lower b := by
  let indices := (Finset.univ : Finset (Fin b.size)).filter
    (fun i => lower ≤ rankAt rank hinj b i ∧ rankAt rank hinj b i < upper)
  have hpositions : indices.image Fin.val =
      Finset.Ico (batchThreshold rank hinj lower b) (batchThreshold rank hinj upper b) := by
    ext j
    constructor
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_Ico.mpr ((batch_window_spec rank hinj lower upper b i).mpr
        (Finset.mem_filter.mp hi).2)
    · intro hj
      have hj' := Finset.mem_Ico.mp hj
      let i : Fin b.size := ⟨j, hj'.2.trans_le (batchThreshold_le rank hinj upper b)⟩
      refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (batch_window_spec rank hinj lower upper b i).mp hj'⟩
  have hcolours : indices.image (colourAt rank hinj b) =
      b.members.filter (fun colour => lower ≤ rank colour ∧ rank colour < upper) := by
    ext colour
    constructor
    · intro hc
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
      exact Finset.mem_filter.mpr ⟨colourAt_mem rank hinj b i, (Finset.mem_filter.mp hi).2⟩
    · intro hc
      have hc' := Finset.mem_filter.mp hc
      obtain ⟨i, rfl⟩ := colourAt_surjective rank hinj b hc'.1
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc'.2⟩, rfl⟩
  calc
    _ = (indices.image (colourAt rank hinj b)).card := congrArg Finset.card hcolours.symm
    _ = indices.card := Finset.card_image_of_injective _ (colourAt_injective rank hinj b)
    _ = (indices.image Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ = _ := by rw [hpositions, Nat.card_Ico]

/-- The computed batch lengths account for the actual global window, since
the stable batches partition all birth identities. -/
theorem global_window_count (births : ℕ) (rank : ℕ → ℕ) (hinj : Function.Injective rank)
    (lower upper : ℕ) :
    windowCount births (batchThreshold rank hinj lower) (batchThreshold rank hinj upper) =
      ((Finset.range births).filter (fun colour => lower ≤ rank colour ∧ rank colour < upper)).card := by
  let window := fun b : Batch => b.members.filter (fun colour => lower ≤ rank colour ∧ rank colour < upper)
  have hdisjoint : (↑(batches births) : Set Batch).PairwiseDisjoint window := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro colour hcolourb hcolourc
    have heq := currentBatches_unique ((mem_batches _ _).mp hb) ((mem_batches _ _).mp hc)
      (Finset.mem_filter.mp hcolourb).1 (Finset.mem_filter.mp hcolourc).1
    exact hbc heq
  have hunion : (batches births).biUnion window =
      (Finset.range births).filter (fun colour => lower ≤ rank colour ∧ rank colour < upper) := by
    ext colour
    constructor
    · intro hcolour
      obtain ⟨b, hb, hcolour⟩ := Finset.mem_biUnion.mp hcolour
      have hc := Finset.mem_filter.mp hcolour
      refine Finset.mem_filter.mpr ⟨?_, hc.2⟩
      exact Finset.mem_range.mpr ((currentBatches_cover births colour).mp
        ⟨b, (mem_batches _ _).mp hb, hc.1⟩)
    · intro hcolour
      have hc := Finset.mem_filter.mp hcolour
      obtain ⟨b, hb, hcolour⟩ := (currentBatches_cover births colour).mpr (Finset.mem_range.mp hc.1)
      exact Finset.mem_biUnion.mpr ⟨b, (mem_batches _ _).mpr hb,
        Finset.mem_filter.mpr ⟨hcolour, hc.2⟩⟩
  unfold windowCount
  calc
    _ = ∑ b ∈ batches births, (window b).card := by
      apply Finset.sum_congr rfl
      intro b hb
      exact (batch_window_card rank hinj lower upper b).symm
    _ = ((batches births).biUnion window).card := (Finset.card_biUnion hdisjoint).symm
    _ = _ := congrArg Finset.card hunion

/-! ## Concrete palette permutations -/

/-- Extend a finite palette permutation to all natural birth identities by
the identity outside the currently born prefix. The extension is injective,
so it can be passed directly to the executable batch sort. -/
def paletteRank {births : ℕ} (order : Equiv.Perm (Fin births)) (colour : ℕ) : ℕ :=
  if h : colour < births then (order ⟨colour, h⟩).val else colour

@[simp] theorem paletteRank_apply {births : ℕ} (order : Equiv.Perm (Fin births)) (colour : Fin births) :
    paletteRank order colour.val = (order colour).val := by simp [paletteRank, colour.isLt]

theorem paletteRank_injective {births : ℕ} (order : Equiv.Perm (Fin births)) :
    Function.Injective (paletteRank order) := by
  intro a b heq
  by_cases ha : a < births <;> by_cases hb : b < births
  · simp only [paletteRank, dif_pos ha, dif_pos hb] at heq
    exact congrArg Fin.val (order.injective (Fin.ext heq))
  · simp only [paletteRank, dif_pos ha, dif_neg hb] at heq
    have h := (order ⟨a, ha⟩).isLt
    omega
  · simp only [paletteRank, dif_neg ha, dif_pos hb] at heq
    have h := (order ⟨b, hb⟩).isLt
    omega
  · simpa only [paletteRank, dif_neg ha, dif_neg hb] using heq

theorem palette_window_card {births : ℕ} (order : Equiv.Perm (Fin births)) (lower upper : ℕ)
    (hupper : upper ≤ births) :
    ((Finset.range births).filter (fun colour =>
      lower ≤ paletteRank order colour ∧ paletteRank order colour < upper)).card = upper - lower := by
  let s := (Finset.range births).filter (fun colour =>
    lower ≤ paletteRank order colour ∧ paletteRank order colour < upper)
  have himage : s.image (paletteRank order) = Finset.Ico lower upper := by
    ext rank
    constructor
    · intro hrank
      obtain ⟨colour, hcolour, rfl⟩ := Finset.mem_image.mp hrank
      exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hcolour).2
    · intro hrank
      have hrank' := Finset.mem_Ico.mp hrank
      let r : Fin births := ⟨rank, hrank'.2.trans_le hupper⟩
      let colour := order.symm r
      have hcol : paletteRank order colour.val = rank := by simp [colour, r]
      refine Finset.mem_image.mpr ⟨colour.val, ?_, hcol⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr colour.isLt, by simpa [hcol] using hrank'⟩
  calc
    _ = (s.image (paletteRank order)).card :=
      (Finset.card_image_of_injective s (paletteRank_injective order)).symm
    _ = upper - lower := by rw [himage, Nat.card_Ico]

theorem palette_batch_window_count {births : ℕ} (order : Equiv.Perm (Fin births))
    (lower upper : ℕ) (hupper : upper ≤ births) :
    windowCount births
      (batchThreshold (paletteRank order) (paletteRank_injective order) lower)
      (batchThreshold (paletteRank order) (paletteRank_injective order) upper) = upper - lower := by
  rw [global_window_count, palette_window_card order lower upper hupper]

/-- The complete executable selector from a finite palette order and a
global half-open interval of current ranks. -/
def selectWindow {births : ℕ} (order : Equiv.Perm (Fin births)) (lower upper : ℕ)
    (veto : Finset Block) : Option Block :=
  selectBlock births
    (batchThreshold (paletteRank order) (paletteRank_injective order) lower)
    (batchThreshold (paletteRank order) (paletteRank_injective order) upper) veto

theorem selected_hub_in_window {births lower upper : ℕ} (order : Equiv.Perm (Fin births))
    {veto : Finset Block} {chosen : Block} (hchosen : selectWindow order lower upper veto = some chosen) :
    lower ≤ paletteRank order (hubColour (paletteRank order) (paletteRank_injective order) chosen) ∧
      paletteRank order (hubColour (paletteRank order) (paletteRank_injective order) chosen) < upper := by
  have hspec := selected_spec hchosen
  have hfits := ((mem_allBlocks _ _).mp hspec.1).2
  let i : Fin chosen.batch.size :=
    ⟨chosen.hubIndex, chosen.hubIndex_bounds.2.trans_le (Block.stop_le_batch_size hfits)⟩
  have hposition :
      batchThreshold (paletteRank order) (paletteRank_injective order) lower chosen.batch ≤ i.val ∧
      i.val < batchThreshold (paletteRank order) (paletteRank_injective order) upper chosen.batch :=
    ⟨hspec.2.1.1.trans chosen.hubIndex_bounds.1, chosen.hubIndex_bounds.2.trans_le hspec.2.1.2⟩
  have hresult := (batch_window_spec (paletteRank order) (paletteRank_injective order)
    lower upper chosen.batch i).mp hposition
  have hcolour : hubColour (paletteRank order) (paletteRank_injective order) chosen =
      colourAt (paletteRank order) (paletteRank_injective order) chosen.batch i := by
    unfold hubColour colourAt
    exact List.getD_eq_get _ _ ⟨chosen.hubIndex,
      hubIndex_lt_length (paletteRank order) (paletteRank_injective order) hfits⟩
  rwa [← hcolour] at hresult

theorem selectWindow_exists {births lower upper : ℕ} (order : Equiv.Perm (Fin births))
    (veto : Finset Block) (hupper : upper ≤ births) (hroom : vetoCost veto < upper - lower) :
    ∃ chosen, selectWindow order lower upper veto = some chosen := by
  apply selectBlock_exists
  · intro b hb
    exact batchThreshold_le _ _ _ _
  · rwa [palette_batch_window_count order lower upper hupper]

/-- The quantitative bound is now applied to the actual global palette
window, with no externally supplied batch-window or dictionary assumptions. -/
theorem selected_palette_window_bound {births M lower upper : ℕ}
    (order : Equiv.Perm (Fin births)) {veto : Finset Block} {chosen : Block}
    (hcap : births ≤ 2 ^ M) (hlower : lower ≤ upper) (hupper : upper ≤ births)
    (hchosen : selectWindow order lower upper veto = some chosen) :
    upper - lower ≤ 4 * chosen.size * (M - chosen.level + 1) + vetoCost veto := by
  have h := selected_window_bound hcap hchosen
    (fun b hb => batchThreshold_mono _ _ hlower b)
    (fun b hb => batchThreshold_le _ _ _ b)
  rwa [palette_batch_window_count order lower upper hupper] at h

theorem selected_trimmed_window_bound {births M lower upper : ℕ}
    (order : Equiv.Perm (Fin births)) {veto : Finset Block} {chosen : Block}
    (hcap : births ≤ 2 ^ M) (hupper : upper ≤ births) (hlarge : 8 ≤ upper - lower)
    (hveto : 4 * vetoCost veto ≤ upper - lower)
    (hchosen : selectWindow order (lower + 1) (upper - 1) veto = some chosen) :
    upper - lower ≤ 8 * chosen.size * (M - chosen.level + 2) := by
  apply selected_raw_window_bound hcap hchosen
    (fun b hb => batchThreshold_mono _ _ (by omega : lower + 1 ≤ upper - 1) b)
    (fun b hb => batchThreshold_le _ _ _ b)
    _ hlarge hveto
  rw [palette_batch_window_count order (lower + 1) (upper - 1) (by omega)]
  omega

end SortingAdversary.Optimal.BatchWindows
