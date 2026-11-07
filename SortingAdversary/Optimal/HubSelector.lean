import SortingAdversary.Optimal.StableBatches
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.GetD

/-!
# Executable selection of dyadic hubs

`selectBlock` enumerates the aligned blocks of the actual current immutable
batches, discards blocks outside the supplied batch windows or already vetoed,
and picks one of largest size with deterministic list-order ties.

The veto is represented by earlier block records. Within the unchanged
current batches this is equivalent to vetoing a previously used hub of the
same singleton/nonsingleton kind. Different kinds may use a colour once each.

For the length estimate it suffices to consider aligned blocks of size twice
the selected size. Every such contained block must be vetoed, and these blocks
cover each batch window apart from fewer than two block lengths at its ends.
This avoids any dependence on the number of earlier choices in the constant
of the hub bound.
-/

namespace SortingAdversary.Optimal.HubSelector

open scoped BigOperators
open StableBatches

structure Block where
  batch : Batch
  level : ℕ
  index : ℕ
  deriving DecidableEq, Repr

def Block.size (a : Block) : ℕ := 2 ^ a.level
def Block.start (a : Block) : ℕ := a.index * a.size
def Block.stop (a : Block) : ℕ := (a.index + 1) * a.size

def Block.Fits (a : Block) : Prop :=
  a.level ≤ a.batch.level ∧ a.index < 2 ^ (a.batch.level - a.level)

instance (a : Block) : Decidable a.Fits := inferInstanceAs (Decidable (_ ∧ _))

theorem Block.size_pos (a : Block) : 0 < a.size := Nat.two_pow_pos _

theorem Block.start_lt_stop (a : Block) : a.start < a.stop := by
  dsimp [Block.start, Block.stop]
  nlinarith [a.size_pos]

theorem Block.stop_le_batch_size {a : Block} (ha : a.Fits) : a.stop ≤ a.batch.size := by
  calc
    a.stop ≤ 2 ^ (a.batch.level - a.level) * 2 ^ a.level :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt ha.2)
    _ = a.batch.size := Nat.pow_sub_mul_pow 2 ha.1

/-- Zero-based position of the manuscript's one-based midpoint hub. -/
def Block.hubIndex (a : Block) : ℕ :=
  if a.level = 0 then a.index else a.start + 2 ^ (a.level - 1) - 1

theorem Block.hubIndex_bounds (a : Block) : a.start ≤ a.hubIndex ∧ a.hubIndex < a.stop := by
  by_cases he : a.level = 0
  · simp [Block.hubIndex, Block.start, Block.stop, Block.size, he]
  have hepos : 1 ≤ a.level := by omega
  have hhalf := Nat.two_pow_pos (a.level - 1)
  have hpow := Nat.pow_sub_mul_pow 2 hepos
  simp only [pow_one] at hpow
  have hsub := Nat.sub_add_cancel (show 1 ≤ a.start + 2 ^ (a.level - 1) by omega)
  simp only [Block.hubIndex, if_neg he]
  dsimp [Block.start, Block.stop, Block.size] at *
  constructor <;> nlinarith

theorem Block.hubIndex_add_one {a : Block} (he : a.level ≠ 0) :
    a.hubIndex + 1 = DyadicDictionary.hubPosition (a.level - 1) a.index := by
  have hepos : 1 ≤ a.level := by omega
  have hhalf := Nat.two_pow_pos (a.level - 1)
  have hpow := Nat.pow_sub_mul_pow 2 hepos
  simp only [pow_one] at hpow
  have hsub := Nat.sub_add_cancel (show 1 ≤ a.start + 2 ^ (a.level - 1) by omega)
  simp only [Block.hubIndex, if_neg he]
  dsimp [Block.start, Block.size, DyadicDictionary.hubPosition] at *
  nlinarith

/-- The colour is an immutable birth identity, not its mutable palette rank.
The default is used only for malformed blocks, which never pass enumeration. -/
def hubColour (rank : ℕ → ℕ) (hinj : Function.Injective rank) (a : Block) : ℕ :=
  (orderedMembers rank hinj a.batch).getD a.hubIndex 0

theorem hubIndex_lt_length (rank : ℕ → ℕ) (hinj : Function.Injective rank)
    {a : Block} (ha : a.Fits) : a.hubIndex < (orderedMembers rank hinj a.batch).length := by
  rw [orderedMembers_length]
  exact a.hubIndex_bounds.2.trans_le (Block.stop_le_batch_size ha)

theorem hubColour_mem (rank : ℕ → ℕ) (hinj : Function.Injective rank)
    {a : Block} (ha : a.Fits) : hubColour rank hinj a ∈ a.batch.members := by
  rw [← mem_orderedMembers rank hinj a.batch]
  unfold hubColour
  rw [List.getD_eq_getElem _ _ (hubIndex_lt_length rank hinj ha)]
  exact List.getElem_mem _

/-- Singleton and nonsingleton choices are separate veto kinds. -/
def hubKey (rank : ℕ → ℕ) (hinj : Function.Injective rank) (a : Block) : Bool × ℕ :=
  (decide (a.level = 0), hubColour rank hinj a)

/-- A direct finite enumeration of all blocks in all current batches. -/
def allBlocks (births : ℕ) : List Block :=
  (currentBatches births).flatMap fun b =>
    (List.range (b.level + 1)).flatMap fun e =>
      (List.range (2 ^ (b.level - e))).map fun j => ⟨b, e, j⟩

@[simp] theorem mem_allBlocks (births : ℕ) (a : Block) :
    a ∈ allBlocks births ↔ a.batch ∈ currentBatches births ∧ a.Fits := by
  rcases a with ⟨b, e, j⟩
  simp [allBlocks, Block.Fits]

/-- Among the unchanged current batches, a kind and hub colour identify
exactly one block. Therefore excluding earlier records implements precisely
the same-kind colour veto, with no extra forbidden blocks. -/
theorem hubKey_injective (rank : ℕ → ℕ) (hinj : Function.Injective rank)
    {births : ℕ} {a b : Block} (ha : a ∈ allBlocks births) (hb : b ∈ allBlocks births)
    (hkey : hubKey rank hinj a = hubKey rank hinj b) : a = b := by
  have ha' := (mem_allBlocks births a).mp ha
  have hb' := (mem_allBlocks births b).mp hb
  have hcolour : hubColour rank hinj a = hubColour rank hinj b := congrArg Prod.snd hkey
  have hbatch : a.batch = b.batch := currentBatches_unique ha'.1 hb'.1
    (hubColour_mem rank hinj ha'.2) (by rw [hcolour]; exact hubColour_mem rank hinj hb'.2)
  rcases a with ⟨ba, ea, ia⟩
  rcases b with ⟨bb, eb, ib⟩
  dsimp only at hbatch
  subst bb
  have hindex : (Block.mk ba ea ia).hubIndex = (Block.mk ba eb ib).hubIndex := by
    unfold hubColour at hcolour
    rw [List.getD_eq_get _ _ ⟨_, hubIndex_lt_length rank hinj ha'.2⟩,
      List.getD_eq_get _ _ ⟨_, hubIndex_lt_length rank hinj hb'.2⟩] at hcolour
    exact congrArg Fin.val ((orderedMembers_nodup rank hinj ba).injective_get hcolour)
  by_cases he : ea = 0
  · by_cases hf : eb = 0
    · simp only [Block.hubIndex, he, hf, if_pos, Block.mk.injEq] at hindex ⊢
      exact ⟨True.intro, True.intro, hindex⟩
    · have hkind := congrArg Prod.fst hkey
      simp [hubKey, he, hf] at hkind
  · by_cases hf : eb = 0
    · have hkind := congrArg Prod.fst hkey
      simp [hubKey, he, hf] at hkind
    · have hpos : DyadicDictionary.hubPosition (ea - 1) ia =
          DyadicDictionary.hubPosition (eb - 1) ib := by
        rw [← Block.hubIndex_add_one (a := ⟨ba, ea, ia⟩) he,
          ← Block.hubIndex_add_one (a := ⟨ba, eb, ib⟩) hf, hindex]
      obtain ⟨hlevels, hindices⟩ := DyadicDictionary.hubPosition_injective hpos
      have hlevels' : ea = eb := by omega
      simp [hlevels', hindices]

/-- The input window in a batch is half open in its sorted position list. -/
def InWindow (lo hi : Batch → ℕ) (a : Block) : Prop :=
  lo a.batch ≤ a.start ∧ a.stop ≤ hi a.batch

instance (lo hi : Batch → ℕ) (a : Block) : Decidable (InWindow lo hi a) :=
  inferInstanceAs (Decidable (_ ∧ _))

def admissible (lo hi : Batch → ℕ) (veto : Finset Block) (a : Block) : Prop :=
  InWindow lo hi a ∧ a ∉ veto

instance (lo hi : Batch → ℕ) (veto : Finset Block) (a : Block) :
    Decidable (admissible lo hi veto a) := inferInstanceAs (Decidable (_ ∧ _))

/-- Deterministic maximum-level choice; enumeration order breaks ties. -/
def selectBlock (births : ℕ) (lo hi : Batch → ℕ) (veto : Finset Block) : Option Block :=
  List.argmax Block.level ((allBlocks births).filter (fun a => decide (admissible lo hi veto a)))

theorem selected_spec {births : ℕ} {lo hi : Batch → ℕ} {veto : Finset Block} {chosen : Block}
    (hchosen : selectBlock births lo hi veto = some chosen) :
    chosen ∈ allBlocks births ∧ InWindow lo hi chosen ∧ chosen ∉ veto := by
  have hm : chosen ∈ selectBlock births lo hi veto := by simp [hchosen]
  have h := List.argmax_mem hm
  have hf := List.mem_filter.mp h
  exact ⟨hf.1, of_decide_eq_true hf.2⟩

theorem selected_maximal {births : ℕ} {lo hi : Batch → ℕ} {veto : Finset Block} {chosen a : Block}
    (hchosen : selectBlock births lo hi veto = some chosen)
    (ha : a ∈ allBlocks births) (hwindow : InWindow lo hi a) (hveto : a ∉ veto) :
    a.level ≤ chosen.level := by
  have hm : chosen ∈ selectBlock births lo hi veto := by simp [hchosen]
  apply List.le_of_mem_argmax _ hm
  simp [List.mem_filter, ha, admissible, hwindow, hveto]

/-- Every larger contained block is an earlier vetoed record. -/
theorem larger_block_mem_veto {births : ℕ} {lo hi : Batch → ℕ} {veto : Finset Block}
    {chosen a : Block} (hchosen : selectBlock births lo hi veto = some chosen)
    (ha : a ∈ allBlocks births) (hwindow : InWindow lo hi a) (hlarger : chosen.level < a.level) :
    a ∈ veto := by
  by_contra h
  have hmax := selected_maximal hchosen ha hwindow h
  omega

/-! ## The elementary interval-cover estimate -/

/-- Whole aligned intervals between the two boundary intervals. -/
def interiorIndices (lo hi width : ℕ) : Finset ℕ := Finset.Ico (lo / width + 1) (hi / width)

theorem interiorIndex_bounds {lo hi width j : ℕ} (hwidth : 0 < width)
    (hj : j ∈ interiorIndices lo hi width) : lo ≤ j * width ∧ (j + 1) * width ≤ hi := by
  have hj' := Finset.mem_Ico.mp hj
  have hlo : lo < (lo / width + 1) * width := by
    have hmod := Nat.mod_lt lo hwidth
    have hdecomp := Nat.mod_add_div lo width
    nlinarith
  have hleft := Nat.mul_le_mul_right width hj'.1
  have hright := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hj'.2)
  have hhi := Nat.div_mul_le_self hi width
  constructor <;> nlinarith

/-- An interval loses at most two block lengths when only wholly contained
aligned blocks are counted. No asymptotic notation is used. -/
theorem interval_length_le (lo hi width : ℕ) (hwidth : 0 < width) (horder : lo ≤ hi) :
    hi - lo ≤ 2 * width + width * (interiorIndices lo hi width).card := by
  have hlo := Nat.mod_add_div lo width
  have hhi := Nat.mod_add_div hi width
  have hmodlo := Nat.mod_lt lo hwidth
  have hmodhi := Nat.mod_lt hi hwidth
  have hquot : lo / width ≤ hi / width := Nat.div_le_div_right horder
  simp only [interiorIndices, Nat.card_Ico]
  by_cases hgap : lo / width + 1 ≤ hi / width
  · have hsub := Nat.sub_add_cancel hgap
    have hwidthmul : width * (hi / width) =
        width * (hi / width - (lo / width + 1)) + width * (lo / width) + width := by
      calc
        _ = width * (hi / width - (lo / width + 1) + (lo / width + 1)) := by rw [hsub]
        _ = _ := by ring
    have hlength := Nat.sub_add_cancel horder
    omega

  · have hzero : hi / width - (lo / width + 1) = 0 := by omega
    have heq : hi / width = lo / width := by omega
    rw [hzero]
    rw [heq] at hhi
    have hlength := Nat.sub_add_cancel horder
    omega

/-! ## Counting the actual current batches -/

def batches (births : ℕ) : Finset Batch := (currentBatches births).toFinset

@[simp] theorem mem_batches (births : ℕ) (b : Batch) :
    b ∈ batches births ↔ b ∈ currentBatches births := List.mem_toFinset

def largeBatches (births e : ℕ) : Finset Batch :=
  (batches births).filter (fun b => e < b.level)

def smallBatches (births e : ℕ) : Finset Batch :=
  (batches births).filter (fun b => b.level ≤ e)

theorem batch_levels_injOn {births : ℕ} {s : Finset Batch} (hs : s ⊆ batches births) :
    Set.InjOn Batch.level s := by
  intro b hb c hc heq
  exact currentBatches_level_injective
    ((mem_batches _ _).mp (hs hb)) ((mem_batches _ _).mp (hs hc)) heq

theorem largeBatches_card_le {births M e : ℕ} (hcap : births ≤ 2 ^ M) :
    (largeBatches births e).card ≤ M - e := by
  have hinj := batch_levels_injOn (Finset.filter_subset (fun b => e < b.level) (batches births))
  have himage : (largeBatches births e).image Batch.level ⊆ Finset.Ico (e + 1) (M + 1) := by
    intro level hlevel
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hlevel
    have hb' := Finset.mem_filter.mp hb
    have hupper := currentBatches_level_le hcap ((mem_batches _ _).mp hb'.1)
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  calc
    _ = ((largeBatches births e).image Batch.level).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Ico (e + 1) (M + 1)).card := Finset.card_le_card himage
    _ = M - e := by simp

theorem sum_pow_two_add_one (N : ℕ) : (∑ e ∈ Finset.range N, 2 ^ e) + 1 = 2 ^ N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem smallBatches_total_le (births e : ℕ) :
    (∑ b ∈ smallBatches births e, b.size) ≤ 2 ^ (e + 1) := by
  have hinj := batch_levels_injOn (Finset.filter_subset (fun b => b.level ≤ e) (batches births))
  have himage : (smallBatches births e).image Batch.level ⊆ Finset.range (e + 1) := by
    intro level hlevel
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hlevel
    exact Finset.mem_range.mpr (by have h := (Finset.mem_filter.mp hb).2; omega)
  calc
    _ = ∑ level ∈ (smallBatches births e).image Batch.level, 2 ^ level :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ level ∈ Finset.range (e + 1), 2 ^ level :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (by intros; exact Nat.zero_le _)
    _ ≤ 2 ^ (e + 1) := by have h := sum_pow_two_add_one (e + 1); omega

/-- Total number of window colours across the disjoint current batches. -/
def windowCount (births : ℕ) (lo hi : Batch → ℕ) : ℕ :=
  ∑ b ∈ batches births, (hi b - lo b)

/-- The lengths of earlier blocks, counted once per actual earlier record. -/
def vetoCost (veto : Finset Block) : ℕ := ∑ a ∈ veto, a.size

/-- The contained blocks of size `2^(e+1)` used to certify the selection. -/
def interiorBlocks (births e : ℕ) (lo hi : Batch → ℕ) : Finset Block :=
  (largeBatches births e).biUnion fun b =>
    (interiorIndices (lo b) (hi b) (2 ^ (e + 1))).image (fun j => ⟨b, e + 1, j⟩)

theorem interiorBlock_valid {births e : ℕ} {lo hi : Batch → ℕ} {b : Batch} {j : ℕ}
    (hb : b ∈ largeBatches births e) (hupper : hi b ≤ b.size)
    (hj : j ∈ interiorIndices (lo b) (hi b) (2 ^ (e + 1))) :
    (Block.mk b (e + 1) j) ∈ allBlocks births ∧ InWindow lo hi ⟨b, e + 1, j⟩ := by
  have hb' := Finset.mem_filter.mp hb
  have hbounds := interiorIndex_bounds (Nat.two_pow_pos (e + 1)) hj
  have hlevel : e + 1 ≤ b.level := by omega
  have hmul : (j + 1) * 2 ^ (e + 1) ≤ 2 ^ (b.level - (e + 1)) * 2 ^ (e + 1) := by
    rw [Nat.pow_sub_mul_pow 2 hlevel]
    exact hbounds.2.trans hupper
  have hindex : j < 2 ^ (b.level - (e + 1)) := by
    have h := Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos (e + 1))
    omega
  constructor
  · exact (mem_allBlocks _ _).mpr ⟨(mem_batches _ _).mp hb'.1, hlevel, hindex⟩
  · exact hbounds

theorem interiorBlocks_subset_veto {births : ℕ} {lo hi : Batch → ℕ} {veto : Finset Block}
    {chosen : Block} (hchosen : selectBlock births lo hi veto = some chosen)
    (hupper : ∀ b ∈ batches births, hi b ≤ b.size) :
    interiorBlocks births chosen.level lo hi ⊆ veto := by
  intro a ha
  obtain ⟨b, hb, ha⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
  have hvalid := interiorBlock_valid hb (hupper b (Finset.mem_filter.mp hb).1) hj
  exact larger_block_mem_veto hchosen hvalid.1 hvalid.2 (by change chosen.level < chosen.level + 1; omega)

theorem sum_interiorBlocks (births e : ℕ) (lo hi : Batch → ℕ) :
    (∑ a ∈ interiorBlocks births e lo hi, a.size) =
      ∑ b ∈ largeBatches births e,
        2 ^ (e + 1) * (interiorIndices (lo b) (hi b) (2 ^ (e + 1))).card := by
  have hdisjoint : (↑(largeBatches births e) : Set Batch).PairwiseDisjoint
      (fun b => (interiorIndices (lo b) (hi b) (2 ^ (e + 1))).image
        (fun j => Block.mk b (e + 1) j)) := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro a ha hc'
    obtain ⟨j, hj, hja⟩ := Finset.mem_image.mp ha
    obtain ⟨k, hk, hka⟩ := Finset.mem_image.mp hc'
    exact hbc (congrArg Block.batch (hja.trans hka.symm))
  rw [interiorBlocks, Finset.sum_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_image (by
    intro i hi j hj heq
    exact congrArg Block.index heq)]
  simp [Block.size, Nat.mul_comm]

/-- The selected block pays for the whole window with an absolute factor;
the only subtraction is the actual total length of earlier vetoed blocks.
This is the quantitative hub lemma for the executable selector. -/
theorem selected_window_bound {births M : ℕ} {lo hi : Batch → ℕ} {veto : Finset Block}
    {chosen : Block} (hcap : births ≤ 2 ^ M)
    (hchosen : selectBlock births lo hi veto = some chosen)
    (horder : ∀ b ∈ batches births, lo b ≤ hi b)
    (hupper : ∀ b ∈ batches births, hi b ≤ b.size) :
    windowCount births lo hi ≤ 4 * chosen.size * (M - chosen.level + 1) + vetoCost veto := by
  let e := chosen.level
  let large := largeBatches births e
  let small := smallBatches births e
  have hinterior : (∑ a ∈ interiorBlocks births e lo hi, a.size) ≤ vetoCost veto :=
    Finset.sum_le_sum_of_subset_of_nonneg (interiorBlocks_subset_veto hchosen hupper)
      (by intros; omega)
  rw [sum_interiorBlocks] at hinterior
  have hlarge : (∑ b ∈ large, (hi b - lo b)) ≤
      4 * chosen.size * large.card + vetoCost veto := by
    have hlocal (b : Batch) (hb : b ∈ large) :=
      interval_length_le (lo b) (hi b) (2 ^ (e + 1)) (Nat.two_pow_pos _)
        (horder b (Finset.mem_filter.mp hb).1)
    have hsum := Finset.sum_le_sum hlocal
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
    have hwidth : 2 ^ (e + 1) = 2 * chosen.size := by simp [e, Block.size, pow_succ, Nat.mul_comm]
    rw [hwidth] at hsum hinterior
    nlinarith
  have hsmall : (∑ b ∈ small, (hi b - lo b)) ≤ 2 * chosen.size := by
    calc
      _ ≤ ∑ b ∈ small, b.size := Finset.sum_le_sum (fun b hb =>
        (Nat.sub_le (hi b) (lo b)).trans (hupper b (Finset.mem_filter.mp hb).1))
      _ ≤ 2 ^ (e + 1) := smallBatches_total_le births e
      _ = _ := by simp [e, Block.size, pow_succ, Nat.mul_comm]
  have hsplit : windowCount births lo hi =
      (∑ b ∈ large, (hi b - lo b)) + ∑ b ∈ small, (hi b - lo b) := by
    have h := Finset.sum_filter_add_sum_filter_not (batches births)
      (fun b => e < b.level) (fun b => hi b - lo b)
    simpa [windowCount, large, small, largeBatches, smallBatches, Nat.not_lt] using h.symm
  have hlargecard := largeBatches_card_le (e := e) hcap
  have hmul := Nat.mul_le_mul_left (4 * chosen.size) hlargecard
  rw [hsplit]
  dsimp [e, large, small] at hlarge hsmall hmul ⊢
  nlinarith

/-- All singleton records in the supplied batch windows. -/
def windowSingletons (births : ℕ) (lo hi : Batch → ℕ) : Finset Block :=
  (batches births).biUnion fun b => (Finset.Ico (lo b) (hi b)).image (fun j => ⟨b, 0, j⟩)

theorem sum_windowSingletons (births : ℕ) (lo hi : Batch → ℕ) :
    (∑ a ∈ windowSingletons births lo hi, a.size) = windowCount births lo hi := by
  have hdisjoint : (↑(batches births) : Set Batch).PairwiseDisjoint
      (fun b => (Finset.Ico (lo b) (hi b)).image (fun j => Block.mk b 0 j)) := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro a ha hc'
    obtain ⟨j, hj, hja⟩ := Finset.mem_image.mp ha
    obtain ⟨k, hk, hka⟩ := Finset.mem_image.mp hc'
    exact hbc (congrArg Block.batch (hja.trans hka.symm))
  rw [windowSingletons, Finset.sum_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_image (by
    intro i hi j hj heq
    exact congrArg Block.index heq)]
  simp [Block.size]

theorem windowSingleton_valid {births : ℕ} {lo hi : Batch → ℕ} {a : Block}
    (ha : a ∈ windowSingletons births lo hi)
    (hupper : ∀ b ∈ batches births, hi b ≤ b.size) :
    a ∈ allBlocks births ∧ InWindow lo hi a := by
  obtain ⟨b, hb, ha⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
  have hj' := Finset.mem_Ico.mp hj
  constructor
  · apply (mem_allBlocks _ _).mpr
    refine ⟨(mem_batches _ _).mp hb, Nat.zero_le _, ?_⟩
    simpa only [Nat.sub_zero, Batch.size] using hj'.2.trans_le (hupper b hb)
  · simp only [InWindow, Block.start, Block.stop, Block.size, pow_zero, Nat.mul_one]
    exact ⟨hj'.1, by omega⟩

theorem mem_veto_of_none {births : ℕ} {lo hi : Batch → ℕ} {veto : Finset Block}
    (hnone : selectBlock births lo hi veto = none) {a : Block}
    (ha : a ∈ allBlocks births) (hwindow : InWindow lo hi a) : a ∈ veto := by
  by_contra hveto
  have hempty := List.argmax_eq_none.mp hnone
  have hmem : a ∈ (allBlocks births).filter (fun b => decide (admissible lo hi veto b)) := by
    simp [ha, admissible, hwindow, hveto]
  rw [hempty] at hmem
  exact List.not_mem_nil hmem

/-- The executable search cannot fail when the window has more colours
than the total length charged to earlier vetoes. -/
theorem selectBlock_exists {births : ℕ} {lo hi : Batch → ℕ} {veto : Finset Block}
    (hupper : ∀ b ∈ batches births, hi b ≤ b.size)
    (hroom : vetoCost veto < windowCount births lo hi) :
    ∃ chosen, selectBlock births lo hi veto = some chosen := by
  cases hsel : selectBlock births lo hi veto with
  | some chosen => exact ⟨chosen, rfl⟩
  | none =>
      have hsubset : windowSingletons births lo hi ⊆ veto := by
        intro a ha
        have hvalid := windowSingleton_valid ha hupper
        exact mem_veto_of_none hsel hvalid.1 hvalid.2
      have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := Block.size) hsubset
        (by intros; exact Nat.zero_le _)
      rw [sum_windowSingletons] at hsum
      exact False.elim (Nat.not_lt_of_ge hsum hroom)

/-- Restoring the two trimmed endpoints and paying a quarter-window veto
budget gives a constant of eight, independent of the scale-group length. -/
theorem selected_raw_window_bound {births M rawSize : ℕ} {lo hi : Batch → ℕ}
    {veto : Finset Block} {chosen : Block} (hcap : births ≤ 2 ^ M)
    (hchosen : selectBlock births lo hi veto = some chosen)
    (horder : ∀ b ∈ batches births, lo b ≤ hi b)
    (hupper : ∀ b ∈ batches births, hi b ≤ b.size)
    (htrim : rawSize ≤ windowCount births lo hi + 2)
    (hlarge : 8 ≤ rawSize) (hveto : 4 * vetoCost veto ≤ rawSize) :
    rawSize ≤ 8 * chosen.size * (M - chosen.level + 2) := by
  have h := selected_window_bound hcap hchosen horder hupper
  nlinarith

/-! ## Sequential vetoes inside one unchanged group -/

/-- A deterministic series of selections with the same birth counter.
Changing parent batches is deliberately not an operation of this loop. -/
def selectGroup (births : ℕ) (lo hi : ℕ → Batch → ℕ) : ℕ → ℕ → Finset Block → List Block
  | _, 0, _ => []
  | step, count + 1, veto =>
      match selectBlock births (lo step) (hi step) veto with
      | none => []
      | some a => a :: selectGroup births lo hi (step + 1) count (insert a veto)

theorem selectGroup_mem_allBlocks (births : ℕ) (lo hi : ℕ → Batch → ℕ)
    (step count : ℕ) (veto : Finset Block) {a : Block}
    (ha : a ∈ selectGroup births lo hi step count veto) : a ∈ allBlocks births := by
  induction count generalizing step veto with
  | zero => simp [selectGroup] at ha
  | succ count ih =>
      cases hsel : selectBlock births (lo step) (hi step) veto with
      | none => simp [selectGroup, hsel] at ha
      | some chosen =>
          simp only [selectGroup, hsel, List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact (selected_spec hsel).1
          · exact ih _ _ ha

theorem selectGroup_avoids_veto (births : ℕ) (lo hi : ℕ → Batch → ℕ)
    (step count : ℕ) (veto : Finset Block) {a : Block}
    (ha : a ∈ selectGroup births lo hi step count veto) : a ∉ veto := by
  induction count generalizing step veto with
  | zero => simp [selectGroup] at ha
  | succ count ih =>
      cases hsel : selectBlock births (lo step) (hi step) veto with
      | none => simp [selectGroup, hsel] at ha
      | some chosen =>
          simp only [selectGroup, hsel, List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact (selected_spec hsel).2.2
          · have h := ih _ _ ha
            exact fun hv => h (Finset.mem_insert_of_mem hv)

theorem selectGroup_nodup (births : ℕ) (lo hi : ℕ → Batch → ℕ)
    (step count : ℕ) (veto : Finset Block) :
    (selectGroup births lo hi step count veto).Nodup := by
  induction count generalizing step veto with
  | zero => simp [selectGroup]
  | succ count ih =>
      cases hsel : selectBlock births (lo step) (hi step) veto with
      | none => simp [selectGroup, hsel]
      | some chosen =>
          simp only [selectGroup, hsel, List.nodup_cons]
          refine ⟨?_, ih _ _⟩
          intro hmem
          exact selectGroup_avoids_veto _ _ _ _ _ _ hmem (Finset.mem_insert_self _ _)

theorem selectGroup_length_le (births : ℕ) (lo hi : ℕ → Batch → ℕ)
    (step count : ℕ) (veto : Finset Block) :
    (selectGroup births lo hi step count veto).length ≤ count := by
  induction count generalizing step veto with
  | zero => simp [selectGroup]
  | succ count ih =>
      cases hsel : selectBlock births (lo step) (hi step) veto with
      | none => simp [selectGroup, hsel]
      | some chosen =>
          simp only [selectGroup, hsel, List.length_cons]
          exact Nat.succ_le_succ (ih _ _)

/-- At most two selected records can have any particular destination colour,
one of each veto kind. This is the concrete multiplicity bound used by the
scale-group conditional entropy calculation. -/
theorem selected_colour_multiplicity_le_two (rank : ℕ → ℕ) (hinj : Function.Injective rank)
    {births : ℕ} (selected : Finset Block)
    (hvalid : ∀ a ∈ selected, a ∈ allBlocks births) (colour : ℕ) :
    (selected.filter (fun a => hubColour rank hinj a = colour)).card ≤ 2 := by
  let s := selected.filter (fun a => hubColour rank hinj a = colour)
  let kind := fun a : Block => decide (a.level = 0)
  have hkind : Set.InjOn kind s := by
    intro a ha b hb heq
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    apply hubKey_injective rank hinj (hvalid a ha'.1) (hvalid b hb'.1)
    exact Prod.ext heq (ha'.2.trans hb'.2.symm)
  calc
    _ = (s.image kind).card := (Finset.card_image_of_injOn hkind).symm
    _ ≤ Fintype.card Bool := Finset.card_le_univ _
    _ = 2 := by decide

end SortingAdversary.Optimal.HubSelector
