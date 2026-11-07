import SortingAdversary.Optimal.DyadicDictionary
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Sort

/-!
# Executable stable batches from chronological colour births

The birth counter itself is the state. `currentBatches` reconstructs its
binary decomposition, using immutable aligned intervals of birth numbers.
Reconstruction visits one level per binary digit; it is a concrete alternative
to mutating a binary-counter array. It has the same properties required by the
hub selector: a partition of all born colours, at most one current batch at
each power-of-two size, and a permanent identity for every batch ever used.

Palette insertion never renumbers birth identities. The later palette-order
sort is within a fixed batch's members; it does not change these records.
-/

namespace SortingAdversary.Optimal.StableBatches

open scoped BigOperators
open DyadicDictionary

structure Batch where
  start : ℕ
  level : ℕ
  deriving DecidableEq, Repr

def Batch.size (b : Batch) : ℕ := 2 ^ b.level
def Batch.stop (b : Batch) : ℕ := b.start + b.size
def Batch.members (b : Batch) : Finset ℕ := Finset.Ico b.start b.stop

theorem Batch.size_pos (b : Batch) : 0 < b.size := Nat.two_pow_pos _

@[simp] theorem Batch.mem_members (b : Batch) (colour : ℕ) :
    colour ∈ b.members ↔ b.start ≤ colour ∧ colour < b.stop := by
  simp [Batch.members]

@[simp] theorem Batch.card_members (b : Batch) : b.members.card = b.size := by
  simp [Batch.members, Batch.stop]

/-- Descending binary decomposition of a birth interval. The intended
precondition is `count < 2^(depth+1)` and `2^depth ∣ start`. -/
def prefixBatches : ℕ → ℕ → ℕ → List Batch
  | 0, start, count => if count = 0 then [] else [⟨start, 0⟩]
  | depth + 1, start, count =>
      if 2 ^ (depth + 1) ≤ count then
        ⟨start, depth + 1⟩ ::
          prefixBatches depth (start + 2 ^ (depth + 1)) (count - 2 ^ (depth + 1))
      else
        prefixBatches depth start count

theorem prefixBatches_level_le {depth start count : ℕ} {b : Batch}
    (hb : b ∈ prefixBatches depth start count) : b.level ≤ depth := by
  induction depth generalizing start count with
  | zero =>
      by_cases h : count = 0
      · simp [prefixBatches, h] at hb
      · simp only [prefixBatches, if_neg h, List.mem_singleton] at hb
        subst b
        rfl
  | succ depth ih =>
      by_cases h : 2 ^ (depth + 1) ≤ count
      · simp only [prefixBatches, if_pos h, List.mem_cons] at hb
        rcases hb with rfl | hb
        · rfl
        · exact (ih hb).trans (Nat.le_succ _)
      · simp only [prefixBatches, if_neg h] at hb
        exact (ih hb).trans (Nat.le_succ _)

/-- At most one current batch exists at any size. -/
theorem prefixBatches_levels_nodup (depth start count : ℕ) :
    ((prefixBatches depth start count).map Batch.level).Nodup := by
  induction depth generalizing start count with
  | zero => by_cases h : count = 0 <;> simp [prefixBatches, h]
  | succ depth ih =>
      by_cases h : 2 ^ (depth + 1) ≤ count
      · simp only [prefixBatches, if_pos h, List.map_cons, List.nodup_cons]
        constructor
        · intro hmem
          obtain ⟨b, hb, heq⟩ := List.mem_map.mp hmem
          have hle := prefixBatches_level_le hb
          omega
        · exact ih _ _
      · simpa only [prefixBatches, if_neg h] using ih start count

/-- The reconstruction performs at most one batch append per binary level. -/
theorem prefixBatches_length_le (depth start count : ℕ) :
    (prefixBatches depth start count).length ≤ depth + 1 := by
  induction depth generalizing start count with
  | zero => by_cases h : count = 0 <;> simp [prefixBatches, h]
  | succ depth ih =>
      by_cases h : 2 ^ (depth + 1) ≤ count
      · simp only [prefixBatches, if_pos h, List.length_cons]
        exact Nat.add_le_add_right (ih _ _) 1
      · simp only [prefixBatches, if_neg h]
        exact (ih start count).trans (by omega)

/-- Every record has its claimed aligned birth interval, entirely inside
the supplied interval. Alignment is what bounds the entire batch history. -/
theorem prefixBatches_bounds {depth start count : ℕ}
    (hcount : count < 2 ^ (depth + 1)) (haligned : 2 ^ depth ∣ start)
    {b : Batch} (hb : b ∈ prefixBatches depth start count) :
    start ≤ b.start ∧ b.stop ≤ start + count ∧ b.size ∣ b.start := by
  induction depth generalizing start count with
  | zero =>
      by_cases h : count = 0
      · simp [prefixBatches, h] at hb
      · simp only [prefixBatches, if_neg h, List.mem_singleton] at hb
        subst b
        have hc : count = 1 := by norm_num at hcount; omega
        simp [Batch.stop, Batch.size, hc]
  | succ depth ih =>
      have hlow : 2 ^ depth ∣ 2 ^ (depth + 1) := ⟨2, by rw [pow_succ]⟩
      have hstart : 2 ^ depth ∣ start := dvd_trans hlow haligned
      by_cases h : 2 ^ (depth + 1) ≤ count
      · simp only [prefixBatches, if_pos h, List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact ⟨le_rfl, by dsimp [Batch.stop, Batch.size]; omega, haligned⟩
        · have hcount' : count - 2 ^ (depth + 1) < 2 ^ (depth + 1) := by
            rw [show depth + 1 + 1 = (depth + 1) + 1 by omega, pow_succ] at hcount
            omega
          have hresult := ih hcount' (dvd_add hstart hlow) hb
          rcases hresult with ⟨hfirst, hlast, halign⟩
          exact ⟨by omega, by omega, halign⟩
      · simp only [prefixBatches, if_neg h] at hb
        exact ih (by omega) hstart hb

/-- The sum of the actual batch cardinalities is exactly the birth count. -/
theorem prefixBatches_total {depth start count : ℕ}
    (hcount : count < 2 ^ (depth + 1)) :
    ((prefixBatches depth start count).map Batch.size).sum = count := by
  induction depth generalizing start count with
  | zero =>
      by_cases h : count = 0
      · simp [prefixBatches, h]
      · have hc : count = 1 := by norm_num at hcount; omega
        simp [prefixBatches, hc, Batch.size]
  | succ depth ih =>
      by_cases h : 2 ^ (depth + 1) ≤ count
      · have hcount' : count - 2 ^ (depth + 1) < 2 ^ (depth + 1) := by
          rw [pow_succ] at hcount
          omega
        simp only [prefixBatches, if_pos h, List.map_cons, List.sum_cons, Batch.size,
          ih hcount']
        omega
      · simpa only [prefixBatches, if_neg h] using ih (start := start) (by omega)

/-- Every born colour is covered, and no colour outside the requested
interval is included. This is a correctness theorem for the executable
reconstruction, not a supplied partition invariant. -/
theorem prefixBatches_cover {depth start count : ℕ}
    (hcount : count < 2 ^ (depth + 1)) (colour : ℕ) :
    (∃ b ∈ prefixBatches depth start count, colour ∈ b.members) ↔
      start ≤ colour ∧ colour < start + count := by
  induction depth generalizing start count with
  | zero =>
      by_cases h : count = 0
      · simp [prefixBatches, h]
      · have hc : count = 1 := by norm_num at hcount; omega
        simp [prefixBatches, hc, Batch.members, Batch.stop, Batch.size]
  | succ depth ih =>
      by_cases h : 2 ^ (depth + 1) ≤ count
      · have hcount' : count - 2 ^ (depth + 1) < 2 ^ (depth + 1) := by
          rw [pow_succ] at hcount
          omega
        simp only [prefixBatches, if_pos h, List.mem_cons]
        constructor
        · rintro ⟨b, rfl | hb, hcolour⟩
          · simp only [Batch.mem_members, Batch.stop, Batch.size] at hcolour
            omega
          · have hc := (ih hcount').mp ⟨b, hb, hcolour⟩
            omega
        · intro hc
          by_cases hleft : colour < start + 2 ^ (depth + 1)
          · exact ⟨⟨start, depth + 1⟩, Or.inl rfl, by
              simp only [Batch.mem_members, Batch.stop, Batch.size]
              exact ⟨hc.1, hleft⟩⟩
          · obtain ⟨b, hb, hcolour⟩ :=
              (ih (start := start + 2 ^ (depth + 1)) hcount').mpr (by omega)
            exact ⟨b, Or.inr hb, hcolour⟩
      · simpa only [prefixBatches, if_neg h] using ih (start := start) (count := count) (by omega)

/-- The covering is a partition: two current records cannot contain the
same birth identity. -/
theorem prefixBatches_unique {depth start count : ℕ}
    (hcount : count < 2 ^ (depth + 1)) (haligned : 2 ^ depth ∣ start)
    {b c : Batch} {colour : ℕ}
    (hb : b ∈ prefixBatches depth start count) (hc : c ∈ prefixBatches depth start count)
    (hcolourb : colour ∈ b.members) (hcolourc : colour ∈ c.members) : b = c := by
  induction depth generalizing start count with
  | zero =>
      by_cases h : count = 0
      · simp [prefixBatches, h] at hb
      · simp only [prefixBatches, if_neg h, List.mem_singleton] at hb hc
        exact hb.trans hc.symm
  | succ depth ih =>
      have hlow : 2 ^ depth ∣ 2 ^ (depth + 1) := ⟨2, by rw [pow_succ]⟩
      have hstart : 2 ^ depth ∣ start := dvd_trans hlow haligned
      by_cases h : 2 ^ (depth + 1) ≤ count
      · have hcount' : count - 2 ^ (depth + 1) < 2 ^ (depth + 1) := by
          rw [pow_succ] at hcount
          omega
        have halign' := dvd_add hstart hlow
        simp only [prefixBatches, if_pos h, List.mem_cons] at hb hc
        rcases hb with rfl | hb
        · rcases hc with rfl | hc
          · rfl
          · have hbounds := prefixBatches_bounds hcount' halign' hc
            simp only [Batch.mem_members, Batch.stop, Batch.size] at hcolourb hcolourc
            omega
        · rcases hc with rfl | hc
          · have hbounds := prefixBatches_bounds hcount' halign' hb
            simp only [Batch.mem_members, Batch.stop, Batch.size] at hcolourb hcolourc
            omega
          · exact ih hcount' halign' hb hc
      · simp only [prefixBatches, if_neg h] at hb hc
        exact ih (by omega) hstart hb hc

/-- Recompute the current immutable binary batches from the birth counter. -/
def currentBatches (births : ℕ) : List Batch := prefixBatches (Nat.log 2 births) 0 births

theorem currentBatches_levels_nodup (births : ℕ) :
    ((currentBatches births).map Batch.level).Nodup := prefixBatches_levels_nodup _ _ _

theorem currentBatches_length_le (births : ℕ) :
    (currentBatches births).length ≤ Nat.log 2 births + 1 := prefixBatches_length_le _ _ _

theorem currentBatches_total (births : ℕ) :
    ((currentBatches births).map Batch.size).sum = births :=
  prefixBatches_total (Nat.lt_pow_succ_log_self (by decide : 1 < 2) births)

theorem currentBatches_cover (births colour : ℕ) :
    (∃ b ∈ currentBatches births, colour ∈ b.members) ↔ colour < births := by
  simpa only [currentBatches, Nat.zero_le, true_and, Nat.zero_add] using
    prefixBatches_cover (start := 0) (Nat.lt_pow_succ_log_self (by decide : 1 < 2) births) colour

theorem currentBatches_bounds {births : ℕ} {b : Batch} (hb : b ∈ currentBatches births) :
    b.stop ≤ births ∧ b.size ∣ b.start := by
  have h := prefixBatches_bounds
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) births) (dvd_zero _) hb
  simpa using h.2

theorem currentBatches_unique {births colour : ℕ} {b c : Batch}
    (hb : b ∈ currentBatches births) (hc : c ∈ currentBatches births)
    (hcolourb : colour ∈ b.members) (hcolourc : colour ∈ c.members) : b = c :=
  prefixBatches_unique (Nat.lt_pow_succ_log_self (by decide : 1 < 2) births)
    (dvd_zero _) hb hc hcolourb hcolourc

theorem currentBatches_level_injective {births : ℕ} {b c : Batch}
    (hb : b ∈ currentBatches births) (hc : c ∈ currentBatches births)
    (hlevel : b.level = c.level) : b = c :=
  List.inj_on_of_nodup_map (currentBatches_levels_nodup births) hb hc hlevel

theorem currentBatches_level_le {births M : ℕ} (hcap : births ≤ 2 ^ M)
    {b : Batch} (hb : b ∈ currentBatches births) : b.level ≤ M := by
  have hlevel := prefixBatches_level_le hb
  have hlog := Nat.log_mono_right (b := 2) hcap
  rw [Nat.log_pow (by decide : 1 < 2)] at hlog
  exact hlevel.trans hlog

/-- Encode every block of every batch ever current before the final birth
cap in the exact finite dictionary used by the signed-price theorem. The
batch may have been retired long before the last insertion. -/
def dictionaryRecord {M births : ℕ} (hcap : births ≤ 2 ^ M)
    (b : Batch) (hb : b ∈ currentBatches births) (e : ℕ) (he : e ≤ b.level)
    (block : Fin (2 ^ (b.level - e))) : HubSlot M := by
  let batchIndex := b.start / b.size
  have hbounds := currentBatches_bounds hb
  have hstart : batchIndex * 2 ^ b.level = b.start := by
    exact Nat.div_mul_cancel hbounds.2
  have hborn : (batchIndex + 1) * 2 ^ b.level ≤ births := by
    have hstop : (batchIndex + 1) * 2 ^ b.level = b.stop := by
      dsimp [Batch.stop, Batch.size]
      nlinarith [hstart]
    rw [hstop]
    exact hbounds.1
  have hlevel : b.level ≤ M := currentBatches_level_le hcap hb
  exact batchSlot M e b.level he hlevel
    ⟨batchIndex, batch_index_lt hlevel hborn hcap⟩ block

@[simp] theorem dictionaryRecord_deficit {M births : ℕ} (hcap : births ≤ 2 ^ M)
    (b : Batch) (hb : b ∈ currentBatches births) (e : ℕ) (he : e ≤ b.level)
    (block : Fin (2 ^ (b.level - e))) :
    (dictionaryRecord hcap b hb e he block).1.val = M - e := rfl

@[simp] theorem dictionaryRecord_blockSize {M births : ℕ} (hcap : births ≤ 2 ^ M)
    (b : Batch) (hb : b ∈ currentBatches births) (e : ℕ) (he : e ≤ b.level)
    (block : Fin (2 ^ (b.level - e))) :
    blockSize (dictionaryRecord hcap b hb e he block) = 2 ^ e := by
  have heM := he.trans (currentBatches_level_le hcap hb)
  simp only [blockSize, dictionaryRecord_deficit, Nat.sub_sub_self heM]

private theorem packed_indices_injective {width a b i j : ℕ} (hwidth : 0 < width)
    (hi : i < width) (hj : j < width) (h : a * width + i = b * width + j) : a = b ∧ i = j := by
  have hquot := congrArg (fun n => n / width) h
  rw [Nat.mul_comm a width, Nat.mul_comm b width, Nat.mul_add_div hwidth,
    Nat.mul_add_div hwidth, Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hj,
    Nat.add_zero, Nat.add_zero] at hquot
  refine ⟨hquot, ?_⟩
  rw [hquot] at h
  exact Nat.add_left_cancel h

/-- The finite record faithfully retains the batch identity, block scale,
and block position, even when the two records were produced at different
times in the lifetime. This closes the history-to-dictionary counting link. -/
theorem dictionaryRecord_injective {M births₁ births₂ : ℕ}
    (hcap₁ : births₁ ≤ 2 ^ M) (hcap₂ : births₂ ≤ 2 ^ M)
    (b₁ b₂ : Batch) (hb₁ : b₁ ∈ currentBatches births₁) (hb₂ : b₂ ∈ currentBatches births₂)
    (e₁ e₂ : ℕ) (he₁ : e₁ ≤ b₁.level) (he₂ : e₂ ≤ b₂.level)
    (i₁ : Fin (2 ^ (b₁.level - e₁))) (i₂ : Fin (2 ^ (b₂.level - e₂)))
    (heq : dictionaryRecord hcap₁ b₁ hb₁ e₁ he₁ i₁ =
      dictionaryRecord hcap₂ b₂ hb₂ e₂ he₂ i₂) :
    b₁ = b₂ ∧ e₁ = e₂ ∧ i₁.val = i₂.val := by
  have heM₁ := he₁.trans (currentBatches_level_le hcap₁ hb₁)
  have heM₂ := he₂.trans (currentBatches_level_le hcap₂ hb₂)
  have hd := congrArg (fun slot : DyadicDictionary.HubSlot M => slot.1.val) heq
  change M - e₁ = M - e₂ at hd
  have he : e₁ = e₂ := by omega
  have hrow := congrArg (fun slot : DyadicDictionary.HubSlot M => slot.2.1.val) heq
  change b₁.level - e₁ = b₂.level - e₂ at hrow
  have hlevel : b₁.level = b₂.level := by omega
  have hflat := congrArg (fun slot : DyadicDictionary.HubSlot M => slot.2.2.val) heq
  change b₁.start / b₁.size * 2 ^ (b₁.level - e₁) + i₁.val =
    b₂.start / b₂.size * 2 ^ (b₂.level - e₂) + i₂.val at hflat
  have hpow : 2 ^ (b₁.level - e₁) = 2 ^ (b₂.level - e₂) := congrArg (fun d => 2 ^ d) hrow
  have hflat' := (congrArg (fun width => b₁.start / b₁.size * width + i₁.val) hpow.symm).trans hflat
  have hi₁ : i₁.val < 2 ^ (b₂.level - e₂) := i₁.isLt.trans_le hpow.le
  have hpack := packed_indices_injective (Nat.two_pow_pos _) hi₁ i₂.isLt hflat'
  have hstart₁ : b₁.start / b₁.size * 2 ^ b₁.level = b₁.start :=
    Nat.div_mul_cancel (currentBatches_bounds hb₁).2
  have hstart₂ : b₂.start / b₂.size * 2 ^ b₂.level = b₂.start :=
    Nat.div_mul_cancel (currentBatches_bounds hb₂).2
  have hstart : b₁.start = b₂.start := by
    calc
      _ = b₁.start / b₁.size * 2 ^ b₁.level := hstart₁.symm
      _ = b₂.start / b₂.size * 2 ^ b₂.level := by rw [hpack.1, hlevel]
      _ = _ := hstart₂
  have hb : b₁ = b₂ := by
    cases b₁
    cases b₂
    simp only [Batch.mk.injEq]
    exact ⟨hstart, hlevel⟩
  exact ⟨hb, he, hpack.2⟩

/-! ## Ordering a fixed batch in the current palette -/

def rankRel (rank : ℕ → ℕ) (a b : ℕ) : Prop := rank a ≤ rank b

instance rankRel_decidable (rank : ℕ → ℕ) : DecidableRel (rankRel rank) :=
  fun _ _ => inferInstanceAs (Decidable (_ ≤ _))

instance rankRel_trans (rank : ℕ → ℕ) : IsTrans ℕ (rankRel rank) :=
  ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩

instance rankRel_total (rank : ℕ → ℕ) : Std.Total (rankRel rank) :=
  ⟨fun a b => le_total (rank a) (rank b)⟩

theorem rankRel_antisymm {rank : ℕ → ℕ} (hinj : Function.Injective rank) :
    Std.Antisymm (rankRel rank) := ⟨fun _ _ h₁ h₂ => hinj (le_antisymm h₁ h₂)⟩

/-- An executable sort by current palette rank. Injectivity holds because
distinct live colour identities have distinct palette positions. -/
def orderedMembers (rank : ℕ → ℕ) (hinj : Function.Injective rank) (b : Batch) : List ℕ :=
  letI := rankRel_antisymm hinj
  b.members.sort (rankRel rank)

@[simp] theorem orderedMembers_length (rank : ℕ → ℕ) (hinj : Function.Injective rank) (b : Batch) :
    (orderedMembers rank hinj b).length = b.size := by
  let _ := rankRel_antisymm hinj
  simp [orderedMembers]

@[simp] theorem mem_orderedMembers (rank : ℕ → ℕ) (hinj : Function.Injective rank) (b : Batch)
    (colour : ℕ) : colour ∈ orderedMembers rank hinj b ↔ colour ∈ b.members := by
  let _ := rankRel_antisymm hinj
  simp [orderedMembers]

theorem orderedMembers_nodup (rank : ℕ → ℕ) (hinj : Function.Injective rank) (b : Batch) :
    (orderedMembers rank hinj b).Nodup := by
  let _ := rankRel_antisymm hinj
  exact Finset.sort_nodup _ _

theorem orderedMembers_pairwise (rank : ℕ → ℕ) (hinj : Function.Injective rank) (b : Batch) :
    (orderedMembers rank hinj b).Pairwise (rankRel rank) := by
  let _ := rankRel_antisymm hinj
  exact Finset.pairwise_sort _ _

/-- Recomputing a batch's sort after an order-preserving palette insertion
gives exactly the same list of birth identities. Thus its hub colours are
immutable throughout all later refinements, even if numeric ranks change. -/
theorem orderedMembers_stable (oldRank newRank : ℕ → ℕ)
    (hold : Function.Injective oldRank) (hnew : Function.Injective newRank) (b : Batch)
    (hpreserve : ∀ a ∈ b.members, ∀ c ∈ b.members,
      oldRank a ≤ oldRank c ↔ newRank a ≤ newRank c) :
    orderedMembers oldRank hold b = orderedMembers newRank hnew b := by
  let _ := rankRel_antisymm hold
  let _ := rankRel_antisymm hnew
  let embedding : ℕ ↪ ℕ := ⟨newRank, hnew⟩
  have hleft := Finset.map_sort embedding b.members (rankRel oldRank) (· ≤ ·)
    (by simpa [rankRel, embedding] using hpreserve)
  have hright := Finset.map_sort embedding b.members (rankRel newRank) (· ≤ ·)
    (by intros; rfl)
  exact (List.map_injective_iff.mpr hnew) (hleft.trans hright.symm)

end SortingAdversary.Optimal.StableBatches
