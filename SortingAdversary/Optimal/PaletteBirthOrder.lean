import SortingAdversary.Optimal.BatchWindows
import SortingAdversary.Optimal.FiniteRefinement
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Executable palette permutations after a chronological colour birth

The last new birth identity is sent to the chosen fresh palette position.
Every old identity is transported by the order-preserving insertion around
that position. Both directions of the permutation are executable: the
construction composes explicit finite/option equivalences and the previous
permutation, without choosing an inverse by classical choice.
-/

namespace SortingAdversary.Optimal.PaletteBirthOrder

open FiniteRefinement BatchWindows StableBatches

variable {K : ℕ}

def extend (order : Equiv.Perm (Fin K)) (fresh : Fin (K + 1)) : Equiv.Perm (Fin (K + 1)) :=
  (finSuccEquiv' (Fin.last K)).trans ((Equiv.optionCongr order).trans (finSuccEquiv' fresh).symm)

@[simp] theorem extend_last (order : Equiv.Perm (Fin K)) (fresh : Fin (K + 1)) :
    extend order fresh (Fin.last K) = fresh := by
  simp [extend]

@[simp] theorem extend_old (order : Equiv.Perm (Fin K)) (fresh : Fin (K + 1)) (i : Fin K) :
    extend order fresh i.castSucc = fresh.succAbove (order i) := by
  have hi : finSuccEquiv' (Fin.last K) i.castSucc = some i := by
    simpa only [Fin.succAbove_last_apply] using finSuccEquiv'_succAbove (Fin.last K) i
  simp [extend, hi]

theorem extend_old_le_iff (order : Equiv.Perm (Fin K)) (fresh : Fin (K + 1)) (i j : Fin K) :
    extend order fresh i.castSucc ≤ extend order fresh j.castSucc ↔ order i ≤ order j := by
  rw [extend_old, extend_old]
  exact Fin.succAbove_le_succAbove_iff

theorem succAbove_fresh_eq_embed (c d : Fin K) :
    (freshColor c).succAbove d = embedColor c d := by
  by_cases h : d.val ≤ c.val
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by
      change d.val < c.val + 1
      omega)]
    apply Fin.ext
    simp [embedColor, Refinement.embed, h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by
      change c.val + 1 ≤ d.val
      omega)]
    apply Fin.ext
    simp [embedColor, Refinement.embed, h]

theorem succAbove_before_eq_embed (c d : Fin K) :
    c.castSucc.succAbove d = embedColorBefore c d := by
  by_cases h : d.val < c.val
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    apply Fin.ext
    simp [embedColorBefore, Refinement.embedBefore, h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by exact Nat.le_of_not_gt h)]
    apply Fin.ext
    simp [embedColorBefore, Refinement.embedBefore, h]

/-- The lower-endpoint split inserts immediately above the old endpoint. -/
def extendAfter (order : Equiv.Perm (Fin K)) (c : Fin K) : Equiv.Perm (Fin (K + 1)) :=
  extend order (freshColor c)

/-- The upper-endpoint split inserts immediately below the old endpoint. -/
def extendBefore (order : Equiv.Perm (Fin K)) (c : Fin K) : Equiv.Perm (Fin (K + 1)) :=
  extend order c.castSucc

/-- The birthday capacity repair appends a top palette position. -/
def extendTop (order : Equiv.Perm (Fin K)) : Equiv.Perm (Fin (K + 1)) :=
  extend order (Fin.last K)

@[simp] theorem extendAfter_old (order : Equiv.Perm (Fin K)) (c i : Fin K) :
    extendAfter order c i.castSucc = embedColor c (order i) := by
  rw [extendAfter, extend_old, succAbove_fresh_eq_embed]

@[simp] theorem extendAfter_new (order : Equiv.Perm (Fin K)) (c : Fin K) :
    extendAfter order c (Fin.last K) = freshColor c := extend_last _ _

@[simp] theorem extendBefore_old (order : Equiv.Perm (Fin K)) (c i : Fin K) :
    extendBefore order c i.castSucc = embedColorBefore c (order i) := by
  rw [extendBefore, extend_old, succAbove_before_eq_embed]

@[simp] theorem extendBefore_new (order : Equiv.Perm (Fin K)) (c : Fin K) :
    extendBefore order c (Fin.last K) = c.castSucc := extend_last _ _

@[simp] theorem extendTop_old (order : Equiv.Perm (Fin K)) (i : Fin K) :
    extendTop order i.castSucc = (order i).castSucc := by simp [extendTop]

@[simp] theorem extendTop_new (order : Equiv.Perm (Fin K)) :
    extendTop order (Fin.last K) = Fin.last K := extend_last _ _

theorem paletteRank_old (order : Equiv.Perm (Fin K)) (fresh : Fin (K + 1))
    (i : ℕ) (hi : i < K) :
    paletteRank (extend order fresh) i = (fresh.succAbove (order ⟨i, hi⟩)).val := by
  have h := congrArg Fin.val (extend_old order fresh ⟨i, hi⟩)
  simpa only [← paletteRank_apply, Fin.val_castSucc] using h

@[simp] theorem paletteRank_new (order : Equiv.Perm (Fin K)) (fresh : Fin (K + 1)) :
    paletteRank (extend order fresh) K = fresh.val := by
  have h := congrArg Fin.val (extend_last order fresh)
  simpa only [← paletteRank_apply, Fin.val_last] using h

theorem paletteRank_old_order (order : Equiv.Perm (Fin K)) (fresh : Fin (K + 1))
    (i j : ℕ) (hi : i < K) (hj : j < K) :
    paletteRank order i ≤ paletteRank order j ↔
      paletteRank (extend order fresh) i ≤ paletteRank (extend order fresh) j := by
  rw [paletteRank_old order fresh i hi, paletteRank_old order fresh j hj]
  simp only [paletteRank, dif_pos hi, dif_pos hj]
  exact Fin.succAbove_le_succAbove_iff.symm

/-- Every already formed batch keeps exactly the same sorted birth-identity
list through a concrete permutation extension. -/
theorem orderedMembers_preserved (order : Equiv.Perm (Fin K)) (fresh : Fin (K + 1))
    (b : Batch) (hborn : b.stop ≤ K) :
    orderedMembers (paletteRank order) (paletteRank_injective order) b =
      orderedMembers (paletteRank (extend order fresh)) (paletteRank_injective _) b := by
  apply orderedMembers_stable
  intro i hi j hj
  have hil : i < K := (Finset.mem_Ico.mp hi).2.trans_le hborn
  have hjl : j < K := (Finset.mem_Ico.mp hj).2.trans_le hborn
  exact paletteRank_old_order order fresh i j hil hjl

/-- The hub's immutable colour identity survives either endpoint split and
the top append, including retired batches still used in the dictionary. -/
theorem hubColour_preserved (order : Equiv.Perm (Fin K)) (fresh : Fin (K + 1))
    (block : HubSelector.Block) (hborn : block.batch.stop ≤ K) :
    HubSelector.hubColour (paletteRank order) (paletteRank_injective order) block =
      HubSelector.hubColour (paletteRank (extend order fresh)) (paletteRank_injective _) block := by
  unfold HubSelector.hubColour
  rw [orderedMembers_preserved order fresh block.batch hborn]

end SortingAdversary.Optimal.PaletteBirthOrder
