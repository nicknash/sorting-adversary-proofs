import SortingAdversary.Optimal.Routing
import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-!
# Splitting a colour without losing a selected fibre

When a pin must be made at the lower edge `c` of its support, insert one fresh
colour immediately above `c`.  Old colours retain their chronological identity
through `embed`.  Raise the selected vertex and its equal-colour successors.
`collapse` is a left inverse, so this operation is injective on old maps.

These definitions implement both endpoint constructions of section 2.
The upper endpoint is the order dual. Artificial lists are lifted by
inverse image under `collapse`; physical pins are lifted by `embed`.
-/

namespace SortingAdversary.Optimal.Refinement

open Routing

/-- The identity of an old colour after a new colour is inserted above `c`. -/
def embed (c k : ℕ) : ℕ := if k ≤ c then k else k + 1

/-- Collapse the fresh colour `c+1` onto `c`. -/
def collapse (c k : ℕ) : ℕ := if k ≤ c then k else k - 1

@[simp] theorem collapse_embed (c k : ℕ) : collapse c (embed c k) = k := by
  unfold embed collapse
  split_ifs <;> omega

@[simp] theorem collapse_fresh (c : ℕ) : collapse c (c + 1) = c := by
  unfold collapse
  split_ifs <;> omega

theorem embed_strictMono (c : ℕ) : StrictMono (embed c) := by
  intro a b hab
  unfold embed
  split_ifs <;> omega

theorem embed_monotone (c : ℕ) : Monotone (embed c) :=
  (embed_strictMono c).monotone

theorem collapse_monotone (c : ℕ) : Monotone (collapse c) := by
  intro a b hab
  unfold collapse
  split_ifs <;> omega

theorem embed_injective (c : ℕ) : Function.Injective (embed c) :=
  (embed_strictMono c).injective

variable {α : Type*} (R : α → α → Prop) [DecidableRel R]

/-- Raise precisely the equal-colour successors of `v`, including `v` for a
reflexive public order. Every other old colour keeps its identity. -/
def liftMap (v : α) (c : ℕ) (f : α → ℕ) (x : α) : ℕ :=
  if f x = c ∧ R v x then c + 1 else embed c (f x)

@[simp] theorem collapse_liftMap (v : α) (c : ℕ) (f : α → ℕ) (x : α) :
    collapse c (liftMap R v c f x) = f x := by
  unfold liftMap
  split_ifs with h
  · rw [collapse_fresh, h.1]
  · exact collapse_embed c (f x)

/-- Collapse reconstructs the full old assignment, not only its selected
coordinate. This is the fibre-count injection used in the manuscript. -/
theorem liftMap_injective (v : α) (c : ℕ) :
    Function.Injective (liftMap R v c) := by
  intro f g h
  funext x
  have hx := congrArg (fun k : α → ℕ => collapse c (k x)) h
  simpa only [collapse_liftMap] using hx

theorem liftMap_selected {v : α} {c : ℕ} {f : α → ℕ}
    (hrefl : R v v) (hv : f v = c) : liftMap R v c f v = c + 1 := by
  simp [liftMap, hv, hrefl]

/-- Every old raw inequality survives the refinement. -/
theorem liftMap_respects
    (htrans : ∀ ⦃x y z : α⦄, R x y → R y z → R x z)
    {v : α} {c : ℕ} {f : α → ℕ} (hf : Respects R f) :
    Respects R (liftMap R v c f) := by
  intro x y hxy
  have hle := hf x y hxy
  unfold liftMap
  split_ifs with hx hy hy
  · exact le_refl _
  · have hvy := htrans hx.2 hxy
    have hne : f y ≠ c := fun heq => hy ⟨heq, hvy⟩
    unfold embed
    split_ifs <;> omega
  · unfold embed
    split_ifs <;> omega
  · exact embed_monotone c hle

/-- An old physical pin is unchanged in identity unless it is an equal-colour
successor. The interior-support hypothesis rules out precisely that case. -/
theorem liftMap_pin {v p : α} {c d : ℕ} {f : α → ℕ}
    (hpin : f p = d) (hnot : ¬ (d = c ∧ R v p)) :
    liftMap R v c f p = embed c d := by
  simp only [liftMap, hpin, if_neg hnot]

omit [DecidableRel R] in
/-- If a higher value of `v` remains feasible, no physical pin at `c` can be
a successor of `v`. -/
theorem no_pinned_successor {v p : α} {c : ℕ} {g : α → ℕ}
    (hg : Respects R g) (hpin : g p = c) (hhi : c < g v) : ¬ R v p := by
  intro hvp
  have h := hg v p hvp
  rw [hpin] at h
  omega

/-- Lifting an artificial list by the collapse map retains every old member. -/
theorem liftMap_in_lifted_list {v : α} {c : ℕ} {f : α → ℕ}
    {lists : α → Set ℕ} (hf : ∀ x, f x ∈ lists x) :
    ∀ x, liftMap R v c f x ∈ collapse c ⁻¹' lists x := by
  intro x
  simpa only [Set.mem_preimage, collapse_liftMap] using hf x

theorem liftMap_le_succ (v : α) (c : ℕ) (f : α → ℕ) (x : α) :
    liftMap R v c f x ≤ f x + 1 := by
  unfold liftMap embed
  split_ifs <;> omega

theorem liftMap_palette {v : α} {c K : ℕ} {f : α → ℕ}
    (hf : ∀ x, f x < K) : ∀ x, liftMap R v c f x < K + 1 := by
  intro x
  have h := liftMap_le_succ R v c f x
  have hx := hf x
  omega

/-- The fresh colour lies strictly between the old lower endpoint and any
old attainable upper value above it. -/
theorem fresh_is_interior {c u : ℕ} (h : c < u) :
    embed c c < c + 1 ∧ c + 1 < embed c u := by
  unfold embed
  split_ifs <;> omega

omit [DecidableRel R] in
/-- The unraised embedding of a whole map preserves all old inequalities. -/
theorem embedMap_respects {c : ℕ} {f : α → ℕ} (hf : Respects R f) :
    Respects R (fun x => embed c (f x)) := by
  intro x y hxy
  exact embed_monotone c (hf x y hxy)

/-- Strictly separated artificial walls remain separated under arbitrary
inverse-image lifting, even though the fresh colour collapses onto an old one. -/
theorem strict_walls_survive {c l r x y : ℕ}
    (hlr : l < r) (hx : collapse c x ≤ l) (hy : r ≤ collapse c y) : x < y := by
  have hcollapse : collapse c x < collapse c y := lt_of_le_of_lt hx (lt_of_lt_of_le hlr hy)
  by_contra h
  exact (not_le_of_gt hcollapse) (collapse_monotone c (Nat.le_of_not_lt h))

/-! ## The upper endpoint, with a fresh colour immediately below the old pin -/

/-- Here the original colour `c` retains identity `c+1`, and the fresh colour
has index `c`. The same collapse map identifies these two indices. -/
def embedBefore (c k : ℕ) : ℕ := if k < c then k else k + 1

@[simp] theorem collapse_embedBefore (c k : ℕ) : collapse c (embedBefore c k) = k := by
  unfold embedBefore collapse
  split_ifs <;> omega

theorem embedBefore_strictMono (c : ℕ) : StrictMono (embedBefore c) := by
  intro a b hab
  unfold embedBefore
  split_ifs <;> omega

theorem embedBefore_monotone (c : ℕ) : Monotone (embedBefore c) :=
  (embedBefore_strictMono c).monotone

/-- Lower the equal-colour predecessors of the selected vertex. -/
def liftMapBefore (v : α) (c : ℕ) (f : α → ℕ) (x : α) : ℕ :=
  if f x = c ∧ R x v then c else embedBefore c (f x)

@[simp] theorem collapse_liftMapBefore (v : α) (c : ℕ) (f : α → ℕ) (x : α) :
    collapse c (liftMapBefore R v c f x) = f x := by
  unfold liftMapBefore
  split_ifs with h
  · simp [collapse, h.1]
  · exact collapse_embedBefore c (f x)

theorem liftMapBefore_injective (v : α) (c : ℕ) :
    Function.Injective (liftMapBefore R v c) := by
  intro f g h
  funext x
  have hx := congrArg (fun k : α → ℕ => collapse c (k x)) h
  simpa only [collapse_liftMapBefore] using hx

theorem liftMapBefore_selected {v : α} {c : ℕ} {f : α → ℕ}
    (hrefl : R v v) (hv : f v = c) : liftMapBefore R v c f v = c := by
  simp [liftMapBefore, hv, hrefl]

theorem liftMapBefore_respects
    (htrans : ∀ ⦃x y z : α⦄, R x y → R y z → R x z)
    {v : α} {c : ℕ} {f : α → ℕ} (hf : Respects R f) :
    Respects R (liftMapBefore R v c f) := by
  intro x y hxy
  have hle := hf x y hxy
  unfold liftMapBefore
  split_ifs with hx hy hy
  · exact le_refl _
  · unfold embedBefore
    split_ifs <;> omega
  · have hxv := htrans hxy hy.2
    have hne : f x ≠ c := fun heq => hx ⟨heq, hxv⟩
    unfold embedBefore
    split_ifs <;> omega
  · exact embedBefore_monotone c hle

theorem liftMapBefore_pin {v p : α} {c d : ℕ} {f : α → ℕ}
    (hpin : f p = d) (hnot : ¬ (d = c ∧ R p v)) :
    liftMapBefore R v c f p = embedBefore c d := by
  simp only [liftMapBefore, hpin, if_neg hnot]

omit [DecidableRel R] in
theorem no_pinned_predecessor {v p : α} {c : ℕ} {g : α → ℕ}
    (hg : Respects R g) (hpin : g p = c) (hlo : g v < c) : ¬ R p v := by
  intro hpv
  have h := hg p v hpv
  rw [hpin] at h
  omega

theorem liftMapBefore_in_lifted_list {v : α} {c : ℕ} {f : α → ℕ}
    {lists : α → Set ℕ} (hf : ∀ x, f x ∈ lists x) :
    ∀ x, liftMapBefore R v c f x ∈ collapse c ⁻¹' lists x := by
  intro x
  simpa only [Set.mem_preimage, collapse_liftMapBefore] using hf x

theorem liftMapBefore_palette {v : α} {c K : ℕ} {f : α → ℕ}
    (hf : ∀ x, f x < K) : ∀ x, liftMapBefore R v c f x < K + 1 := by
  intro x
  have hx := hf x
  unfold liftMapBefore embedBefore
  split_ifs <;> omega

theorem fresh_before_is_interior {l c : ℕ} (h : l < c) :
    embedBefore c l < c ∧ c < embedBefore c c := by
  unfold embedBefore
  split_ifs <;> omega

omit [DecidableRel R] in
theorem embedMapBefore_respects {c : ℕ} {f : α → ℕ} (hf : Respects R f) :
    Respects R (fun x => embedBefore c (f x)) := by
  intro x y hxy
  exact embedBefore_monotone c (hf x y hxy)

end SortingAdversary.Optimal.Refinement
