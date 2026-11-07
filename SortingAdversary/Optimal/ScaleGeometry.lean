import SortingAdversary.Optimal.GraphBalls
import SortingAdversary.Optimal.NumericalGeometry
import SortingAdversary.Optimal.PinTransitions
import Mathlib.Data.Finset.Max

/-!
# Concrete separated-scale selection in the raw graph

The selected labels are the first crossings of computable integer thresholds
along an actual finite walk. Bounded adjacent width ratios control overshoot.
The same ratio bound on every shortcut then proves separation in graph balls,
and consequently numerical incomparability and preservation of reserved windows.
-/

namespace SortingAdversary.Optimal.ScaleGeometry

open WeakMaps WeakMaps.WeakSystem GraphBalls SparseClosure NumericalGeometry
open FiniteRefinement PinTransitions

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A supplied finite raw-graph walk. Staying at a vertex is permitted; it has
no effect on first crossings and makes breadth-first witnesses convenient. -/
structure Walk (E : α → α → Bool) (length : ℕ) where
  vertex : Fin (length + 1) → α
  step : ∀ i : Fin length, vertex i.succ ∈ closedNeighbors E (vertex i.castSucc)

namespace Walk

variable {E : α → α → Bool} {length : ℕ}

def start (p : Walk E length) : α := p.vertex 0
def finish (p : Walk E length) : α := p.vertex (Fin.last length)

/-- A zero-length walk. -/
def single (E : α → α → Bool) (x : α) : Walk E 0 where
  vertex _ := x
  step i := Fin.elim0 i

/-- Prepend one closed-neighbor step to a finite walk. -/
def prepend (p : Walk E length) (x : α) (hx : p.start ∈ closedNeighbors E x) : Walk E (length + 1) where
  vertex := Fin.cases x p.vertex
  step := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [start, Fin.castSucc_zero, Fin.cases_zero, Fin.cases_succ] using hx
    · simpa only [Fin.castSucc_succ, Fin.cases_succ] using p.step j

@[simp] theorem prepend_start (p : Walk E length) (x : α) (hx : p.start ∈ closedNeighbors E x) :
    (p.prepend x hx).start = x := rfl

@[simp] theorem prepend_finish (p : Walk E length) (x : α) (hx : p.start ∈ closedNeighbors E x) :
    (p.prepend x hx).finish = p.finish := rfl

/-- Breadth expansion gives an actual finite walk with the stated endpoints. -/
theorem exists_of_mem_ball {E : α → α → Bool} {x y : α} {r : ℕ} (hy : y ∈ ball E x r) :
    ∃ p : Walk E r, p.start = x ∧ p.finish = y := by
  induction r generalizing x with
  | zero =>
    have hy' : y = x := by simpa only [ball_zero, Finset.mem_singleton] using hy
    exact ⟨single E x, rfl, hy'.symm⟩
  | succ r ih =>
    obtain ⟨z, hz, hyz⟩ := (mem_ball_succ E x y r).mp hy
    obtain ⟨p, hpstart, hpfinish⟩ := ih hyz
    exact ⟨p.prepend x (hpstart ▸ hz), rfl, hpfinish⟩

/-- A connected pair has a shortest raw-graph walk; first crossings can be
selected on this concrete witness. -/
theorem exists_shortest {E : α → α → Bool} {x y : α} (h : Connected E x y) :
    ∃ r, ∃ p : Walk E r, p.start = x ∧ p.finish = y ∧ ∀ s, y ∈ ball E x s → r ≤ s := by
  obtain ⟨p, hpstart, hpfinish⟩ := exists_of_mem_ball (Nat.find_spec h)
  exact ⟨Nat.find h, p, hpstart, hpfinish, fun _ hs => Nat.find_min' h hs⟩

/-- Every position of the walk is connected to its initial vertex. -/
theorem vertex_mem_ball (p : Walk E length) (i : Fin (length + 1)) :
    p.vertex i ∈ ball E p.start i.val := by
  refine Fin.induction ?_ (fun j ih => ?_) i
  · exact center_mem_ball E p.start 0
  · exact mem_ball_add E ih ((mem_ball_one E _ _).mpr (p.step j))

/-- Indices at which the path has reached the specified width threshold. -/
def crossingIndices (p : Walk E length) (W : α → ℕ) (threshold : ℕ) : Finset (Fin (length + 1)) :=
  Finset.univ.filter (fun i => threshold ≤ W (p.vertex i))

theorem crossings_nonempty (p : Walk E length) (W : α → ℕ) (threshold : ℕ)
    (hend : threshold ≤ W p.finish) : (p.crossingIndices W threshold).Nonempty :=
  ⟨Fin.last length, by simpa [crossingIndices, finish] using hend⟩

/-- The actual first threshold crossing, found by a finite minimum. -/
def firstIndex (p : Walk E length) (W : α → ℕ) (threshold : ℕ)
    (hend : threshold ≤ W p.finish) : Fin (length + 1) :=
  (p.crossingIndices W threshold).min' (p.crossings_nonempty W threshold hend)

theorem firstIndex_reaches (p : Walk E length) (W : α → ℕ) (threshold : ℕ)
    (hend : threshold ≤ W p.finish) : threshold ≤ W (p.vertex (p.firstIndex W threshold hend)) := by
  have h := Finset.min'_mem (p.crossingIndices W threshold) (p.crossings_nonempty W threshold hend)
  exact (Finset.mem_filter.mp h).2

theorem firstIndex_le (p : Walk E length) (W : α → ℕ) (threshold : ℕ)
    (hend : threshold ≤ W p.finish) (i : Fin (length + 1)) (hi : threshold ≤ W (p.vertex i)) :
    p.firstIndex W threshold hend ≤ i :=
  Finset.min'_le _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

theorem before_firstIndex (p : Walk E length) (W : α → ℕ) (threshold : ℕ)
    (hend : threshold ≤ W p.finish) (i : Fin (length + 1)) (hi : i < p.firstIndex W threshold hend) :
    W (p.vertex i) < threshold := by
  by_contra h
  have hle := p.firstIndex_le W threshold hend i (Nat.le_of_not_gt h)
  exact (not_le_of_gt hi) hle

/-- A first crossing overshoots the threshold by at most the adjacent ratio. -/
theorem firstIndex_width_le (p : Walk E length) (W : α → ℕ) (L threshold : ℕ)
    (hL : 1 ≤ L) (hstart : W p.start ≤ threshold) (hend : threshold ≤ W p.finish)
    (hstep : ∀ i : Fin length, W (p.vertex i.succ) ≤ L * W (p.vertex i.castSucc)) :
    W (p.vertex (p.firstIndex W threshold hend)) ≤ L * threshold := by
  let k := p.firstIndex W threshold hend
  by_cases hk : k.val = 0
  · have hk' : k = 0 := Fin.ext hk
    change W (p.vertex k) ≤ _
    rw [hk']
    exact hstart.trans (by simpa using Nat.mul_le_mul_right threshold hL)
  · let i : Fin length := ⟨k.val - 1, by have := k.isLt; omega⟩
    have hisucc : i.succ = k := by apply Fin.ext; dsimp [i]; omega
    have hiprev : i.castSucc < k := by change k.val - 1 < k.val; omega
    have hbefore := p.before_firstIndex W threshold hend i.castSucc hiprev
    have h := hstep i
    rw [hisucc] at h
    exact h.trans (Nat.mul_le_mul_left L hbefore.le)

/-- A threshold family fitting below the final width. -/
def selected (p : Walk E length) (W : α → ℕ) (A w J : ℕ)
    (hA : 1 ≤ A) (hend : A ^ J * w ≤ W p.finish) (i : Fin J) : α :=
  p.vertex (p.firstIndex W (A ^ i.val * w)
    ((Nat.mul_le_mul_right w (Nat.pow_le_pow_right hA i.isLt.le)).trans hend))

theorem selected_lower (p : Walk E length) (W : α → ℕ) (A w J : ℕ)
    (hA : 1 ≤ A) (hend : A ^ J * w ≤ W p.finish) (i : Fin J) :
    A ^ i.val * w ≤ W (p.selected W A w J hA hend i) := p.firstIndex_reaches W _ _

theorem selected_upper (p : Walk E length) (W : α → ℕ) (L A w J : ℕ)
    (hL : 1 ≤ L) (hA : 1 ≤ A) (hstart : W p.start = w) (hend : A ^ J * w ≤ W p.finish)
    (hstep : ∀ i : Fin length, W (p.vertex i.succ) ≤ L * W (p.vertex i.castSucc)) (i : Fin J) :
    W (p.selected W A w J hA hend i) ≤ L * (A ^ i.val * w) := by
  apply p.firstIndex_width_le W L _ hL _ _ hstep
  rw [hstart]
  have hp : 1 ≤ A ^ i.val := one_le_pow₀ hA
  simpa using Nat.mul_le_mul_right w hp

/-- A natural-indexed form convenient for the chronological hub executor. -/
def selectedWidths (p : Walk E length) (W : α → ℕ) (A w J : ℕ)
    (hA : 1 ≤ A) (hend : A ^ J * w ≤ W p.finish) (i : ℕ) : ℕ :=
  if hi : i < J then W (p.selected W A w J hA hend ⟨i, hi⟩) else 0

theorem selectedWidths_bounds (p : Walk E length) (W : α → ℕ) (L A w J : ℕ)
    (hL : 1 ≤ L) (hA : 1 ≤ A) (hstart : W p.start = w) (hend : A ^ J * w ≤ W p.finish)
    (hstep : ∀ i : Fin length, W (p.vertex i.succ) ≤ L * W (p.vertex i.castSucc))
    (i : ℕ) (hi : i < J) :
    A ^ i * w ≤ p.selectedWidths W A w J hA hend i ∧
      p.selectedWidths W A w J hA hend i ≤ L * (A ^ i * w) := by
  simp only [selectedWidths, dif_pos hi]
  exact ⟨p.selected_lower W A w J hA hend ⟨i, hi⟩,
    p.selected_upper W L A w J hL hA hstart hend hstep ⟨i, hi⟩⟩

/-- Every later selected scale dominates every earlier scale by `A/L`. -/
theorem selected_gap (p : Walk E length) (W : α → ℕ) (L A w J : ℕ)
    (hL : 1 ≤ L) (hA : 1 ≤ A) (hstart : W p.start = w) (hend : A ^ J * w ≤ W p.finish)
    (hstep : ∀ i : Fin length, W (p.vertex i.succ) ≤ L * W (p.vertex i.castSucc))
    {i j : Fin J} (hij : i < j) :
    A * W (p.selected W A w J hA hend i) ≤ L * W (p.selected W A w J hA hend j) := by
  have hi := p.selected_upper W L A w J hL hA hstart hend hstep i
  have hj := p.selected_lower W A w J hA hend j
  have hp : A ^ (i.val + 1) ≤ A ^ j.val := Nat.pow_le_pow_right hA (by exact hij)
  have hlow : A * (A ^ i.val * w) ≤ W (p.selected W A w J hA hend j) := by
    calc
      _ = A ^ (i.val + 1) * w := by rw [pow_succ]; ring
      _ ≤ A ^ j.val * w := Nat.mul_le_mul_right w hp
      _ ≤ _ := hj
  exact (Nat.mul_le_mul_left A hi).trans (by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using Nat.mul_le_mul_left L hlow)

end Walk

/-- Neighboring widths obey the ratio bound once steep edges have been cut. -/
def EdgeScaleBound (E : α → α → Bool) (W : α → ℕ) (L : ℕ) : Prop :=
  ∀ x y, y ∈ neighbors E x → W y ≤ L * W x

theorem closed_neighbor_width (E : α → α → Bool) (W : α → ℕ) (L : ℕ)
    (hL : 1 ≤ L) (hscale : EdgeScaleBound E W L) (x y : α)
    (hy : y ∈ closedNeighbors E x) : W y ≤ L * W x := by
  by_cases hxy : y = x
  · subst y; simpa using Nat.mul_le_mul_right (W x) hL
  · apply hscale x y
    apply (mem_neighbors E x y).mpr
    refine ⟨hxy, ?_⟩
    exact ((mem_closedNeighbors E x y).mp hy).resolve_left hxy

/-- Every shortcut of length `r` changes widths by at most `L^r`. -/
theorem width_le_pow_of_mem_ball (E : α → α → Bool) (W : α → ℕ) (L : ℕ)
    (hL : 1 ≤ L) (hscale : EdgeScaleBound E W L) {x y : α} {r : ℕ}
    (hy : y ∈ ball E x r) : W y ≤ L ^ r * W x := by
  induction r generalizing x with
  | zero =>
    have hy' : y = x := by simpa only [ball_zero, Finset.mem_singleton] using hy
    subst y
    simp
  | succ r ih =>
    obtain ⟨z, hz, hyz⟩ := (mem_ball_succ E x y r).mp hy
    have hprev := ih hyz
    have hstep := closed_neighbor_width E W L hL hscale x z hz
    calc
      _ ≤ L ^ r * W z := hprev
      _ ≤ L ^ r * (L * W x) := Nat.mul_le_mul_left _ hstep
      _ = L ^ (r + 1) * W x := by rw [pow_succ]; ring

/-- A width gap larger than every possible short-path ratio proves actual
metric separation, even when the original selection path has shortcuts. -/
theorem not_mem_ball_of_gap (E : α → α → Bool) (W : α → ℕ) (L A r : ℕ)
    (hL : 1 ≤ L) (hscale : EdgeScaleBound E W L) (hgap : L ^ (r + 1) < A)
    {x y : α} (hx : 0 < W x) (hxy : A * W x ≤ L * W y) : y ∉ ball E x r := by
  intro hy
  have hpath := width_le_pow_of_mem_ball E W L hL hscale hy
  have hupper : L * W y ≤ L ^ (r + 1) * W x := by
    calc
      _ ≤ L * (L ^ r * W x) := Nat.mul_le_mul_left L hpath
      _ = _ := by rw [pow_succ]; ring
  have hlt := Nat.mul_lt_mul_of_pos_right hgap hx
  omega

/-- The concrete first-crossing labels are separated in the graph itself. -/
theorem selected_separated {E : α → α → Bool} {length : ℕ} (p : Walk E length)
    (W : α → ℕ) (L A w J r : ℕ) (hL : 1 ≤ L) (hA : 1 ≤ A) (hw : 0 < w)
    (hstart : W p.start = w) (hend : A ^ J * w ≤ W p.finish)
    (hscale : EdgeScaleBound E W L) (hgap : L ^ (r + 1) < A)
    {i j : Fin J} (hij : i < j) :
    p.selected W A w J hA hend j ∉ ball E (p.selected W A w J hA hend i) r := by
  have hstep : ∀ k : Fin length, W (p.vertex k.succ) ≤ L * W (p.vertex k.castSucc) :=
    fun k => closed_neighbor_width E W L hL hscale _ _ (p.step k)
  apply not_mem_ball_of_gap E W L A r hL hscale hgap
  · exact (Nat.mul_pos (pow_pos (by omega : 0 < A) _) hw).trans_le
      (p.selected_lower W A w J hA hend i)
  · exact p.selected_gap W L A w J hL hA hstart hend hstep hij

/-- In particular the selector produces `J` distinct reserved labels. -/
theorem selected_injective {E : α → α → Bool} {length : ℕ} (p : Walk E length)
    (W : α → ℕ) (L A w J r : ℕ) (hL : 1 ≤ L) (hA : 1 ≤ A) (hw : 0 < w)
    (hstart : W p.start = w) (hend : A ^ J * w ≤ W p.finish)
    (hscale : EdgeScaleBound E W L) (hgap : L ^ (r + 1) < A) :
    Function.Injective (p.selected W A w J hA hend) := by
  intro i j heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have h := selected_separated p W L A w J r hL hA hw hstart hend hscale hgap hij
    rw [← heq] at h
    exact h (center_mem_ball _ _ _)
  · have h := selected_separated p W L A w J r hL hA hw hstart hend hscale hgap hji
    rw [heq] at h
    exact h (center_mem_ball _ _ _)

theorem connected_symm {E : α → α → Bool} {x y : α} (h : Connected E x y) : Connected E y x := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, ball_symm E hr⟩

theorem connected_trans {E : α → α → Bool} {x y z : α}
    (hxy : Connected E x y) (hyz : Connected E y z) : Connected E x z := by
  obtain ⟨r, hr⟩ := hxy
  obtain ⟨s, hs⟩ := hyz
  exact ⟨r + s, mem_ball_add E hr hs⟩

theorem neighbors_nonempty_of_connected_ne {E : α → α → Bool} {x y : α}
    (h : Connected E x y) (hxy : y ≠ x) : (neighbors E x).Nonempty := by
  by_contra hn
  have hempty : neighbors E x = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hballs (r : ℕ) : ball E x r = {x} := by
    induction r with
    | zero => rfl
    | succ r ih => simp [ball, closedNeighbors, hempty, ih]
  obtain ⟨r, hr⟩ := h
  rw [hballs] at hr
  exact hxy (Finset.mem_singleton.mp hr)

/-- Every member of a concrete group of at least two distinct scales has an
actual old incident row. Such a reservation is eligible for incidence charging. -/
theorem selected_nonisolated {E : α → α → Bool} {length : ℕ} (p : Walk E length)
    (W : α → ℕ) (L A w J r : ℕ) (hL : 1 ≤ L) (hA : 1 ≤ A) (hw : 0 < w) (hJ : 2 ≤ J)
    (hstart : W p.start = w) (hend : A ^ J * w ≤ W p.finish)
    (hscale : EdgeScaleBound E W L) (hgap : L ^ (r + 1) < A) (i : Fin J) :
    (neighbors E (p.selected W A w J hA hend i)).Nonempty := by
  have hinj := selected_injective p W L A w J r hL hA hw hstart hend hscale hgap
  let j : Fin J := if i.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hji : j ≠ i := by
    intro heq
    have heq' := congrArg Fin.val heq
    by_cases hi : i.val = 0
    · simp [j, hi] at heq'
    · have h : 0 = i.val := by simpa [j, hi] using heq'
      omega
  have hiC : Connected E p.start (p.selected W A w J hA hend i) :=
    ⟨_, p.vertex_mem_ball _⟩
  have hjC : Connected E p.start (p.selected W A w J hA hend j) :=
    ⟨_, p.vertex_mem_ball _⟩
  exact neighbors_nonempty_of_connected_ne (connected_trans (connected_symm hiC) hjC)
    (fun h => hji (hinj h))

variable {n K : ℕ}

/-- A reserved label outside the height ball is incomparable in the numerical
closure, regardless of comparisons retired from a public order elsewhere. -/
theorem incomparable_of_separated (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ) (H : ℕ)
    (hstrict : ∀ x y, Arc E x y → rank x < rank y) (hheight : ∀ x, rank x + 1 ≤ H)
    (x y : Fin n) (hfar : y ∉ ball E x (2 * H)) :
    closure E x y = false ∧ closure E y x = false := by
  have hn : ¬ (closure E y x = true ∨ closure E x y = true) := by
    intro h
    have hh := comparable_mem_ball E rank H hstrict hheight h
    exact hfar (ball_mono E x (by omega : H - 1 ≤ 2 * H) hh)
  exact ⟨Bool.eq_false_iff.mpr (fun h => hn (Or.inr h)),
    Bool.eq_false_iff.mpr (fun h => hn (Or.inl h))⟩

/-- Pinning commutes with closing the unchanged row relation. -/
theorem closeSystem_pinAt (S : WeakSystem (Fin n) (K + 1)) (x : Fin n) (c : Fin (K + 1)) :
    closeSystem (pinAt S x c) = pinAt (closeSystem S) x c := rfl

/-- Pinning a numerical incomparable label changes neither effective endpoint
of a reserved label. This is the actual primitive pin operation. -/
theorem pin_windows_unchanged (S : WeakSystem (Fin n) (K + 1)) (x y : Fin n) (c : Fin (K + 1))
    (hxy : closure S.edge x y = false) (hyx : closure S.edge y x = false) :
    (closeSystem (pinAt S x c)).effectiveLower y = (closeSystem S).effectiveLower y ∧
    (closeSystem (pinAt S x c)).effectiveUpper y = (closeSystem S).effectiveUpper y := by
  rw [closeSystem_pinAt, pinAt_lower, pinAt_upper]
  simp [closeSystem, lookup_tableClosure, hxy, hyx]

/-- Repeated strictly interior scale pins need no palette changes. -/
def pinList (S : WeakSystem (Fin n) (K + 1)) : List (Fin n × Fin (K + 1)) → WeakSystem (Fin n) (K + 1)
  | [] => S
  | (x, c) :: rest => pinList (pinAt S x c) rest

theorem pinList_edges (S : WeakSystem (Fin n) (K + 1)) (pins : List (Fin n × Fin (K + 1))) :
    (pinList S pins).edge = S.edge := by
  induction pins generalizing S with
  | nil => rfl
  | cons p pins ih => exact ih (pinAt S p.1 p.2)

/-- Every reserved label incomparable to all earlier choices retains both
original effective endpoints throughout the entire actual pin prefix. -/
theorem pinList_windows_unchanged (S : WeakSystem (Fin n) (K + 1))
    (pins : List (Fin n × Fin (K + 1))) (y : Fin n)
    (haway : ∀ p ∈ pins, closure S.edge p.1 y = false ∧ closure S.edge y p.1 = false) :
    (closeSystem (pinList S pins)).effectiveLower y = (closeSystem S).effectiveLower y ∧
    (closeSystem (pinList S pins)).effectiveUpper y = (closeSystem S).effectiveUpper y := by
  induction pins generalizing S with
  | nil => exact ⟨rfl, rfl⟩
  | cons p pins ih =>
    have hfirst := haway p (List.mem_cons_self ..)
    have hpin := pin_windows_unchanged S p.1 y p.2 hfirst.1 hfirst.2
    have hrest := ih (pinAt S p.1 p.2) (fun q hq => haway q (List.mem_cons_of_mem p hq))
    exact ⟨hrest.1.trans hpin.1, hrest.2.trans hpin.2⟩

/-- The explicit separation parameter from the manuscript. -/
def scaleBase (J L H : ℕ) : ℕ := 128 * J * (L + 1) ^ (2 * H + 3)

theorem scaleBase_gap (J L H : ℕ) (hJ : 0 < J) : L ^ (2 * H + 1) < scaleBase J L H := by
  have hp : L ^ (2 * H + 1) ≤ (L + 1) ^ (2 * H + 3) := by
    exact (Nat.pow_le_pow_left (Nat.le_succ L) _).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hpos : 0 < (L + 1) ^ (2 * H + 3) := pow_pos (Nat.succ_pos L) _
  unfold scaleBase
  nlinarith

end SortingAdversary.Optimal.ScaleGeometry
