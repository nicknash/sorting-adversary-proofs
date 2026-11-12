import SortingAdversary.Continuous.RefinementBatch
import SortingAdversary.Optimal.GraphBalls
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Chain
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# The deterministic path choice used by repair

Paths are generated along actual outgoing adjacency lists and the least
one in lexicographic order is selected. Under the degree bound the list has
at most `n * d^(H-1)` entries. Its dependence on the ambient input size is
linear; the large remaining factor depends only on the sparsity parameter.
-/

namespace SortingAdversary.Continuous.GraphPaths

open SortingAdversary.Optimal.GraphBalls

variable {n : ℕ}

def outgoing (E : Fin n → Fin n → Bool) (x : Fin n) : List (Fin n) :=
  (List.finRange n).filter (E x)

@[simp] theorem mem_outgoing (E : Fin n → Fin n → Bool) (x y : Fin n) :
    y ∈ outgoing E x ↔ E x y = true := by simp [outgoing]

/-- The tails containing exactly `h` further vertices after `x`. -/
def pathsFrom (E : Fin n → Fin n → Bool) : ℕ → Fin n → List (List (Fin n))
  | 0, _ => [[]]
  | h + 1, x => (outgoing E x).flatMap fun y => (pathsFrom E h y).map (y :: ·)

def paths (E : Fin n → Fin n → Bool) : ℕ → List (List (Fin n))
  | 0 => [[]]
  | h + 1 => (List.finRange n).flatMap fun x => (pathsFrom E h x).map (x :: ·)

def firstPath (E : Fin n → Fin n → Bool) (H : ℕ) : Option (List (Fin n)) :=
  (paths E H).min?

theorem mem_pathsFrom (E : Fin n → Fin n → Bool) (h : ℕ) (x : Fin n)
    (p : List (Fin n)) :
    p ∈ pathsFrom E h x ↔ p.length = h ∧ (x :: p).IsChain (fun a b => E a b = true) := by
  induction h generalizing x p with
  | zero => cases p <;> simp [pathsFrom]
  | succ h ih =>
    cases p with
    | nil => simp [pathsFrom]
    | cons y p =>
      simp only [pathsFrom, List.mem_flatMap, List.mem_map, List.cons.injEq,
        mem_outgoing, List.length_cons, Nat.add_right_cancel_iff, List.isChain_cons_cons]
      constructor
      · rintro ⟨z, hz, q, hq, hzy, hqp⟩
        subst z
        subst q
        exact ⟨(ih y p).mp hq |>.1, hz, (ih y p).mp hq |>.2⟩
      · rintro ⟨hlen, hxy, hp⟩
        exact ⟨y, hxy, p, (ih y p).mpr ⟨hlen, hp⟩, rfl, rfl⟩

theorem mem_paths (E : Fin n → Fin n → Bool) (H : ℕ) (p : List (Fin n)) :
    p ∈ paths E H ↔ p.length = H ∧ p.IsChain (fun a b => E a b = true) := by
  cases H with
  | zero => cases p <;> simp [paths]
  | succ h =>
    cases p with
    | nil => simp [paths]
    | cons x p =>
      simp [paths, List.mem_flatMap, mem_pathsFrom]

/-- The result is precisely the lexicographically first directed path with
the requested number of vertices. -/
theorem firstPath_some (E : Fin n → Fin n → Bool) (H : ℕ) (p : List (Fin n))
    (hp : firstPath E H = some p) :
    p.length = H ∧ p.IsChain (fun a b => E a b = true) ∧
      ∀ q, q.length = H → q.IsChain (fun a b => E a b = true) → p ≤ q := by
  have h := List.min?_eq_some_iff.mp hp
  have hmem := (mem_paths E H p).mp h.1
  exact ⟨hmem.1, hmem.2, fun q hlen hq => h.2 q ((mem_paths E H q).mpr ⟨hlen, hq⟩)⟩

theorem firstPath_none (E : Fin n → Fin n → Bool) (H : ℕ) :
    firstPath E H = none ↔
      ∀ p : List (Fin n), p.IsChain (fun a b => E a b = true) → p.length ≠ H := by
  rw [firstPath, List.min?_eq_none_iff]
  constructor
  · intro he p hp hlen
    have hm := (mem_paths E H p).mpr ⟨hlen, hp⟩
    simp [he] at hm
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro p hp
    have hm := (mem_paths E H p).mp hp
    exact h p hm.2 hm.1

theorem path_nodup (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ)
    (hrank : ∀ x y, E x y = true → rank x < rank y)
    {p : List (Fin n)} (hp : p.IsChain (fun a b => E a b = true)) : p.Nodup := by
  letI : Trans (fun x y : Fin n => rank x < rank y)
      (fun x y : Fin n => rank x < rank y)
      (fun x y : Fin n => rank x < rank y) := ⟨Nat.lt_trans⟩
  have hh := List.isChain_iff_pairwise.mp (hp.imp (fun x y h => hrank x y h))
  apply List.nodup_iff_pairwise_ne.mpr
  exact hh.imp (fun h heq => by simpa [heq] using h)

theorem outgoing_length_le (E : Fin n → Fin n → Bool) (d : ℕ)
    (hloop : ∀ x, E x x = false) (hdegree : ∀ x, (neighbors E x).card ≤ d)
    (x : Fin n) : (outgoing E x).length ≤ d := by
  have hn : (outgoing E x).Nodup := (List.nodup_finRange n).filter _
  have hs : (outgoing E x).toFinset ⊆ neighbors E x := by
    intro y hy
    have he := (mem_outgoing E x y).mp (List.mem_toFinset.mp hy)
    refine (mem_neighbors E x y).mpr ⟨?_, Or.inl he⟩
    intro h
    subst y
    simp [hloop x] at he
  rw [← List.toFinset_card_of_nodup hn]
  exact (Finset.card_le_card hs).trans (hdegree x)

private theorem sum_map_le {α : Type*} (L : List α) (f : α → ℕ) (b : ℕ)
    (hf : ∀ x ∈ L, f x ≤ b) : (L.map f).sum ≤ L.length * b := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    have hx := hf x (by simp)
    have ht := ih (fun y hy => hf y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem pathsFrom_length_le (E : Fin n → Fin n → Bool) (d : ℕ)
    (hloop : ∀ x, E x x = false) (hdegree : ∀ x, (neighbors E x).card ≤ d)
    (h : ℕ) (x : Fin n) : (pathsFrom E h x).length ≤ d ^ h := by
  induction h generalizing x with
  | zero => simp [pathsFrom]
  | succ h ih =>
    simp only [pathsFrom, List.length_flatMap, List.length_map]
    calc
      _ ≤ (outgoing E x).length * d ^ h := sum_map_le _ _ _ (fun y _ => ih y)
      _ ≤ d * d ^ h := Nat.mul_le_mul_right _ (outgoing_length_le E d hloop hdegree x)
      _ = d ^ (h + 1) := by rw [pow_succ, Nat.mul_comm]

theorem paths_length_le (E : Fin n → Fin n → Bool) (d : ℕ)
    (hloop : ∀ x, E x x = false) (hdegree : ∀ x, (neighbors E x).card ≤ d)
    (h : ℕ) : (paths E (h + 1)).length ≤ n * d ^ h := by
  simp only [paths, List.length_flatMap, List.length_map]
  simpa using sum_map_le (List.finRange n) (fun x => (pathsFrom E h x).length) (d ^ h)
    (fun x _ => pathsFrom_length_le E d hloop hdegree h x)

end SortingAdversary.Continuous.GraphPaths
