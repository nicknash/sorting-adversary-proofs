import SortingAdversary.Continuous.PolylogExecution

/-!
# The uniform-block cache on reachable states

A heap extension preserves the original lookup closure. The closure supplied
at initialization reads one existing array cell and selects its zero or
one component. Selection, recording, repair and freezing all preserve it.
-/

namespace SortingAdversary.Continuous.PolylogCacheReads

open PolylogBits PolylogExecution PolylogCompare
open Optimal.PrimitiveWork (Result)
variable {n t b : ℕ}

/-- One indexed word-pair read, a Boolean test and one projection. -/
def read (A : Array (ℕ × ℕ)) (d : ℕ) (one : Bool) : Result ℕ :=
  let p := A[d]!
  ⟨if one then p.2 else p.1, 3⟩

theorem initial_lookup (n t b D : ℕ) :
    (initialMemory n t b D).cache.lookup = (initializeCache blockStore b).cache.lookup := rfl

theorem move_lookup (k : ℕ) (m : Memory n t b) (x : Fin n) (w : WriteResult m) :
    (move k m x w).value.cache.lookup = m.cache.lookup := rfl

private theorem select_lookup (D : ℕ) (P : PolylogPrepared.Params) (q : Query n)
    (f : ℕ) (m m' : Memory n t b) (a : Answer)
    (h : (PolylogCached.select D P q f m).value = some (m',a)) :
    m'.cache.lookup = m.cache.lookup := by
  induction f generalizing m with
  | zero => simp [PolylogCached.select] at h
  | succ f ih =>
    rw [PolylogCached.select] at h
    split at h
    · cases h
      rfl
    · exact (ih _ h).trans (move_lookup ..)

private theorem repair_lookup (D : ℕ) (P : PolylogPrepared.Params) (xs : List (Fin n))
    (m : Memory n t b) : (PolylogCached.repairList D P xs m).value.cache.lookup = m.cache.lookup := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih =>
    change (PolylogCached.repairList D P xs (PolylogCached.repairMove D P m x).value).value.cache.lookup = _
    exact (ih _).trans (move_lookup ..)

theorem compare_lookup (D : ℕ) (P : PolylogPrepared.Params) (q : Query n)
    (m m' : Memory n t b) (a : Answer)
    (h : (PolylogCached.compare D P m q).value = some (m',a)) :
    m'.cache.lookup = m.cache.lookup := by
  rw [PolylogCached.compare] at h
  split at h
  · contradiction
  · rename_i v ans hv
    cases h
    exact (repair_lookup ..).trans (select_lookup D P q 3 m v _ hv)

/-- The state contains the same initialized array for the whole run. -/
def HasCache {c : Config} : State n c → Prop
  | .fallback => True
  | .active _ m | .frozen m => m.cache.lookup = (initializeCache blockStore c.blocks).cache.lookup

theorem start_cache (c : Config) : HasCache (start n c) := by
  unfold start
  split
  · exact initial_lookup ..
  · trivial

theorem step_cache (c : Config) (s : State n c) (q : Query n) (h : HasCache s) :
    HasCache ((step c s q).value.2) := by
  cases s with
  | fallback => trivial
  | frozen m => exact h
  | active fuel m =>
    cases fuel with
    | zero => exact h
    | succ f =>
      simp only [step]
      split
      · exact h
      · rename_i m' a eq
        exact (compare_lookup _ _ q _ _ a eq).trans h

theorem replay_cache (c : Config) (history : History n) : HasCache (replay c history) := by
  induction history with
  | nil => exact start_cache _
  | cons o hist ih => exact step_cache _ _ o.query ih

/-- Every legal online cache access has the value of the stored handle at
that height and uses three word operations, independent of graph and heap size. -/
theorem replay_array (c : Config) (history : History n) (m : Memory n c.tables c.blocks)
    (live : (∃ fuel, replay c history = .active fuel m) ∨ replay c history = .frozen m)
    (d : ℕ) (hd : d ≤ c.blocks) (one : Bool) :
    let A := (initializeCache blockStore c.blocks).table
    d < A.size ∧ (read A d one).value = m.cache.lookup d one ∧
      (read A d one).work = 3 ∧ Represents blockStore m.heap (read A d one).value (filled blockStore d one) := by
  have h := replay_cache c history
  have he : m.cache.lookup = (initializeCache blockStore c.blocks).cache.lookup := by
    rcases live with ⟨fuel, st⟩ | st <;> rw [st] at h <;> exact h
  have hv : (read (initializeCache blockStore c.blocks).table d one).value = m.cache.lookup d one := by
    rw [he]
    rfl
  exact ⟨(initializeCache blockStore c.blocks).size ▸ Nat.lt_succ_of_le hd, hv, rfl,
    hv.symm ▸ m.cache.spec hd one⟩

end SortingAdversary.Continuous.PolylogCacheReads
