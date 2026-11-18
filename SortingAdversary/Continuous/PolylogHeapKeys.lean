import SortingAdversary.Continuous.PolylogExecution
import SortingAdversary.Continuous.PolylogWordWork

/-!
# Word widths of keys in the two interning dictionaries

Interning at height d installs a key with tag d and two child addresses.
Beginning at the empty dictionaries, no zero-tag record is ever inserted.
The same tag bound holds inside a carry walk and on disposable probe heaps.
Typing gives the allocation bound for both children of every stored key.
-/

namespace SortingAdversary.Continuous.PolylogHeapKeys

open PolylogBits PolylogCompare PolylogExecution
open PolylogRawBits (Output)
variable {n t b cap : ℕ} {H : Heap} {S : Store}

def Tagged (H : Heap) (cap : ℕ) : Prop :=
  ∀ (i : ℕ) (k : Key), H.record[i]? = some k → 0 < k.1 ∧ k.1 ≤ cap

theorem Tagged.mono {B : ℕ} (tag : Tagged H cap) (inc : cap ≤ B) : Tagged H B :=
  fun i k e => ⟨(tag i k e).1,(tag i k e).2.trans inc⟩

theorem Tagged.intern (tag : Tagged H cap) (k : Key) (pos : 0 < k.1) (bound : k.1 ≤ cap) :
    Tagged (H.intern k).1 cap := by
  intro i x hx
  unfold Heap.intern at hx
  split at hx
  · exact tag _ _ hx
  · simp only [Std.TreeMap.getElem?_insert] at hx
    split at hx
    · exact Option.some.inj hx ▸ ⟨pos,bound⟩
    · exact tag _ _ hx

private theorem truncate_tag (table : PolylogRawBits.Table) (tag : Tagged H cap) {h : ℕ}
    (p : Position h) (lim : h ≤ cap) (i : ℕ) : Tagged (PolylogRawBits.truncate table H p i).heap cap := by
  induction p generalizing i with
  | here => exact tag
  | high p ih | low p ih => exact (ih (by omega) _).intern _ (Nat.succ_pos _) lim

private theorem bump_tag (table : PolylogRawBits.Table) (tag : Tagged H cap) (h i : ℕ)
    (lim : h ≤ cap) : Tagged (PolylogRawBits.bump table H h i).heap cap := by
  induction h generalizing i with
  | zero => exact tag
  | succ h ih =>
    simp only [PolylogRawBits.bump]
    split <;> exact (ih _ (by omega)).intern _ (Nat.succ_pos _) lim

theorem add_tag (table : PolylogRawBits.Table) (tag : Tagged H cap) {h : ℕ}
    (p : Position h) (lim : h ≤ cap) (i : ℕ) : Tagged (PolylogRawBits.addUnit table H p i).1.heap cap := by
  induction p generalizing i with
  | here => exact tag
  | high p ih => exact (ih (by omega) _).intern _ (Nat.succ_pos _) lim
  | @low h p ih =>
    have smaller : h ≤ cap := by omega
    have prev := ih smaller (H.children i).2
    simp only [PolylogRawBits.addUnit]
    split
    · split
      · exact prev.intern _ (Nat.succ_pos _) lim
      · exact (bump_tag table prev h _ smaller).intern _ (Nat.succ_pos _) lim
    · exact prev.intern _ (Nat.succ_pos _) lim

private theorem advance_tag (table : PolylogRawBits.Table) (tag : Tagged H cap) {h : ℕ}
    (p : Position h) (lim : h ≤ cap) (i j : ℕ) : Tagged (PolylogRawBits.advance table H p i j).heap cap := by
  induction j with
  | zero => exact tag
  | succ j ih => exact add_tag table ih p lim _

theorem fallback_tag (v : H.Valid) (typed : H.Typed) (cache : Cached S H cap) (D F l r : ℕ)
    {h : ℕ} (lim : h ≤ cap) (tag : Tagged H cap) :
    Tagged (PolylogRawAnchor.fallback D F v typed cache lim l r).heap cap := by
  unfold PolylogRawAnchor.fallback
  split
  · exact advance_tag cache.lookup (truncate_tag cache.lookup tag _ lim l) _ lim _ _
  · exact tag

private theorem emit_tag (v : H.Valid) (cache : Cached S H cap) {h : ℕ} (lim : h ≤ cap)
    (tag : Tagged H cap) (len off z : ℕ) : Tagged (PolylogEmbed.emit v cache lim len off z).heap cap := by
  induction len generalizing off z with
  | zero => exact tag
  | succ len ih =>
    simp only [PolylogEmbed.emit]
    split
    · exact add_tag cache.lookup (ih (off+1) (z/2)) _ lim _
    · exact ih _ _

private theorem cache_tag (S : Store) (b : ℕ) : Tagged (initializeCache S b).heap b := by
  induction b with
  | zero =>
    intro i k e
    change (Heap.empty.record[i]?) = some k at e
    simp [Heap.empty] at e
  | succ d ih =>
    exact ((ih.mono (Nat.le_succ d)).intern _ (Nat.succ_pos d) (le_refl _)).intern _
      (Nat.succ_pos d) (le_refl _)

theorem initial_tag (n t b D : ℕ) : Tagged (initialMemory n t b D).heap b :=
  emit_tag _ _ (le_refl b) (cache_tag blockStore b) _ _ _

theorem prefix_tag (D : ℕ) (m : Memory n t b) (tag : Tagged m.heap b) (x : Fin n) :
    Tagged (writePrefix D m x).out.heap b :=
  fallback_tag m.valid m.typed m.cache _ _ _ _ (le_refl b) tag

theorem mint_tag (D : ℕ) (m : Memory n t b) (tag : Tagged m.heap b) (x : Fin n) (test : Option ℚ) :
    Tagged (mint D m x test).out.heap b := by
  cases test with
  | none => exact prefix_tag D m tag x
  | some _ => exact emit_tag _ _ (le_refl b) tag _ _ _

private theorem select_tag (D : ℕ) (P : PolylogPrepared.Params) (q : Query n) (f : ℕ)
    (m u : Memory n t b) (a : Answer) (tag : Tagged m.heap b)
    (sel : (PolylogCached.select D P q f m).value = some (u,a)) : Tagged u.heap b := by
  induction f generalizing m with
  | zero => simp [PolylogCached.select] at sel
  | succ f ih =>
    rw [PolylogCached.select] at sel
    split at sel
    · cases sel; exact tag
    · exact ih _ (prefix_tag D m tag _) sel

private theorem repair_tag (D : ℕ) (P : PolylogPrepared.Params) (xs : List (Fin n))
    (m : Memory n t b) (tag : Tagged m.heap b) :
    Tagged (PolylogCached.repairList D P xs m).value.heap b := by
  induction xs generalizing m with
  | nil => exact tag
  | cons x xs ih => exact ih _ (mint_tag D m tag x _)

theorem compare_tag (D : ℕ) (P : PolylogPrepared.Params) (q : Query n) (m u : Memory n t b)
    (a : Answer) (tag : Tagged m.heap b) (ok : (PolylogCached.compare D P m q).value = some (u,a)) :
    Tagged u.heap b := by
  rw [PolylogCached.compare] at ok
  split at ok
  · contradiction
  · rename_i v ans s
    cases ok
    exact repair_tag _ _ _ _ (select_tag D P q 3 m v _ tag s)

def Good {c : Config} : State n c → Prop
  | .fallback => True
  | .active _ m | .frozen m => Tagged m.heap c.blocks

theorem replay_tag (c : Config) (hist : History n) : Good (replay c hist) := by
  induction hist with
  | nil =>
    simp only [replay,start]
    split
    · exact initial_tag n c.tables c.blocks c.binaryPoint
    · trivial
  | cons o h ih =>
    simp only [replay]
    generalize eq : replay c h = state at ih ⊢
    cases state with
    | fallback => trivial
    | frozen => exact ih
    | active fuel m =>
      cases fuel with
      | zero => exact ih
      | succ f =>
        simp only [step]
        split
        · exact ih
        · rename_i u a ok
          exact compare_tag _ _ _ _ _ a ih ok

/-- The tag is bounded by the block height. Each child appearing as a
forward-map key component or inverse-map record is below the allocator. -/
theorem stored_key {m : Memory n t b} (tag : Tagged m.heap b) (i : ℕ) (k : Key)
    (hit : m.heap.record[i]? = some k) :
    0 < k.1 ∧ k.1 ≤ b ∧ i < m.heap.next ∧ k.2.1 < m.heap.next ∧ k.2.2 < m.heap.next := by
  obtain ⟨p,bound⟩ := tag i k hit
  refine ⟨p,bound,(m.valid.bounds i k hit).2,?_⟩
  obtain ⟨a,l,r⟩ := k
  cases a with
  | zero => exact False.elim (by exact Nat.not_lt_zero _ p)
  | succ a =>
    obtain ⟨v,rv⟩ := m.typed blockStore a i l r hit
    cases rv with
    | node fetch left right =>
      have eq := Option.some.inj (fetch.symm.trans hit)
      cases eq
      exact ⟨PolylogResources.represented_address m.valid left,PolylogResources.represented_address m.valid right⟩

/-- Each component compared in the forward or inverse dictionary fits in
the fixed table word, at every online query boundary including freezing. -/
theorem replay_key_width (active : ActiveRefinement n) (hist : History n) (m : Mem n)
    (live : (∃ f, replay (config n) hist = .active f m) ∨ replay (config n) hist = .frozen m)
    (i : ℕ) (k : Key) (hit : m.heap.record[i]? = some k ∨ m.heap.address[k]? = some i) :
    i.size ≤ PolylogResources.tableHeight n ∧ k.1.size ≤ PolylogResources.tableHeight n ∧
      k.2.1.size ≤ PolylogResources.tableHeight n ∧ k.2.2.size ≤ PolylogResources.tableHeight n := by
  have tag := replay_tag (config n) hist
  have tagged : Tagged m.heap (config n).blocks := by
    rcases live with ⟨_,e⟩ | e <;> rw [e] at tag <;> exact tag
  have entry := stored_key tagged i k (hit.elim id (m.valid.inverse k i).mp)
  have bounds {M : Controller.Memory n} (hk : 64 ≤ (config n).k) (s : Stores m M)
      (depth : Controller.totalDepth M ≤ Controller.horizon n) :
      m.heap.next < 2^PolylogResources.tableHeight n ∧
      (config n).blocks < 2^PolylogResources.tableHeight n := by
    have cap := PolylogSchedule.capacity_bits (extra := PolylogAdversary.extra) hk (le_refl (Optimal.Parameters.logCap n))
    change (config n).blocks ≤ 5+(Optimal.Parameters.logCap n+1)*3 at cap
    have room := (PolylogResources.indices_fit s.aligned.sized cap (by omega)).2
    refine ⟨(Nat.le_add_right ..).trans_lt room,?_⟩
    apply lt_of_le_of_lt _ (Nat.lt_two_pow_self (n := PolylogResources.tableHeight n))
    dsimp only [PolylogResources.tableHeight]; omega
  have rel := replay_relates active hist
  generalize eq : (PolylogAdversary.policy n).replay (config n).k hist = state at rel
  have both := show m.heap.next < 2^PolylogResources.tableHeight n ∧
      (config n).blocks < 2^PolylogResources.tableHeight n from by
    rcases live with ⟨_,e⟩ | e <;> rw [e] at rel
    · cases rel with
      | active hk good => exact bounds hk good (PolylogResources.replay_refinements hk hist eq)
    · cases rel with
      | frozen hk good hd => exact bounds hk good hd
  exact ⟨Nat.size_le.mpr (entry.2.2.1.trans both.1), Nat.size_le.mpr (entry.2.1.trans_lt both.2),
    Nat.size_le.mpr (entry.2.2.2.1.trans both.1), Nat.size_le.mpr (entry.2.2.2.2.trans both.1)⟩

end SortingAdversary.Continuous.PolylogHeapKeys
