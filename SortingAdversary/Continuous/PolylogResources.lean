import SortingAdversary.Continuous.PolylogEmbed
import SortingAdversary.Continuous.PolylogPrecision
import SortingAdversary.Continuous.PolylogDictionary
import SortingAdversary.Continuous.PolylogStorage
import SortingAdversary.Continuous.ControllerResources

/-!
# Address capacity of the sparse adversary

The hierarchy allocates at most one node per refinement. Its canonical
block heap grows by the number of blocks used by the selected writer.
We reserve a fixed height for the label, child, and ancestor tables before
the first comparison. This height covers temporary allocations as well
as the persistent state through the freezing horizon.
-/

namespace SortingAdversary.Continuous.PolylogResources

open Controller PolylogBits
open Optimal.Parameters (logCap)

variable {n t b cap : ℕ} {S : Store} {H : Heap}

def perMove (A b : ℕ) : ℕ := max (7*b) (1+(A+1)*((b+1)^2+10*b+6))

/-- One spare writer allowance covers the initial representation of one. -/
structure Sized (A b m : ℕ) (dir : PolylogHierarchy.Store t) (heap : Heap) : Prop where
  directory : dir.next ≤ 1+m
  blocks : heap.next ≤ 2*b+2+(m+1)*perMove A b

def tableHeight (n : ℕ) := 13 + 6*(logCap n + 1)

theorem initialized (S : Store) (A b D t : ℕ) :
    let I := initializeCache S b
    Sized A b 0 (PolylogHierarchy.empty t)
      (PolylogEmbed.embedAddr D 0 1 I.valid I.cache (le_refl b)).heap := by
  let I := initializeCache S b
  let w := PolylogEmbed.embedAddr D 0 1 I.valid I.cache (le_refl b)
  have hw := PolylogEmbed.embedAddr_work D 0 1 I.valid I.cache (le_refl b)
  have bound : w.work ≤ perMove A b := by
    apply le_trans hw
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ (show 0+1 ≤ A+1 by omega)) _).trans
      (le_max_right ..)
  constructor
  · exact le_rfl
  · simpa using w.allocated.trans (Nat.add_le_add I.allocated bound)

/-- The actual two storage updates advance the count by one. -/
theorem sized_move {A m : ℕ} {s : PolylogStorage.State n t} (sz : Sized A b m s.directory H)
    (x : Fin n) (c : ℕ) {out : Heap} (hw : out.next ≤ H.next + perMove A b) :
    Sized A b (m+1) (PolylogStorage.moveCursor s x c).value.directory out := by
  constructor
  · have hh := (PolylogHierarchy.adds_at_most_one s.directory (s.locations.get x.val).value c).2
    change _ ≤ 1+(m+1)
    exact hh.trans (by have := sz.directory; omega)
  · have hh := sz.blocks
    rw [Nat.succ_mul (m+1)]
    omega

theorem perMove_le {A b : ℕ} (hb : b ≤ 5+(A+1)*3) : perMove A b ≤ 200*(A+1)^3 := by
  apply max_le
  · nlinarith [Nat.zero_le (A^3), Nat.zero_le (A^2)]
  · have h := Nat.mul_le_mul_left (A+1) (Nat.add_le_add_right (Nat.add_le_add
      (Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) 2) (Nat.mul_le_mul_left 10 hb)) 6)
    nlinarith [Nat.zero_le (A^3), Nat.zero_le (A^2)]

/-- An extra writer allowance includes transient sums in the binary search
and the block that will be passed to the directory in the current move. -/
theorem space_envelope {m : ℕ} {dir : PolylogHierarchy.Store t}
    (sz : Sized (logCap n) b m dir H) (hb : b ≤ 5+(logCap n+1)*3)
    (hm : m ≤ horizon n + logCap n + 2) :
    let L := logCap n+1
    dir.next ≤ 4*(n+1)*L ∧ H.next+perMove (logCap n) b ≤ 4096*(n+1)*L^4 := by
  let L := logCap n+1
  have hp : 1 ≤ L := by dsimp [L]; omega
  have hq := PolylogSchedule.horizon_le n
  have hm' : m+2 ≤ 4*(n+1)*L := by dsimp [L] at *; nlinarith
  change dir.next ≤ 4*(n+1)*L ∧ _
  refine ⟨by have := sz.directory; omega, ?_⟩
  have hw := perMove_le hb
  have hh := sz.blocks
  have hmul := Nat.mul_le_mul hm' hw
  rw [Nat.succ_mul (m+1)] at hmul
  have hsmall : 2*b+2 ≤ 18*(n+1)*L^4 := by
    have h1 : L ≤ L^4 := by exact Nat.le_self_pow (by decide) _
    have h2 : L^4 ≤ (n+1)*L^4 := Nat.le_mul_of_pos_left _ (by omega)
    have h3 : 18*((n+1)*L^4) = 18*(n+1)*L^4 := by ring
    rw [← h3]
    change b ≤ 5+L*3 at hb
    omega
  change _ ≤ 4096*(n+1)*L^4
  change _ ≤ 4*(n+1)*L*(200*L^3) at hmul
  calc
    _ ≤ 2*b+2 + 4*(n+1)*L*(200*L^3) := by omega
    _ ≤ 18*(n+1)*L^4 + 4*(n+1)*L*(200*L^3) := Nat.add_le_add_right hsmall _
    _ ≤ _ := by ring_nf; omega

theorem envelope_fits (n : ℕ) : 4096*(n+1)*(logCap n+1)^4 < 2^tableHeight n := by
  let L := logCap n+1
  have hn : n+1 ≤ 2^L := (Nat.lt_pow_succ_log_self (by decide) (n+1)).le
  have hl : L ≤ 2^L := Nat.lt_two_pow_self.le
  have hh := Nat.mul_le_mul (Nat.mul_le_mul_left 4096 hn) (Nat.pow_le_pow_left hl 4)
  apply hh.trans_lt
  calc
    4096 * 2^L * (2^L)^4 = 2^(12+L*5) := by
      rw [pow_add 2 12, pow_mul 2 L]; ring
    _ < 2^tableHeight n := Nat.pow_lt_pow_right (by decide) (by dsimp [tableHeight, L]; omega)

theorem label_fits (n : ℕ) : n ≤ 2^tableHeight n := by
  exact (Nat.le_succ n).trans <| (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n+1)).le.trans <|
    Nat.pow_le_pow_right (by decide) (by dsimp [tableHeight, Optimal.Parameters.logCap]; omega)

theorem indices_fit {m : ℕ} {dir : PolylogHierarchy.Store t}
    (sz : Sized (logCap n) b m dir H) (hb : b ≤ 5+(logCap n+1)*3)
    (hm : m ≤ horizon n + logCap n + 2) :
    dir.next < 2^tableHeight n ∧ H.next+perMove (logCap n) b < 2^tableHeight n := by
  obtain ⟨dd,hh⟩ := space_envelope sz hb hm
  refine ⟨dd.trans_lt (lt_of_le_of_lt ?_ (envelope_fits n)), hh.trans_lt (envelope_fits n)⟩
  have h : logCap n+1 ≤ (logCap n+1)^4 := Nat.le_self_pow (by decide) _
  exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (by decide)) h

theorem represented_address {z : S.Ref b} {i : ℕ} (v : H.Valid) (rep : Represents S H i z) :
    i < H.next := by
  cases rep with
  | leaf d => have := v.reserved; cases d <;> simp <;> omega
  | node hi _ _ => exact (v.bounds _ _ hi).2

/-- Distinct prefix lengths give distinct directory entries. -/
theorem prefix_count {u : PolylogHierarchy.Cursor t} {nodes : List (List ℕ)} {p : List ℕ}
    (h : u.At nodes p) : p.length+1 ≤ nodes.length := by
  have count := Finset.card_le_card_of_injOn (s := Finset.range (p.length+1)) (t := nodes.toFinset)
    (fun i => p.take i) (by
      intro i hi; exact List.mem_toFinset.mpr (h.2.mem i (by simpa using Finset.mem_range.mp hi)))
    (by
      intro i hi j hj he
      have h1 : i ≤ p.length := by simpa using Finset.mem_range.mp hi
      have h2 : j ≤ p.length := by simpa using Finset.mem_range.mp hj
      simpa only [List.length_take, Nat.min_eq_left h1, Nat.min_eq_left h2] using congrArg List.length he)
  simpa only [Finset.card_range] using count.trans nodes.toFinset_card_le

/-- Bounds for the exact indices used by the stored mutation, including a
new block in the output heap and the ancestor row's next depth. -/
theorem move_indices {m : ℕ} {s : PolylogStorage.State n (tableHeight n)} {nodes : List (List ℕ)}
    {M : Memory n} {decode : ℕ → ℚ} (hs : PolylogStorage.Represents s nodes M decode)
    (sz : Sized (logCap n) b m s.directory H) (hb : b ≤ 5+(logCap n+1)*3)
    (hm : m ≤ horizon n + logCap n + 2) (x : Fin n) {out : Heap} (v : out.Valid)
    (hw : out.next ≤ H.next+perMove (logCap n) b) {c : ℕ} {z : S.Ref b}
    (hc : Represents S out c z) :
    c < 2^tableHeight n ∧ s.directory.next < 2^tableHeight n ∧
      (M.tree.location x).length+1 < 2^tableHeight n := by
  obtain ⟨dir, blocks⟩ := indices_fit sz hb hm
  refine ⟨(represented_address v hc).trans (hw.trans_lt blocks), dir, ?_⟩
  obtain ⟨p, hp, hmap⟩ := hs.located x
  rw [← hmap, List.length_map]
  rw [hs.directory.count] at dir
  exact (prefix_count hp).trans_lt dir

/-- A move using a fresh canonical address satisfies the table's actual domain
restrictions, even when made partway through a reserved path. -/
theorem moveCursor_safe {m : ℕ} {s : PolylogStorage.State n (tableHeight n)} {nodes : List (List ℕ)}
    {M : Memory n} {decode : ℕ → ℚ} (hs : PolylogStorage.Represents s nodes M decode)
    (sz : Sized (logCap n) b m s.directory H) (hb : b ≤ 5+(logCap n+1)*3)
    (hm : m ≤ horizon n + logCap n + 2) (x : Fin n) {out : Heap} (v : out.Valid)
    (hw : out.next ≤ H.next+perMove (logCap n) b) {c : ℕ} {z : S.Ref b}
    (hc : Represents S out c z) :
    let st := (PolylogStorage.moveCursor s x c).value
    ∃ more : List (List ℕ), more.length ≤ 1 ∧ PolylogHierarchy.Valid st.directory (nodes ++ more) ∧
      ∀ y : Fin n, ∃ p : List ℕ, (st.locations.get y.val).value.At (nodes ++ more) p ∧
        p.map decode = if y = x then M.tree.location x ++ [decode c] else M.tree.location y := by
  obtain ⟨addr, room, depth⟩ := move_indices hs sz hb hm x v hw hc
  exact PolylogStorage.moveCursor_spec hs (label_fits n) x c addr room depth

/-- Balanced hash-cons dictionaries are charged for key comparisons against
the actual allocation bound, including a writer's temporary heap. -/
theorem intern_comparisons {m : ℕ} {dir : PolylogHierarchy.Store t}
    (sz : Sized (logCap n) b m dir H) (hb : b ≤ 5+(logCap n+1)*3)
    (hm : m ≤ horizon n + logCap n + 2) {out : Heap} (v : out.Valid)
    (hw : out.next ≤ H.next+perMove (logCap n) b) (key : Key) :
    PolylogDictionary.internComparisons out key ≤ 9*tableHeight n := by
  have room := hw.trans_lt (indices_fit sz hb hm).2
  have pos : out.next ≠ 0 := by have := v.reserved; omega
  have bits := (Nat.log2_lt pos).mpr room
  exact (PolylogDictionary.internComparisons_allocated out v key).trans (Nat.mul_le_mul_left 9 bits)

section Calls

variable [rules : Choices n]

private theorem selected_moves (k : ℕ) (q : Query n) (fuel : ℕ) (M : Memory n) (r : Result n)
    (h : selectLoop k q fuel M = some r) : refinementCount r.actions < fuel := by
  induction fuel generalizing M r with
  | zero => simp [selectLoop] at h
  | succ fuel ih =>
    cases ha : rules.select M k q with
    | answer a =>
      simp only [selectLoop, ha, Option.some.injEq] at h
      subst r; exact Nat.zero_lt_succ _
    | refine x c =>
      cases ht : selectLoop k q fuel (applyMove M (makeMove M x c)) with
      | none => simp [selectLoop, ha, ht] at h
      | some r' =>
        simp only [selectLoop, ha, ht, Option.map_some, Option.some.injEq] at h
        subst r
        have := ih _ _ ht
        simp only [refinementCount_cons, actionRefinements]; omega

private theorem repair_moves (k : ℕ) (M : Memory n) : refinementCount (repair k M).2 ≤ 2^k := by
  cases hp : GraphPaths.firstPath M.tree.system.edge (2^k) with
  | some xs =>
    have hlen := congrArg List.length (pathBatch_labels k M xs)
    simpa only [repair, hp, refinementCount_cons, refinementCount_nil, actionRefinements,
      Nat.add_zero, List.length_map, (GraphPaths.firstPath_some _ _ _ hp).1] using
      (show (pathBatch k M xs).2.length ≤ 2^k by
        simpa only [List.length_map, (GraphPaths.firstPath_some _ _ _ hp).1] using hlen.le)
  | none =>
    cases hd : degreeChoice M k with
    | none => simp [repair, hp, hd]
    | some x =>
      simp only [repair, hp, hd, refinementCount_cons, actionRefinements, refinementCount_nil, Nat.add_zero]
      exact Nat.two_pow_pos _

/-- The number of newly allocated paths comes from the actual actions
returned by the selector and its chosen repair. -/
theorem comparison_moves (k : ℕ) (M : Memory n) (q : Query n) {r : Result n}
    (hr : Controller.compare k M q = some r) : refinementCount r.actions ≤ 2^k+2 := by
  cases hs : selectLoop k q 3 M with
  | none => simp [Controller.compare, hs] at hr
  | some z =>
    simp only [Controller.compare, hs, Option.map_some, Option.some.injEq] at hr
    subst r
    have h₂ := selected_moves k q 3 M z hs
    have h₁ := repair_moves k (recorded z.memory q z.answer)
    simp only [refinementCount_append, refinementCount_cons, refinementCount_nil, actionRefinements]
    change refinementCount z.actions + (0+0) + refinementCount (repair k (recorded z.memory q z.answer)).2 ≤ _
    omega

end Calls

local instance roundedChoices (n : ℕ) : Choices n := PolylogOracle.choices n
local instance roundedLaws (n : ℕ) : ChoiceLaws (roundedChoices n) := PolylogOracle.choices_valid n

/-- Accounting through the actual rounded transitions, including replay of
queries with arbitrarily supplied historical answers. -/
theorem active_trace {k t : ℕ} (hk : 64 ≤ k) {M : Memory n}
    (run : PolylogPrecision.ActiveRun k t M) : Ready k M ∧ Traced k M ∧ M.history.length = t := by
  induction run with
  | start => exact ⟨initial_ready n k (by omega), initial_traced k n, rfl⟩
  | @next t M prior q r step ih =>
    obtain ⟨s, hs, hready, hv⟩ := compare_total_spec k hk M ih.1 q
    have eq : s = r := Option.some.inj (hs.symm.trans step)
    subst r
    exact ⟨hready, ih.2.1.compare q s hs hv, by rw [compare_history k M q s hs, List.length_cons, ih.2.2]⟩

theorem replay_refinements {k fuel : ℕ} (hk : 64 ≤ k) (hist : History n) {M : Memory n}
    (h : (PolylogAdversary.policy n).replay k hist = .active fuel M) : totalDepth M ≤ horizon n := by
  obtain ⟨run, _, clock⟩ := PolylogPrecision.replay_active hk hist h
  obtain ⟨ready, trace, len⟩ := active_trace hk run
  exact trace.totalDepth_le_horizon hk ready.toGeometric (by omega)

/-- Each prefix of the current comparison, down to a position inside a
reserved path, fits the same fixed tables. -/
theorem intermediate_refinements (extra : Optimal.CappedArithmetic.Expr) {fuel : ℕ}
    (hk : 64 ≤ PolylogSchedule.parameter extra n) (hist : History n) {M : Memory n}
    (h : (PolylogAdversary.policy n).replay (PolylogSchedule.parameter extra n) hist = .active fuel M)
    (q : Query n) {r : Result n} (step : Controller.compare (PolylogSchedule.parameter extra n) M q = some r)
    {i : ℕ} (hi : i ≤ refinementCount r.actions) :
    totalDepth M + i ≤ horizon n + logCap n + 2 := by
  have hm := replay_refinements hk hist h
  have hn := comparison_moves _ M q step
  have hheight := PolylogSchedule.height_le hk
  have hpow : 2^PolylogSchedule.parameter extra n ≤ ArbitraryLabels.pathHeight (PolylogSchedule.parameter extra n) :=
    Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
  omega

end SortingAdversary.Continuous.PolylogResources
