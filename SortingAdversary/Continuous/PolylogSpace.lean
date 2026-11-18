import SortingAdversary.Continuous.PolylogExecution
import SortingAdversary.Continuous.PolylogMutation

/-!
# Population of the stored tables through and after freezing

Count the five per-label slots (two adjacency rows, two wall handles, one
cursor), both incidence lists, allocated hierarchy nodes, and entries of
both balanced block dictionaries. This measures logical table entries;
a persistent-trie path or balanced-map node has its own word cost.
-/

namespace SortingAdversary.Continuous.PolylogExecution

open PolylogCompare (Memory)
open PolylogResources
open Optimal.Parameters (logCap)
variable {n t b : ℕ}

def incidenceEntries (m : Memory n t b) : ℕ :=
  ∑ x : Fin n, ((m.spatial.graph.succs.get x.val).value.length +
    (m.spatial.graph.preds.get x.val).value.length)

def tableEntries (m : Memory n t b) : ℕ :=
  5*n + incidenceEntries m + m.spatial.directory.next + m.heap.address.size + m.heap.record.size

theorem incidenceEntries_le (m : Memory n t b) {D : ℕ} {M : Controller.Memory n}
    {nodes : List (List ℕ)} (hr : m.Represents D nodes M) {k : ℕ} (hg : Controller.Admissible k M) :
    incidenceEntries m ≤ n*(2*k) := by
  have deg := PolylogMutation.bounded_of_degree hr.spatial.graph k hg.noLoop hg.degree
  calc
    _ ≤ ∑ _ : Fin n, 2*k := Finset.sum_le_sum fun x _ => by
      have := deg.1 x; have := deg.2 x; omega
    _ = _ := by simp

/-- Applies at the temporary graph degree of a comparison as well as the
stricter graph degree of its public call boundaries. -/
theorem tableEntries_le (m : Memory n t b) {D k : ℕ} {M : Controller.Memory n}
    (rep : PolylogCompare.Aligned D (logCap n) m M) (geo : Controller.Admissible k M)
    (hk : k ≤ logCap n) (hb : b ≤ 5+(logCap n+1)*3)
    (hm : Controller.totalDepth M ≤ Controller.horizon n + logCap n + 2) :
    tableEntries m ≤ 8210*(n+1)*(logCap n+1)^4 := by
  let L := logCap n+1
  obtain ⟨nodes,hr⟩ := rep.storage
  obtain ⟨hd,hh⟩ := space_envelope rep.sized hb hm
  have row := (incidenceEntries_le m hr geo).trans (Nat.mul_le_mul_left n (Nat.mul_le_mul_left 2 hk))
  have entries := m.valid.address_size
  have records := m.valid.record_size
  let W := (n+1)*L^4
  have hL : L ≤ L^4 := Nat.le_self_pow (by decide) _
  have h₁ : (n+1)*L ≤ W := Nat.mul_le_mul_left _ hL
  have h₂ : n ≤ W := (Nat.le_succ _).trans ((Nat.le_mul_of_pos_right _ (by dsimp [L]; omega)).trans h₁)
  have h₃ : incidenceEntries m ≤ 2*W := by
    apply row.trans
    calc
      n*(2*logCap n) ≤ 2*((n+1)*L) := by dsimp [L]; nlinarith
      _ ≤ _ := Nat.mul_le_mul_left _ h₁
  have h₄ : m.spatial.directory.next ≤ 4*W := by
    apply hd.trans
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left 4 h₁
  have h₅ : m.heap.next ≤ 4096*W := by
    dsimp only [W,L]
    rw [← Nat.mul_assoc]
    omega
  change _ ≤ 8210*(n+1)*L^4
  rw [Nat.mul_assoc]
  change 5*n + incidenceEntries m + m.spatial.directory.next + m.heap.address.size +
    m.heap.record.size ≤ 8210*W
  omega

def storedEntries {c : Config} : State n c → ℕ
  | .fallback => 0
  | .active _ m | .frozen m => tableEntries m

/-- Freezing reuses the same memory for arbitrarily long continuations. -/
theorem replay_entries (active : ActiveRefinement n) (hist : History n) :
    storedEntries (replay (config n) hist) ≤ 8210*(n+1)*(logCap n+1)^4 := by
  have bound {m : Mem n} {M : Controller.Memory n} (a : Stores m M) (stage : 64 ≤ (config n).k)
      (depth : Controller.totalDepth M ≤ Controller.horizon n) :
      tableEntries m ≤ 8210*(n+1)*(logCap n+1)^4 := by
    have bh := PolylogSchedule.capacity_bits (extra := PolylogAdversary.extra) stage (le_refl (logCap n))
    have sh := PolylogSchedule.height_le (extra := PolylogAdversary.extra) stage
    have deg : (config n).k ≤ logCap n := (Nat.lt_two_pow_self (n := (config n).k)).le.trans
      ((Nat.pow_le_pow_right (by decide) (Nat.le_succ _)).trans sh)
    exact tableEntries_le m a.aligned a.ready.admissible deg bh (by omega)
  have rel := replay_relates active hist
  generalize concrete : replay (config n) hist = s at rel ⊢
  generalize hs : (PolylogAdversary.policy n).replay (config n).k hist = ref at rel
  cases rel with
  | fallback => exact Nat.zero_le _
  | active hk good => exact bound good hk (replay_refinements hk hist hs)
  | frozen hk good hd => exact bound good hk hd

/-- Cumulative operation charges up to the last mutating call. The history
is stored newest first, so the induction visits the actual states in order. -/
def preFreezeCharges (c : Config) : History n → ℕ
  | [] => 0
  | o :: past => preFreezeCharges c past +
      if past.length < Controller.horizon n then (step c (replay c past) o.query).work else 0

theorem preFreezeCharges_le {B : ℕ} (bounds : ∀ hist : History n, ∀ q : Query n,
    (step (config n) (replay (config n) hist) q).work ≤ B) (hist : History n) :
    preFreezeCharges (config n) hist ≤ min hist.length (Controller.horizon n) * B := by
  induction hist with
  | nil => simp [preFreezeCharges]
  | cons o h ih =>
    by_cases lt : h.length < Controller.horizon n
    · simp only [preFreezeCharges, if_pos lt, List.length_cons, Nat.min_eq_left (Nat.succ_le_of_lt lt),
        Nat.succ_mul]
      rw [Nat.min_eq_left lt.le] at ih
      exact Nat.add_le_add ih (bounds h o.query)
    · have ge := Nat.le_of_not_gt lt
      simpa only [preFreezeCharges, if_neg lt, Nat.add_zero, List.length_cons,
        Nat.min_eq_right (Nat.le_succ_of_le ge)] using (Nat.min_eq_right ge ▸ ih)

/-- If each query takes C·L^e operations, all pre-freeze calls together
take at most C·n·L^(e+1), also bounding their cumulative unit allocations.
The result is uniform in the length of any read-only frozen suffix. -/
theorem preFreezeCharges_polynomial (C e : ℕ) (bounds : ∀ hist : History n, ∀ q : Query n,
    (step (config n) (replay (config n) hist) q).work ≤ C*(logCap n+1)^e) (hist : History n) :
    preFreezeCharges (config n) hist ≤ C*n*(logCap n+1)^(e+1) := by
  apply (preFreezeCharges_le bounds hist).trans
  calc
    _ ≤ (n*(logCap n+1))*(C*(logCap n+1)^e) := Nat.mul_le_mul_right _
      ((Nat.min_le_right ..).trans (PolylogSchedule.horizon_le n))
    _ = _ := by ring

end SortingAdversary.Continuous.PolylogExecution
