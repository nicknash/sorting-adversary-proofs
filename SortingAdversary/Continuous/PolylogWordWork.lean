import SortingAdversary.Continuous.PolylogCompareProofs

/-!
# Balanced dictionary costs for shared block operations

The two dictionaries implementing the block heap have machine-word keys or
triples of such words. The comparison count below follows their actual key
paths. A key visit covers at most three component comparisons and one local
insertion rebalance. A probe may discard its temporary heap; both the
dictionary work and the maximal temporary allocation are accounted for.
-/

namespace SortingAdversary.Continuous.PolylogWordWork

open PolylogBits PolylogDictionary
open Optimal.PrimitiveWork (Result)

def fetch (H : Heap) (i : ℕ) : Option Key × ℕ :=
  lookup i H.record.inner.inner

theorem fetch_value (H : Heap) (i : ℕ) : (fetch H i).1 = H.record[i]? :=
  (lookup_map ..).1

private theorem log_fit {i T : ℕ} (hi : i < 2^T) (pos : 0 < T) : i.log2+1 ≤ T := by
  by_cases e : i = 0
  · simp [e]; omega
  · exact (Nat.log2_lt e).2 hi

theorem fetch_fit (H : Heap) (valid : H.Valid) {T : ℕ} (pos : 0 < T)
    (fits : H.next < 2^T) (i : ℕ) : (fetch H i).2 ≤ 3*T := by
  exact (lookup_map H.record i).2.trans (Nat.mul_le_mul_left 3
    (log_fit (valid.record_size.trans_lt fits) pos))

theorem intern_fit (H : Heap) (valid : H.Valid) {T : ℕ} (pos : 0 < T)
    (fits : H.next < 2^T) (k : Key) : internComparisons H k ≤ 9*T :=
  (internComparisons_allocated H valid k).trans (Nat.mul_le_mul_left 9 (log_fit fits pos))

/-- A trace of the record lookups and canonical joins actually selected by
a computation. `temporary` runs a subtrace and discards its heap. -/
inductive Trace
  | done
  | read (addr : ℕ) (next : Trace)
  | join (key : Key) (next : Trace)
  | temporary (probe next : Trace)

def Trace.visits : Trace → ℕ
  | .done => 0
  | .read _ xs | .join _ xs => xs.visits+1
  | .temporary p xs => p.visits+xs.visits

def Trace.run : Trace → Heap → Result Heap
  | .done, H => ⟨H,0⟩
  | .read i xs, H =>
    let later := xs.run H
    ⟨later.value, 1 + (fetch H i).2 + later.work⟩
  | .join k xs, H =>
    let later := xs.run (H.intern k).1
    ⟨later.value, 3 + 4*internComparisons H k + later.work⟩
  | .temporary p xs, H =>
    let later := xs.run H
    ⟨later.value,(p.run H).work+later.work⟩

def Trace.append : Trace → Trace → Trace
  | .done, ys => ys
  | .read i xs, ys => .read i (xs.append ys)
  | .join k xs, ys => .join k (xs.append ys)
  | .temporary p xs, ys => .temporary p (xs.append ys)

@[simp] theorem Trace.append_visits (xs ys : Trace) :
    (xs.append ys).visits = xs.visits+ys.visits := by
  induction xs with
  | done => simp [append,visits]
  | read _ _ ih | join _ _ ih => simp [append,visits,ih]; omega
  | temporary _ _ _ ih => simp [append,visits,ih,Nat.add_assoc]

@[simp] theorem Trace.append_value (xs ys : Trace) (H : Heap) :
    ((xs.append ys).run H).value = (ys.run (xs.run H).value).value := by
  induction xs generalizing H with
  | done => rfl
  | read _ _ ih | join _ _ ih => exact ih _
  | temporary _ _ _ ih => exact ih _

/-- Every map path in an adaptive trace is charged, including paths in
failed binary-search probes. `T` bounds addresses at all intermediate
states, using at most one new record per visit. -/
theorem Trace.bound (xs : Trace) (H : Heap) (valid : H.Valid) {T : ℕ}
    (pos : 0 < T) (room : H.next+xs.visits < 2^T) :
    (xs.run H).value.Valid ∧ (xs.run H).value.next ≤ H.next+xs.visits ∧
      (xs.run H).work ≤ xs.visits*(36*T+3) := by
  induction xs generalizing H with
  | done => exact ⟨valid, Nat.le_refl _, Nat.zero_le _⟩
  | read i xs ih =>
    simp only [visits] at room ⊢
    have here : H.next < 2^T := by omega
    obtain ⟨v,n,w⟩ := ih H valid (by omega)
    have f := fetch_fit H valid pos here i
    simp only [run]
    refine ⟨v,by omega,?_⟩
    rw [Nat.succ_mul xs.visits]
    omega
  | join k xs ih =>
    simp only [visits] at room ⊢
    have h := (H.intern_growth valid k).1
    obtain ⟨v,n,w⟩ := ih _ (H.intern_valid valid k) (by omega)
    have f := intern_fit H valid pos (by omega) k
    simp only [run]
    refine ⟨v,by omega,?_⟩
    rw [Nat.succ_mul xs.visits]
    omega
  | temporary p xs ip ix =>
    simp only [visits] at room ⊢
    obtain ⟨_,_,pr⟩ := ip H valid (by omega)
    obtain ⟨v,n,w⟩ := ix H valid (by omega)
    simp only [run,Nat.add_mul]
    exact ⟨v,by omega,Nat.add_le_add pr w⟩

/-- The precise record IDs fetched by the address comparison. -/
def compareTrace (H : Heap) : ℕ → ℕ → ℕ → Trace
  | 0, _, _ => .done
  | h+1, i, j =>
    let x := H.children i
    let y := H.children j
    let rest := if x.1 = y.1 then compareTrace H h x.2 y.2 else compareTrace H h x.1 y.1
    .read i (.read j rest)

theorem compareTrace_visits (H : Heap) (h i j : ℕ) :
    (compareTrace H h i j).visits = 2*h := by
  induction h generalizing i j with
  | zero => rfl
  | succ h ih =>
    simp only [compareTrace,Trace.visits]
    split <;> rw [ih] <;> omega

/-- The precise reads and writes along an addressed truncation. Keys use
the actually allocated child address and the cached zero reference. -/
def truncateTrace (z : PolylogRawBits.Table) (H : Heap) : {h : ℕ} → Position h → ℕ → Trace
  | _, .here, _ => .done
  | _, @Position.high h p, i =>
    let left := (H.children i).1
    let t := PolylogRawBits.truncate z H p left
    .read i ((truncateTrace z H p left).append (.join (h+1,t.addr,z h false) .done))
  | _, @Position.low h p, i =>
    let x := H.children i
    let t := PolylogRawBits.truncate z H p x.2
    .read i ((truncateTrace z H p x.2).append (.join (h+1,x.1,t.addr) .done))

theorem truncateTrace_spec (z : PolylogRawBits.Table) (H : Heap) {h : ℕ} (p : Position h) (i : ℕ) :
    ((truncateTrace z H p i).run H).value = (PolylogRawBits.truncate z H p i).heap ∧
      (truncateTrace z H p i).visits = 2*h := by
  induction p generalizing i with
  | here => exact ⟨rfl,rfl⟩
  | high p ih | low p ih =>
    obtain ⟨e,c⟩ := ih (_ : ℕ)
    constructor
    · simp only [truncateTrace,Trace.run,Trace.append_value,PolylogRawBits.truncate,
        PolylogRawBits.join,Trace.run]
      rw [e]
    · simp only [truncateTrace,Trace.visits,Trace.append_visits,c]
      omega

def bumpTrace (z : PolylogRawBits.Table) (H : Heap) : ℕ → ℕ → Trace
  | 0, _ => .done
  | h+1, i =>
    let x := H.children i
    .read i (if x.2 = z h true then
      let t := PolylogRawBits.bump z H h x.1
      (bumpTrace z H h x.1).append (.join (h+1,t.addr,z h false) .done)
    else
      let t := PolylogRawBits.bump z H h x.2
      (bumpTrace z H h x.2).append (.join (h+1,x.1,t.addr) .done))

theorem bumpTrace_spec (z : PolylogRawBits.Table) (H : Heap) (h i : ℕ) :
    ((bumpTrace z H h i).run H).value = (PolylogRawBits.bump z H h i).heap ∧
      (bumpTrace z H h i).visits = 2*h := by
  induction h generalizing i with
  | zero => exact ⟨rfl,rfl⟩
  | succ h ih =>
    simp only [bumpTrace,PolylogRawBits.bump,Trace.run,Trace.visits]
    split <;> simp only [Trace.append_value,Trace.append_visits,Trace.run,Trace.visits,
      (ih _).1, (ih _).2, PolylogRawBits.join, true_and] <;> omega

/-- The trace includes the second carry walk only in the branch that
actually needs it. The other carry cases reuse a cached block. -/
def addTrace (z : PolylogRawBits.Table) (H : Heap) : {h : ℕ} → Position h → ℕ → Trace
  | _, .here, _ => .done
  | _, @Position.high h p, i =>
    let x := H.children i
    let t := PolylogRawBits.addUnit z H p x.1
    .read i ((addTrace z H p x.1).append (.join (h+1,t.1.addr,x.2) .done))
  | _, @Position.low h p, i =>
    let x := H.children i
    let t := PolylogRawBits.addUnit z H p x.2
    .read i ((addTrace z H p x.2).append
      (if t.2 then
        if x.1 = z h true then .join (h+1,z h false,t.1.addr) .done
        else
          let w := PolylogRawBits.bump z t.1.heap h x.1
          (bumpTrace z t.1.heap h x.1).append (.join (h+1,w.addr,t.1.addr) .done)
       else .join (h+1,x.1,t.1.addr) .done))

theorem addTrace_spec (z : PolylogRawBits.Table) (H : Heap) {h : ℕ} (p : Position h) (i : ℕ) :
    ((addTrace z H p i).run H).value = (PolylogRawBits.addUnit z H p i).1.heap ∧
      (addTrace z H p i).visits ≤ 2*h^2 := by
  induction p generalizing i with
  | here => exact ⟨rfl,by simp [addTrace,Trace.visits]⟩
  | @high h p ih =>
    obtain ⟨v,c⟩ := ih (H.children i).1
    simp only [addTrace,PolylogRawBits.addUnit,Trace.run,Trace.visits,
      Trace.append_value,Trace.append_visits,v,PolylogRawBits.join,true_and]
    nlinarith only [c,Nat.zero_le h]
  | @low h p ih =>
    obtain ⟨v,c⟩ := ih (H.children i).2
    simp only [addTrace,PolylogRawBits.addUnit,Trace.run,Trace.visits,Trace.append_value,Trace.append_visits,v]
    split
    · split
      · simp only [Trace.run,Trace.visits,PolylogRawBits.join,true_and]; nlinarith only [c,Nat.zero_le h]
      · simp only [Trace.append_value,Trace.run,Trace.append_visits,Trace.visits,
          (bumpTrace_spec ..).1,(bumpTrace_spec ..).2,PolylogRawBits.join,true_and]
        nlinarith only [c,Nat.zero_le h]
    · simp only [Trace.run,Trace.visits,PolylogRawBits.join,true_and]; nlinarith only [c,Nat.zero_le h]

def advanceTrace (z : PolylogRawBits.Table) (H : Heap) {h : ℕ} (p : Position h) (i : ℕ) :
    ℕ → Trace
  | 0 => .done
  | j+1 =>
    let t := PolylogRawBits.advance z H p i j
    (advanceTrace z H p i j).append (addTrace z t.heap p t.addr)

theorem advanceTrace_spec (z : PolylogRawBits.Table) (H : Heap) {h : ℕ} (p : Position h) (i j : ℕ) :
    ((advanceTrace z H p i j).run H).value = (PolylogRawBits.advance z H p i j).heap ∧
      (advanceTrace z H p i j).visits ≤ j*(2*h^2) := by
  induction j with
  | zero => exact ⟨rfl,by simp [advanceTrace,Trace.visits]⟩
  | succ j ih =>
    dsimp only [advanceTrace,PolylogRawBits.advance]
    rw [Trace.append_value,ih.1,Trace.append_visits,Nat.succ_mul j]
    exact ⟨(addTrace_spec ..).1,Nat.add_le_add ih.2 (addTrace_spec ..).2⟩

/-- Any trace of at most C·L^e block accesses at a represented intermediate
state has O(L) dictionary work per access, with L = logCap n + 1. This
allows ephemeral probes to allocate anywhere within the trace's own budget. -/
theorem reachable_trace {n b t D : ℕ} {m : PolylogCompare.Memory n t b} {M : Controller.Memory n}
    (aligned : PolylogCompare.Aligned D (Optimal.Parameters.logCap n) m M)
    (hb : b ≤ 5+(Optimal.Parameters.logCap n+1)*3)
    (hm : Controller.totalDepth M ≤ Controller.horizon n+Optimal.Parameters.logCap n+2)
    (xs : Trace) (C e : ℕ) (count : xs.visits ≤ C*(Optimal.Parameters.logCap n+1)^e) :
    (xs.run m.heap).work ≤ xs.visits*((36*(20+C.size+e)+3)*(Optimal.Parameters.logCap n+1)) := by
  let L := Optimal.Parameters.logCap n+1
  let T := PolylogResources.tableHeight n
  have start : m.heap.next < 2^T := by
    have h := (PolylogResources.indices_fit aligned.sized hb hm).2
    exact (Nat.le_add_right ..).trans_lt h
  have hL : L ≤ 2^L := Nat.lt_two_pow_self.le
  have trace : xs.visits ≤ 2^(C.size+L*e) := by
    rw [pow_add,pow_mul]
    exact count.trans (Nat.mul_le_mul (Nat.lt_size_self C).le (Nat.pow_le_pow_left hL e))
  let width := T+C.size+L*e
  have a : T ≤ width := by dsimp [width]; omega
  have d : C.size+L*e ≤ width := by dsimp [width]; omega
  have room : m.heap.next+xs.visits < 2^(width+1) := by
    have h1 := start.trans_le (Nat.pow_le_pow_right (by decide) a)
    have h2 := trace.trans (Nat.pow_le_pow_right (by decide) d)
    rw [pow_succ]; omega
  have factor : 36*(width+1)+3 ≤ (36*(20+C.size+e)+3)*L := by
    have h1 : 1 ≤ L := by dsimp [L]; omega
    have hc := Nat.mul_le_mul_left C.size h1
    dsimp only [width,T,PolylogResources.tableHeight] at *
    change 36*(13+6*L+C.size+L*e+1)+3 ≤ _
    nlinarith
  exact (xs.bound m.heap m.valid (Nat.succ_pos _) room).2.2.trans (Nat.mul_le_mul_left _ factor)

/-- A bisection subtrace is discarded before the next trial. The same
predicate and midpoint recurrence choose the subsequent interval. -/
def bisectionTrace (test : ℕ → Bool) (trial : ℕ → Trace) : ℕ → ℕ → ℕ → Trace
  | 0, _, _ => .done
  | rounds+1, lo, hi =>
    let mid := (lo+hi)/2
    .temporary (trial mid) (if test mid then bisectionTrace test trial rounds lo mid
      else bisectionTrace test trial rounds (mid+1) hi)

theorem bisectionTrace_spec (test : ℕ → Bool) (trial : ℕ → Trace) (rounds lo hi : ℕ)
    (H : Heap) (B : ℕ) (bound : ∀ j, (trial j).visits ≤ B) :
    ((bisectionTrace test trial rounds lo hi).run H).value = H ∧
      (bisectionTrace test trial rounds lo hi).visits ≤ rounds*B := by
  induction rounds generalizing lo hi with
  | zero => exact ⟨rfl,by simp [bisectionTrace,Trace.visits]⟩
  | succ rounds ih =>
    simp only [bisectionTrace,Trace.run,Trace.visits,Nat.succ_mul rounds]
    split <;> exact ⟨(ih _ _).1,(Nat.add_le_add (bound _) (ih _ _).2).trans_eq (Nat.add_comm ..)⟩

def probeTrace (table : PolylogRawBits.Table) (H : Heap) {h : ℕ} (p : Position h)
    (l r : ℕ) : Trace :=
  let sum := PolylogRawBits.addUnit table H p l
  (addTrace table H p l).append (compareTrace sum.1.heap h r sum.1.addr)

theorem probeTrace_visits (table : PolylogRawBits.Table) (H : Heap) {h : ℕ} (p : Position h)
    (l r : ℕ) : (probeTrace table H p l r).visits ≤ 2*h^2+2*h := by
  simp only [probeTrace,Trace.append_visits,compareTrace_visits]
  exact Nat.add_le_add_right (addTrace_spec ..).2 _

def fallbackTrace (table : PolylogRawBits.Table) (H : Heap) (h D F l r : ℕ) : Trace :=
  let pos := fun j => PolylogBlockAnchor.placeFor h D (min j F)
  let test := fun j => PolylogRawAnchor.probe table H (pos j) l r
  let rounds := Nat.log 2 F+1
  let search := bisectionTrace test (fun j => probeTrace table H (pos j) l r) rounds 0 F
  let p := PolylogBlockAnchor.placeFor h D ((PolylogAnchor.bisect test rounds 0 F).1+2)
  let t := PolylogRawBits.truncate table H p l
  search.append ((truncateTrace table H p l).append (advanceTrace table t.heap p t.addr 3))

theorem fallbackTrace_spec (table : PolylogRawBits.Table) (H : Heap) (h D F l r : ℕ) :
    ((fallbackTrace table H h D F l r).run H).value = (PolylogRawAnchor.run table H h D F l r).heap ∧
      (fallbackTrace table H h D F l r).visits+2 ≤ (h+1)*PolylogRawAnchor.workBound h F := by
  let pos := fun j => PolylogBlockAnchor.placeFor h D (min j F)
  let test := fun j => PolylogRawAnchor.probe table H (pos j) l r
  let rounds := Nat.log 2 F+1
  let trial := fun j => probeTrace table H (pos j) l r
  let p := PolylogBlockAnchor.placeFor h D ((PolylogAnchor.bisect test rounds 0 F).1+2)
  let t := PolylogRawBits.truncate table H p l
  have take := bisectionTrace_spec test trial rounds 0 F H (2*h^2+2*h)
    (fun _ => probeTrace_visits ..)
  have strip := truncateTrace_spec table H p l
  have add := advanceTrace_spec table t.heap p t.addr 3
  change (((bisectionTrace test trial rounds 0 F).append ((truncateTrace table H p l).append
    (advanceTrace table t.heap p t.addr 3))).run H).value = (PolylogRawBits.advance table t.heap p t.addr 3).heap ∧ _
  constructor
  · rw [Trace.append_value,take.1,Trace.append_value,strip.1]
    exact add.1
  · change ((bisectionTrace test trial rounds 0 F).append ((truncateTrace table H p l).append
       (advanceTrace table t.heap p t.addr 3))).visits+2 ≤ _
    rw [Trace.append_visits,Trace.append_visits,strip.2]
    change _ ≤ (h+1)*(rounds*(24*h+20)+(48*h+24))
    have small := take.2
    have total := add.2
    nlinarith [Nat.zero_le (rounds*h^2),Nat.zero_le (rounds*h),Nat.zero_le (h^2),Nat.zero_le h,
      Nat.zero_le rounds]

def checkedFallbackTrace (table : PolylogRawBits.Table) (H : Heap) (h D F l r : ℕ) : Trace :=
  .read l (.read r (if PolylogAddressOrder.isRoot H h l && PolylogAddressOrder.isRoot H h r
    then fallbackTrace table H h D F l r else .done))

/-- These are traces of the concrete writer used in the machine, including
its two root-height checks on entry and every discarded trial. -/
theorem checkedFallback_spec {S : Store} {H : Heap} {b cap : ℕ} (D F : ℕ)
    (v : H.Valid) (typed : H.Typed) (cache : Cached S H cap) (hc : b ≤ cap) (l r : ℕ) :
    let xs := checkedFallbackTrace cache.lookup H b D F l r
    let out := PolylogRawAnchor.fallback D F v typed cache hc l r
    (xs.run H).value = out.heap ∧ xs.visits ≤ (b+1)*out.work := by
  dsimp only [checkedFallbackTrace,Trace.run,Trace.visits]
  by_cases good : PolylogAddressOrder.isRoot H b l = true ∧ PolylogAddressOrder.isRoot H b r = true
  · simpa [Bool.and_eq_true,good,PolylogRawAnchor.fallback,Nat.add_assoc] using
      fallbackTrace_spec cache.lookup H b D F l r
  · simp [Bool.and_eq_true,good,PolylogRawAnchor.fallback,Trace.run,Trace.visits]
    omega

theorem reachable_trace_polynomial {n b t D : ℕ} {m : PolylogCompare.Memory n t b} {M : Controller.Memory n}
    (aligned : PolylogCompare.Aligned D (Optimal.Parameters.logCap n) m M)
    (hb : b ≤ 5+(Optimal.Parameters.logCap n+1)*3)
    (hm : Controller.totalDepth M ≤ Controller.horizon n+Optimal.Parameters.logCap n+2)
    (xs : Trace) (C e : ℕ) (count : xs.visits ≤ C*(Optimal.Parameters.logCap n+1)^e) :
    (xs.run m.heap).work ≤ (C*(36*(20+C.size+e)+3))*(Optimal.Parameters.logCap n+1)^(e+1) := by
  apply (reachable_trace aligned hb hm xs C e count).trans
  apply (Nat.mul_le_mul_right _ count).trans
  rw [pow_succ]
  exact le_of_eq (by ac_rfl)

/-- Dictionary visits for the physical fallback from a pair of stored wall
addresses. All three temporary carries and the final output heap appear in
the trace. The bound is uniform over all labels on an active call. -/
theorem stored_prefix_dictionary {n : ℕ} (hk : 64 ≤ PolylogAdversary.parameter n)
    {m : PolylogCompare.ScheduledMemory n} {M : Controller.Memory n} (align : PolylogCompare.Tracks m M)
    (depth : Controller.totalDepth M ≤ PolylogCompare.depthLimit n) (x : Fin n) :
    let D := PolylogCompare.binaryPoint n
    let b := D.size
    let l := (m.spatial.walls.lower.get x.val).value
    let r := (m.spatial.walls.upper.get x.val).value
    let xs := checkedFallbackTrace m.cache.lookup m.heap b D (D-2) l r
    (xs.run m.heap).value = (PolylogCompare.writePrefix D m x).out.heap ∧
      (xs.run m.heap).work ≤ 50000000*(Optimal.Parameters.logCap n+1)^4 := by
  let D := PolylogCompare.binaryPoint n
  let b := D.size
  let L := Optimal.Parameters.logCap n+1
  let l := (m.spatial.walls.lower.get x.val).value
  let r := (m.spatial.walls.upper.get x.val).value
  let xs := checkedFallbackTrace m.cache.lookup m.heap b D (D-2) l r
  have spec := checkedFallback_spec D (D-2) m.valid m.typed m.cache (le_refl b) l r
  refine ⟨spec.1,?_⟩
  have hb : b ≤ 5+L*3 :=
    PolylogSchedule.capacity_bits (extra := PolylogAdversary.extra) hk le_rfl
  have hl : 1 ≤ L := by dsimp only [L]; omega
  have hbs : b+1 ≤ 9*L := by omega
  have hd : Nat.log 2 (D-2)+1 ≤ b+1 := by
    rw [← Nat.log2_eq_log_two]
    by_cases z : D-2=0
    · simp [z]
    have a := (Nat.log2_lt z).2 ((Nat.sub_le D 2).trans_lt (Nat.lt_size_self D))
    dsimp only [b]; omega
  have cb : (b+1)*PolylogRawAnchor.workBound b (D-2) ≤ 30000 * L^3 := by
    have p := Nat.mul_le_mul hd (show 24*b+20 ≤ 216*L by omega)
    have small : 48*b+24 ≤ 432*L := by omega
    change (b+1)*((Nat.log 2 (D-2)+1)*(24*b+20)+(48*b+24)) ≤ _
    apply (Nat.mul_le_mul hbs (Nat.add_le_add p small)).trans
    nlinarith [Nat.mul_le_mul_right (L^2) hl]
  have count : xs.visits ≤ 30000*L^3 :=
    spec.2.trans ((Nat.mul_le_mul_left _ (PolylogRawAnchor.work_bound D (D-2) m.valid m.typed
      m.cache (le_refl b) l r)).trans cb)
  apply (reachable_trace_polynomial align hb (depth.trans (PolylogCompare.depthLimit_table hk)) xs
    30000 3 count).trans
  exact Nat.mul_le_mul_right _ (by decide)

/-- A successful short anchor visits precisely the one bits of its short
numerator, using the same raw carry writes as the embedder. -/
def embedTrace {S : Store} {H : Heap} {h cap : ℕ}
    (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap) : ℕ → ℕ → ℕ → Trace
  | 0, _, _ => .done
  | len+1, off, z =>
    let prev := PolylogEmbed.emit v cache hc len (off+1) (z/2)
    let prior := embedTrace v cache hc len (off+1) (z/2)
    if z%2 = 1 then prior.append (addTrace cache.lookup prev.heap (atBit h off) prev.cell.addr)
    else prior

theorem embedTrace_spec {S : Store} {H : Heap} {h cap : ℕ}
    (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap) (len off z : ℕ) :
    ((embedTrace v cache hc len off z).run H).value = (PolylogEmbed.emit v cache hc len off z).heap ∧
      (embedTrace v cache hc len off z).visits ≤ len*(2*h^2) := by
  induction len generalizing off z with
  | zero => exact ⟨rfl,by simp [embedTrace,Trace.visits]⟩
  | succ len ih =>
    let w := PolylogEmbed.emit v cache hc len (off+1) (z/2)
    obtain ⟨he,hv⟩ := ih (off+1) (z/2)
    simp only [embedTrace,PolylogEmbed.emit]
    split
    · rw [Trace.append_value,he,Trace.append_visits]
      have a := addTrace_spec cache.lookup w.heap (atBit h off) w.cell.addr
      exact ⟨a.1,(Nat.add_le_add hv a.2).trans_eq (Nat.succ_mul ..).symm⟩
    · exact ⟨he,hv.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))⟩

/-- A short anchor on the actual stored heap also has quartic logarithmic
dictionary work. Its mathematical numerator occurs at short precision only. -/
theorem stored_embed_dictionary {n : ℕ} (hk : 64 ≤ PolylogAdversary.parameter n)
    {m : PolylogCompare.ScheduledMemory n} {M : Controller.Memory n} (align : PolylogCompare.Tracks m M)
    (depth : Controller.totalDepth M ≤ PolylogCompare.depthLimit n) (z : ℕ) :
    let D := PolylogCompare.binaryPoint n
    let e := Optimal.Parameters.logCap n
    let xs := embedTrace m.valid m.cache (le_refl D.size) (e+1) (D-e) z
    (xs.run m.heap).value = (PolylogEmbed.embedAddr D e z m.valid m.cache (le_refl D.size)).heap ∧
      (xs.run m.heap).work ≤ 200000*(e+1)^4 := by
  let D := PolylogCompare.binaryPoint n
  let b := D.size
  let e := Optimal.Parameters.logCap n
  let L := e+1
  let xs := embedTrace m.valid m.cache (le_refl b) (e+1) (D-e) z
  have spec := embedTrace_spec m.valid m.cache (le_refl b) (e+1) (D-e) z
  refine ⟨spec.1,?_⟩
  have hb : b ≤ 5+L*3 :=
    PolylogSchedule.capacity_bits (extra := PolylogAdversary.extra) hk le_rfl
  have hl : 1 ≤ L := by dsimp only [L]; omega
  have hb' : b ≤ 8*L := by omega
  have p := Nat.pow_le_pow_left hb' 2
  have count : xs.visits ≤ 128*L^3 := spec.2.trans (by
    change L*(2*b^2) ≤ _
    apply (Nat.mul_le_mul_left L (Nat.mul_le_mul_left 2 p)).trans
    exact le_of_eq (by ring))
  apply (reachable_trace_polynomial align hb (depth.trans (PolylogCompare.depthLimit_table hk)) xs
    128 3 count).trans
  exact Nat.mul_le_mul_right _ (by decide)

/-- The two child-table reads at each comparison level are within the
comparison's original block-operation charge. -/
theorem compareTrace_bound (H : Heap) (h i j : ℕ) :
    ((compareTrace H h i j).run H).value = H ∧
      (compareTrace H h i j).visits ≤ (H.lessAddr h i j).2 := by
  constructor
  · induction h generalizing i j with
    | zero => rfl
    | succ h ih =>
      simp only [compareTrace,Trace.run]; split <;> exact ih _ _
  · rw [compareTrace_visits,PolylogActive.lessAddr_work]
    omega

def checkedLessTrace (H : Heap) (h i j : ℕ) : Trace :=
  .read i (.read j (if PolylogAddressOrder.isRoot H h i && PolylogAddressOrder.isRoot H h j
    then compareTrace H h i j else .done))

theorem checkedLessTrace_bound (H : Heap) (h i j : ℕ) :
    ((checkedLessTrace H h i j).run H).value = H ∧
      (checkedLessTrace H h i j).visits ≤ (PolylogAddressOrder.less H h i j).work := by
  have c := compareTrace_bound H h i j
  cases l : PolylogAddressOrder.isRoot H h i <;> cases r : PolylogAddressOrder.isRoot H h j <;>
    simp [checkedLessTrace,l,r,PolylogAddressOrder.less,Trace.run,Trace.visits,c.1] <;> omega

/-- The read of one leading bit and the trailing-zero check follow the
same addressed path. Inspecting an excluded sibling uses its zero-cache
handle and does not open that sibling. -/
def bitTrace (H : Heap) : ℕ → ℕ → ℕ → Trace
  | 0, _, _ => .done
  | h+1, i, addr =>
    let x := H.children addr
    .read addr (if i < 2^h then bitTrace H h i x.2 else bitTrace H h (i-2^h) x.1)

theorem bitTrace_spec (H : Heap) (zero : ℕ → ℕ) (h i addr : ℕ) :
    ((bitTrace H h i addr).run H).value = H ∧ (bitTrace H h i addr).visits = h ∧
      h ≤ (PolylogPrefix.readBit H h i addr).2 ∧ h ≤ (PolylogPrefix.tailClear H zero h i addr).2 := by
  induction h generalizing i addr with
  | zero => exact ⟨rfl,rfl,Nat.zero_le _,Nat.zero_le _⟩
  | succ h ih =>
    simp only [bitTrace,Trace.run,Trace.visits,PolylogPrefix.readBit,PolylogPrefix.tailClear]
    split
    · obtain ⟨a,b,c,d⟩ := ih i (H.children addr).2
      exact ⟨a,by omega,by omega,by omega⟩
    · obtain ⟨a,b,c,d⟩ := ih (i-2^h) (H.children addr).1
      exact ⟨a,by omega,by omega,by omega⟩

def leadingTrace (H : Heap) (h addr D : ℕ) : ℕ → Trace
  | 0 => .done
  | len+1 => (leadingTrace H h addr D len).append (bitTrace H h (D-len) addr)

theorem leadingTrace_spec (H : Heap) (h addr D len : ℕ) :
    ((leadingTrace H h addr D len).run H).value = H ∧ (leadingTrace H h addr D len).visits = len*h ∧
      len*h ≤ (PolylogPrefix.readLeading H h addr D len).2 := by
  induction len with
  | zero => exact ⟨rfl,by simp [leadingTrace,Trace.visits],by simp [PolylogPrefix.readLeading]⟩
  | succ len ih =>
    have b := bitTrace_spec H (fun _ => 0) h (D-len) addr
    simp only [leadingTrace,Trace.append_value,Trace.append_visits,ih.1,ih.2.1,b.1,b.2.1,
      Nat.succ_mul len,PolylogPrefix.readLeading,true_and]
    have := ih.2.2
    have := b.2.2.1
    omega

def prefixReadTrace (H : Heap) (h addr D F : ℕ) : Trace :=
  (leadingTrace H h addr D (F+1)).append (bitTrace H h (D-F) addr)

theorem prefixReadTrace_bound (H : Heap) (zero : ℕ → ℕ) (h addr D F : ℕ) :
    ((prefixReadTrace H h addr D F).run H).value = H ∧
      (prefixReadTrace H h addr D F).visits ≤ (PolylogPrefix.read H zero h addr D F).work := by
  have a := leadingTrace_spec H h addr D (F+1)
  have b := bitTrace_spec H zero h (D-F) addr
  simp only [prefixReadTrace,Trace.append_value,Trace.append_visits,a.1,b.1,a.2.1,b.2.1,true_and,
    PolylogPrefix.read]
  have := a.2.2
  have := b.2.2.2
  omega

def Trace.ReadOnly : Trace → Prop
  | .done => True
  | .read _ xs => xs.ReadOnly
  | .join _ _ => False
  | .temporary x y => x.ReadOnly ∧ y.ReadOnly

theorem Trace.ReadOnly.append {xs ys : Trace} (first : xs.ReadOnly) (second : ys.ReadOnly) :
    (xs.append ys).ReadOnly := by
  induction xs with
  | done => exact second
  | read _ _ ih => exact ih first
  | join => exact False.elim first
  | temporary _ _ _ ih => exact ⟨first.1,ih first.2⟩

theorem Trace.read_bound {xs : Trace} (ro : xs.ReadOnly) (H : Heap) (valid : H.Valid)
    {T : ℕ} (pos : 0 < T) (fits : H.next < 2^T) :
    (xs.run H).work ≤ (3*T+1)*xs.visits := by
  induction xs with
  | done => exact Nat.zero_le _
  | read i xs ih =>
    have f := fetch_fit H valid pos fits i
    have t := ih ro
    simp only [run,visits,Nat.mul_succ]
    omega
  | join => exact False.elim ro
  | temporary _ _ ip ix => exact (Nat.add_le_add (ip ro.1) (ix ro.2)).trans_eq (Nat.mul_add ..).symm

theorem compareTrace_readOnly (H : Heap) (h i j : ℕ) : (compareTrace H h i j).ReadOnly := by
  induction h generalizing i j with
  | zero => trivial
  | succ h ih => simp only [compareTrace,Trace.ReadOnly]; split <;> exact ih _ _

theorem checkedLessTrace_readOnly (H : Heap) (h i j : ℕ) : (checkedLessTrace H h i j).ReadOnly := by
  simp only [checkedLessTrace,Trace.ReadOnly]
  split
  · exact compareTrace_readOnly ..
  · trivial

theorem bitTrace_readOnly (H : Heap) (h i addr : ℕ) : (bitTrace H h i addr).ReadOnly := by
  induction h generalizing i addr with
  | zero => trivial
  | succ h ih => simp only [bitTrace,Trace.ReadOnly]; split <;> exact ih _ _

theorem leadingTrace_readOnly (H : Heap) (h addr D F : ℕ) : (leadingTrace H h addr D F).ReadOnly := by
  induction F with
  | zero => trivial
  | succ f ih => exact ih.append (bitTrace_readOnly ..)

theorem prefixReadTrace_readOnly (H : Heap) (h addr D F : ℕ) : (prefixReadTrace H h addr D F).ReadOnly :=
  (leadingTrace_readOnly ..).append (bitTrace_readOnly ..)

/-- This conversion uses the original scalar charge of exactly this read
and has no premise on its precision or number of visits. -/
theorem prefixRead_dictionary (H : Heap) (valid : H.Valid) {T : ℕ} (pos : 0 < T)
    (fits : H.next < 2^T) (zero : ℕ → ℕ) (h addr D F : ℕ) :
    ((prefixReadTrace H h addr D F).run H).work ≤ (3*T+1)*(PolylogPrefix.read H zero h addr D F).work :=
  (Trace.read_bound (prefixReadTrace_readOnly ..) H valid pos fits).trans
    (Nat.mul_le_mul_left _ (prefixReadTrace_bound H zero h addr D F).2)

theorem compare_dictionary (H : Heap) (valid : H.Valid) {T : ℕ} (pos : 0 < T)
    (fits : H.next < 2^T) (h i j : ℕ) :
    ((compareTrace H h i j).run H).work ≤ (3*T+1)*(H.lessAddr h i j).2 :=
  (Trace.read_bound (compareTrace_readOnly ..) H valid pos fits).trans
    (Nat.mul_le_mul_left _ (compareTrace_bound ..).2)

theorem checkedLess_dictionary (H : Heap) (valid : H.Valid) {T : ℕ} (pos : 0 < T)
    (fits : H.next < 2^T) (h i j : ℕ) :
    ((checkedLessTrace H h i j).run H).work ≤ (3*T+1)*(PolylogAddressOrder.less H h i j).work :=
  (Trace.read_bound (checkedLessTrace_readOnly ..) H valid pos fits).trans
    (Nat.mul_le_mul_left _ (checkedLessTrace_bound ..).2)

end SortingAdversary.Continuous.PolylogWordWork
