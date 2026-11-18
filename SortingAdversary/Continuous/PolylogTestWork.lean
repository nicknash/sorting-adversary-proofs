import SortingAdversary.Continuous.PolylogPreparedDefs
import SortingAdversary.Continuous.OperandBounds
import SortingAdversary.Continuous.PolylogLocalBudget
import SortingAdversary.Continuous.PolylogNeighborhoodBudget
import SortingAdversary.Continuous.PolylogCompareShape

/-! Work of the stored local tests, even on rows with incompatible walls. -/

namespace SortingAdversary.Continuous.PolylogTestWork

open PolylogPrepared PolylogOracleWork PolylogEnclosureWork PolylogPrefix PolylogBits PolylogNeighborhood
open EnclosureWork FiniteAveraging Optimal Certificates
open Optimal.PrimitiveWork (Result)
variable {n h m : ℕ}

private def Short (F : ℕ) (q : ℚ) := OnDyadicGrid F q ∧ 0 ≤ q ∧ q ≤ 2

private theorem leading_lt (H : Heap) (h addr D len : ℕ) :
    (readLeading H h addr D len).1 < 2^len := by
  induction len with
  | zero => simp [readLeading]
  | succ l ih =>
    simp only [readLeading, pow_succ]
    cases (readBit H h (D-l) addr).1 <;> simp <;> omega

private theorem read_short (H : Heap) (zero : ℕ → ℕ) (h D F addr : ℕ) :
    Short F (read H zero h addr D F).value.1 ∧ Short F (read H zero h addr D F).value.2 := by
  let a := (readLeading H h addr D (F+1)).1
  have b := leading_lt H h addr D (F+1)
  rw [pow_succ] at b
  change a < 2^F * 2 at b
  have spec (v : ℕ) (hv : v ≤ 2^F*2) : Short F ((v:ℚ)/2^F) := by
    refine ⟨⟨(v:ℤ),by simp⟩,by positivity,(div_le_iff₀ (by positivity)).mpr ?_⟩
    rw [mul_comm]
    exact_mod_cast hv
  change Short F ((a:ℚ)/2^F) ∧ Short F (((if _ then a else a+1 : ℕ):ℚ)/2^F)
  constructor
  · exact spec a b.le
  · split
    · exact spec a b.le
    · exact spec (a+1) b

private theorem steps_range (E : System (Fin m) ℚ) (S : ℕ) (ts : List (Fin m × Fin S))
    (Y : Fin m → ℚ) (hl : ∀ x, 0 ≤ E.lower x ∧ E.lower x ≤ 2)
    (hu : ∀ x, 0 ≤ E.upper x ∧ E.upper x ≤ 2) (hy : ∀ x, 0 ≤ Y x ∧ Y x ≤ 2) (x : Fin m) :
    0 ≤ FiniteAveraging.fullSteps E S ts Y x ∧ FiniteAveraging.fullSteps E S ts Y x ≤ 2 := by
  let fixed (q : ℚ) : System (Fin m) ℚ := ⟨fun _ => q,fun _ => q,E.edge⟩
  have exactFixed (q : ℚ) : FiniteAveraging.fullSteps (fixed q) S ts (fun _ => q) x = q := by
    have ok := OperandBounds.fullSteps_feasible (fixed q) S ts (fun _ => q)
      ⟨fun _ => ⟨le_rfl,le_rfl⟩, fun _ _ _ => le_rfl⟩
    exact le_antisymm (ok.1 x).2 (ok.1 x).1
  have lo := PolylogEnclosure.fullSteps_le_add (fixed 0) E rfl 0 (fun i => by simpa using (hl i).1)
    (fun i => by simpa using (hu i).1) S ts (fun _ => 0) Y (fun i => by simpa using (hy i).1) x
  have hi := PolylogEnclosure.fullSteps_le_add E (fixed 2) rfl 0 (fun i => by simpa using (hl i).2)
    (fun i => by simpa using (hu i).2) S ts Y (fun _ => 2) (fun i => by simpa using (hy i).2) x
  simpa only [exactFixed,add_zero] using And.intro lo hi

private theorem steps_short (E : StoredSystem m) (F s : ℕ) (ts : List (Fin m × Fin (2^s)))
    (Y : Vector ℚ m) (hl : ∀ i, Short F (E.system.lower i)) (hu : ∀ i, Short F (E.system.upper i))
    (hy : ∀ i, Short F (values Y i)) (i : Fin m) :
    Short (F+ts.length*s) (values (EnclosureWork.fullSteps E (2^s) ts Y).value i) := by
  rw [EnclosureWork.fullSteps_value]
  exact ⟨fullSteps_onDyadicGrid E.system F s ts (values Y) (fun x => (hl x).1)
    (fun x => (hu x).1) (fun x => (hy x).1) i,
    steps_range _ _ _ _ (fun x => (hl x).2) (fun x => (hu x).2) (fun x => (hy x).2) i⟩

private theorem round_work (J : Interval) (F : ℕ) (hl : J.1 < J.2) (hu : J.2 - J.1 < 4)
    (hg : OnDyadicGrid F J.1 ∧ OnDyadicGrid F J.2) : (RoundingWork.roundUp J).work ≤ 6*F+28 := by
  by_cases small : J.2-J.1 < 1
  · have w := Precision.interval_width_ge hg.1 hg.2 hl
    have cap : ⌈(J.2-J.1)⁻¹⌉₊ ≤ 2^F := by
      apply Nat.ceil_le.mpr
      push_cast
      rw [← one_div, div_le_iff₀ (by linarith)]
      rw [mul_comm]
      exact (div_le_iff₀ (by positivity)).mp w
    have c := Nat.clog_le_of_le_pow cap
    rw [RoundingWork.roundUp_work J small,RoundingWork.roundingExponent_eq_clog small]
    omega
  · have cap : ⌊J.2-J.1⌋₊ < 4 := (Nat.floor_lt (by linarith)).2 (by exact_mod_cast hu)
    have cc : Nat.log 2 ⌊J.2-J.1⌋₊ ≤ 2 := (Nat.log_mono_right (by omega : ⌊J.2-J.1⌋₊ ≤ 4)).trans (by decide)
    simp only [RoundingWork.roundUp,RoundingWork.zpowTwo_work,RoundingWork.integerLog,
      le_of_not_gt small,if_true,StateWork.logTwo_value,StateWork.logTwo_work,Int.natAbs_natCast]
    omega

private theorem anchor_bound (L U : StoredSystem m) (F s : ℕ) (ts : List (Fin m)) (x : Fin m)
    (ll : ∀ i, Short F (L.system.lower i)) (lu : ∀ i, Short F (L.system.upper i))
    (ul : ∀ i, Short F (U.system.lower i)) (uu : ∀ i, Short F (U.system.upper i)) :
    (anchorTest L U (2^s) ts x).work ≤ listBound m (2^s) ts.length +
      72*((2^s)^ts.length+1)^2 + 6*(F+ts.length*s)+30 := by
  let S := 2^s
  let entries := evaluate L U S ts
  let data := PrimitiveWork.map (fun v => (⟨coords v x,3⟩ : Result _)) entries.value
  have len : entries.value.length = S ^ ts.length := by simp [entries,evaluate,EnclosureWork.words_length]
  have size : data.value.length = S ^ ts.length := by simp [data,len]
  have vals (I : Interval) (hI : I ∈ data.value) :
      Short (F+ts.length*s) I.1 ∧ Short (F+ts.length*s) I.2 := by
    simp only [data,entries,evaluate,PrimitiveWork.map_value,List.mem_map] at hI
    obtain ⟨_,⟨word,_,rfl⟩,rfl⟩ := hI
    have lo := steps_short L F s (word.assign ts).value L.lower ll lu ll x
    have hi := steps_short U F s (word.assign ts).value U.upper ul uu uu x
    rw [Word.assign_length] at lo hi
    exact ⟨lo,hi⟩
  have ce := evaluate_work L U S (by dsimp [S]; positivity) ts
  have cm := PrimitiveWork.map_work_le (fun v => (⟨coords v x,3⟩ : Result _)) entries.value 3
    (fun _ _ => le_rfl)
  have ct := CertificateWork.centralInterval_work data.value
  change entries.work ≤ _ at ce
  change data.work ≤ _ at cm
  rw [len] at cm
  rw [size] at ct
  change (match (CertificateWork.centralInterval data.value).value with
    | none => ⟨none,entries.work+data.work+(CertificateWork.centralInterval data.value).work+1⟩
    | some J => ⟨some (RoundingWork.roundUp J).value,entries.work+data.work+
      (CertificateWork.centralInterval data.value).work+(RoundingWork.roundUp J).work+1⟩ : Result _).work ≤ _
  split
  · dsimp only [S] at *; nlinarith
  · rename_i J hJ
    rw [CertificateWork.centralInterval_value] at hJ
    have hg := Precision.centralInterval_onGrid (F+ts.length*s) (fun I hI =>
      ⟨(vals I hI).1.1,(vals I hI).2.1⟩) hJ
    have bounds := Precision.centralInterval_interior (l := -1) (r := 3) (fun I hI =>
      And.intro (lt_of_lt_of_le (by norm_num : (-1:ℚ) < 0) (vals I hI).2.2.1)
        (lt_of_le_of_lt (vals I hI).1.2.2 (by norm_num : (2:ℚ)<3))) hJ
    have r := round_work J _ (centralInterval_inside hJ).1 (by linarith [bounds.1,bounds.2]) hg
    dsimp only [S] at *; nlinarith

theorem heapCentral_work_raw (H : Heap) (zero : ℕ → ℕ) (height D F s : ℕ)
    (lo hi : Vector ℕ m) (edges : SparseClosure.Table m) (ts : List (Fin m)) (x : Fin m) :
    (heapCentral H zero height D F s lo hi edges ts x).work ≤
      2*m*(readBound height F+2)+8*m+2+listBound m (2^s) ts.length+
      72*((2^s)^ts.length+1)^2+6*(F+ts.length*s)+31 := by
  let t := tables H zero height D F lo hi edges
  have l (i : Fin m) := read_short H zero height D F lo[i]
  have u (i : Fin m) := read_short H zero height D F hi[i]
  have a := anchor_bound t.value.1 t.value.2 F s ts x
    (fun i => by simpa [t,tables,StoredSystem.system] using (l i).1)
    (fun i => by simpa [t,tables,StoredSystem.system] using (u i).1)
    (fun i => by simpa [t,tables,StoredSystem.system] using (l i).2)
    (fun i => by simpa [t,tables,StoredSystem.system] using (u i).2)
  have ht := tables_work H zero height D F lo hi edges
  change t.work ≤ _ at ht
  change t.work + (anchorTest t.value.1 t.value.2 _ ts x).work + 1 ≤ _
  omega



def kernelBound (h level B : ℕ) := 2*(7*B+4)+2*B*(4*h+3)+3+
  2*B*(readBound level B+2)+8*B+2+readBound level B+1000*(B+1)^5+
  72*(B+1)^2+6*B+35

def stageBound (h level B : ℕ) := (8*h+2*B+10)*(20000*(B+1)^7) + kernelBound h level B

private theorem index_work (p : Prepared n m) (x : Fin n) (f : Fin m → Result (Option α)) (b : ℕ)
    (hf : ∀ i, (f i).work ≤ b) : (withIndex p x f).work ≤ 7*m+4+b := by
  have cap := queryIndex_work p.embedding x
  simp only [withIndex]
  split
  · rename_i j _; have := hf j; omega
  · change (queryIndex p.embedding x).work+0+2 ≤ _
    omega

private theorem walls_work (w : PolylogWallTables.Walls ℕ h) (p : Prepared n m)
    (f : Vector ℕ m → Vector ℕ m → Result α) (b : ℕ) (hf : ∀ lo hi, (f lo hi).work ≤ b) :
    (withWalls w p f).work ≤ 2*m*(4*h+3)+3+b := by
  have aw := addresses_work w p.embedding
  have t := hf (addresses w p.embedding).value.1 (addresses w p.embedding).value.2
  simp only [withWalls]
  omega

/-- Bounds shared by each call after the graph has been reindexed. -/
structure Caps (P : Params) (m length B : ℕ) : Prop where
  vertices : m ≤ B
  length_le : length ≤ B
  precision : P.grid + length*P.exponent ≤ B
  words : (2^P.exponent)^length ≤ B

theorem Caps.list {P : Params} {m l B : ℕ} (c : Caps P m l B) :
    listBound m (2^P.exponent) l ≤ 1000*(B+1)^5 := by
  unfold listBound endpointBound
  calc
    _ ≤ 20*(B+1)*B + B*(2*(B*(60*(B+1)+5)+5)+3)+1 := by
      gcongr <;> first | exact c.words | exact c.length_le | exact c.vertices
    _ ≤ _ := by ring_nf; omega

private theorem readBound_mono (l : ℕ) {a b : ℕ} (h : a ≤ b) : readBound l a ≤ readBound l b := by
  unfold readBound
  gcongr

private def heapBound (l B : ℕ) := 2*B*(readBound l B+2)+8*B+2+readBound l B+
  1000*(B+1)^5+72*(B+1)^2+6*B+35

section Call
variable (w : PolylogWallTables.Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D : ℕ)
  (P : Params) (p : Prepared n m) (B : ℕ) (c : Caps P m p.schedule.length B)

include c

private theorem pairAt_work (x y : Fin n) :
    (pairAtWith w heap zero level D P x y p).work ≤ kernelBound h level B := by
  have bound (i j : Fin m) (lo hi : Vector ℕ m) :
      (heapPair heap zero level D P.grid P.exponent lo hi p.data.edge p.schedule P.k i j).work ≤ heapBound level B := by
    have a := heapPair_work heap zero level D P.grid P.exponent lo hi p.data.edge p.schedule P.k i j
    have hv := c.vertices
    have words := c.words
    have read := readBound_mono level (show P.grid ≤ B from (Nat.le_add_right ..).trans c.precision)
    have bds : 2*m*(readBound level P.grid+2) ≤ 2*B*(readBound level B+2) := by gcongr
    unfold heapBound
    nlinarith [c.list]
  have r := index_work p x _ _ (fun i => index_work p y _ _ (fun j =>
    walls_work w p _ _ (bound i j)))
  apply r.trans
  unfold kernelBound heapBound
  have := c.vertices
  have tables : 2*m*(4*h+3) ≤ 2*B*(4*h+3) := by gcongr
  omega

private theorem thresholdAt_work (x : Fin n) (addr : ℕ) :
    (thresholdAtWith w heap zero level D P x addr p).work ≤ kernelBound h level B := by
  have bound (i : Fin m) (lo hi : Vector ℕ m) :
      (heapThreshold heap zero level D P.grid P.exponent lo hi p.data.edge p.schedule P.k i addr).work ≤ heapBound level B := by
    have a := heapThreshold_work heap zero level D P.grid P.exponent lo hi p.data.edge p.schedule P.k i addr
    have hv := c.vertices
    have words := c.words
    have read := readBound_mono level (show P.grid ≤ B from (Nat.le_add_right ..).trans c.precision)
    have bds : 2*m*(readBound level P.grid+2) ≤ 2*B*(readBound level B+2) := by gcongr
    unfold heapBound
    nlinarith [c.list, readBound_mono level c.precision]
  have r := index_work p x _ _ (fun i => walls_work w p _ _ (bound i))
  apply r.trans
  unfold kernelBound heapBound
  have := c.vertices
  have tables : 2*m*(4*h+3) ≤ 2*B*(4*h+3) := by gcongr
  omega

private theorem centralAt_work (x : Fin n) :
    (centralAtWith w heap zero level D P x p).work ≤ kernelBound h level B := by
  have bound (i : Fin m) (lo hi : Vector ℕ m) :
      (heapCentral heap zero level D P.grid P.exponent lo hi p.data.edge p.schedule i).work ≤ heapBound level B := by
    have a := heapCentral_work_raw heap zero level D P.grid P.exponent lo hi p.data.edge p.schedule i
    have hv := c.vertices
    have read := readBound_mono level (show P.grid ≤ B from (Nat.le_add_right ..).trans c.precision)
    have bds : 2*m*(readBound level P.grid+2) ≤ 2*B*(readBound level B+2) := by gcongr
    have prec := c.precision
    have lst := c.list
    have wd := Nat.pow_le_pow_left (Nat.add_le_add_right c.words 1) 2
    unfold heapBound
    omega
  have r := index_work p x _ _ (fun i => walls_work w p _ _ (bound i))
  apply r.trans
  unfold kernelBound heapBound
  have := c.vertices
  have tables : 2*m*(4*h+3) ≤ 2*B*(4*h+3) := by gcongr
  omega

end Call


open PolylogSchedule PolylogCompareWork PolylogRows PolylogWallTables

variable (extra : CappedArithmetic.Expr) (hk : 64 ≤ parameter extra n)
  {g : Graph n h} (sh : Shape g (parameter extra n))

include hk in
private theorem admitted_caps (A : System (Fin n) ℚ) (Q : Finset (Fin n)) (hQ : Q.card ≤ 2)
    (degree : ∀ x, (GraphBalls.neighbors A.edge x).card ≤ parameter extra n) :
    let k := parameter extra n
    let H := ArbitraryLabels.pathHeight k
    let hp : 0 < k := (by decide : 0 < 64).trans_le hk
    let m := (Neighborhood.labels A k H hp (halfWidth k) (width_pos k) Q).card
    let l := (Neighborhood.schedule A k H hp (halfWidth k) (width_pos k) Q).length
    Caps (Params.stage k) m l (Parameters.logCap n) := by
  let k := parameter extra n
  let H := ArbitraryLabels.pathHeight k
  let B := Parameters.logCap n
  let hp : 0 < k := (by decide : 0 < 64).trans_le hk
  let l := (Neighborhood.schedule A k H hp (halfWidth k) (width_pos k) Q).length
  have words : EnclosureParameters.alphabet k H ^ l ≤ B :=
    (PolylogLocalBudget.word_count extra A hk Q hQ degree).trans (admitted_costs hk).1
  have vertices := PolylogLocalBudget.vertex_count extra A hk Q hQ degree
  have precision := PolylogLocalBudget.endpoint_precision extra A hk Q hQ degree
  have s4 : 4 ≤ EnclosureParameters.alphabet k H :=
    Nat.le_of_dvd (EnclosureParameters.alphabet_pos k H) (EnclosureParameters.four_dvd_alphabet k H)
  have length : l ≤ B := (Nat.lt_two_pow_self (n := l)).le.trans
    ((Nat.pow_le_pow_left ((by decide : 2 ≤ 4).trans s4) l).trans words)
  dsimp only
  constructor
  · exact vertices
  · exact length
  · simp only [Params.stage]
    exact precision
  · simp only [Params.stage]
    simpa only [EnclosureParameters.alphabet,k,H,l,B] using words

set_option maxHeartbeats 800000 in
include hk sh in
private theorem run_stage (level : ℕ) (roots : List (Fin n)) (nr : roots.length ≤ 2)
    (f : ∀ {m}, Prepared n m → Result (Option α))
    (hf : ∀ {m} (p : Prepared n m),
      Caps (Params.stage (parameter extra n)) m p.schedule.length (Parameters.logCap n) →
      (f p).work ≤ kernelBound h level (Parameters.logCap n)) :
    (run g (parameter extra n) roots f).work ≤ stageBound h level (Parameters.logCap n) := by
  let B := Parameters.logCap n
  let k := parameter extra n
  have kp : 0 < k := by dsimp [k]; omega
  let H := ArbitraryLabels.pathHeight k
  let t := Neighborhood.sweeps k H kp (halfWidth k) (width_pos k)
  have rowBounds := sh.bounded
  obtain ⟨E,vg,hl,degree⟩ := sh
  let A : System (Fin n) ℚ := ⟨fun _ => 0,fun _ => 0,E⟩
  have good : g.Valid A.edge := vg
  have adj := adjacent_mem g A good hl
  let p := calibrated (reads g) A (adjacent g) adj roots k H kp (halfWidth k) (width_pos k)
  have cost := withPrepared_eq (reads g) A (adjacent g) adj roots (H*t) t (8*h+2*k+10) @f
  change (runWith g (Params.stage k) roots f).work ≤ _
  simp only [runWith,Params.stage,dif_pos kp,if_pos kp]
  change (withPrepared (reads g) (adjacent g) roots (H*t) t (8*h+2*k+10) f).work ≤ _
  rw [cost]
  change (8*h+2*k+10)*p.work+(f p.value).work ≤ _
  have pr := prepare_work (reads g) A (adjacent g) adj roots (H*t) t (2*k) 1
    (fun x => by
      change (PolylogRepair.prev g x ++ PolylogRepair.nextRow g x).length ≤ 2*k
      rw [List.length_append]
      exact (Nat.add_le_add (rowBounds.2 x) (rowBounds.1 x)).trans (by dsimp only [k]; omega))
    (fun x => (rowBounds.1 x).trans (by dsimp only [k]; omega)) (fun _ => le_rfl) (fun _ => le_rfl)
  change p.work ≤ _ at pr
  have cprep := totalCost_stage extra n roots.length 1 nr hk
  change totalCost (2*k) 1 roots.length (H*t) t ≤ 10000*(B+1)^7*(1+1) at cprep
  have kcap := (stage_bounds extra n roots.length nr hk).2.2.2
  have hQ : roots.toFinset.card ≤ 2 := (List.toFinset_card_le _).trans nr
  have sched := calibrated_schedule (reads g) A (reads_edge g A good) (adjacent g) adj roots k H kp
    (halfWidth k) (width_pos k)
  change p.value.schedule = _ at sched
  have cs := admitted_caps extra hk A roots.toFinset hQ degree
  have caps : Caps (Params.stage k) (Neighborhood.labels A k H kp (halfWidth k) (width_pos k) roots.toFinset).card p.value.schedule.length B :=
    Eq.mpr (congrArg (fun ts => Caps (Params.stage k)
      (Neighborhood.labels A k H kp (halfWidth k) (width_pos k) roots.toFinset).card (List.length ts) B) sched) cs
  have output := hf p.value caps
  change (8*h+2*k+10)*p.work+(f p.value).work ≤ (8*h+2*B+10)*(20000*(B+1)^7)+_
  apply Nat.add_le_add _ output
  apply Nat.mul_le_mul
  · change k ≤ B at kcap
    omega
  · exact (pr.trans cprep).trans (by ring_nf; omega)

variable (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D : ℕ)
include hk sh

theorem pair_work (x y : Fin n) :
    (pair g w heap zero level D (parameter extra n) x y).work ≤ stageBound h level (Parameters.logCap n) :=
  run_stage extra hk sh level [x,y] (by simp) _ (fun p c => pairAt_work w heap zero level D _ p _ c x y)

theorem threshold_work (x : Fin n) (addr : ℕ) :
    (threshold g w heap zero level D (parameter extra n) x addr).work ≤ stageBound h level (Parameters.logCap n) :=
  run_stage extra hk sh level [x] (by simp) _ (fun p c => thresholdAt_work w heap zero level D _ p _ c x addr)

theorem central_work (x : Fin n) :
    (central g w heap zero level D (parameter extra n) x).work ≤ stageBound h level (Parameters.logCap n) :=
  run_stage extra hk sh level [x] (by simp) _ (fun p c => centralAt_work w heap zero level D _ p _ c x)

end SortingAdversary.Continuous.PolylogTestWork
