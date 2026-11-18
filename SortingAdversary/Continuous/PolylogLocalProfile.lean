import SortingAdversary.Continuous.PolylogPrefixProfile
import SortingAdversary.Continuous.PolylogTestWork

/-! Composing measured short scalar operations with the sparse neighbor and address lookup code. -/

namespace SortingAdversary.Continuous.PolylogLocalProfile

open PolylogPrepared PolylogTestWork PolylogBits PolylogNeighborhood PolylogRows PolylogWallTables
open FiniteAveraging PolylogEnclosureWork PolylogOracleWork EnclosureWork Certificates OperandBounds
open Optimal
open PrimitiveWork (Result)

variable {n h m : ℕ}

structure Kernels where
  sweep : {m : ℕ} → StoredSystem m → StoredSystem m → ℕ → List (Fin m) →
    Result (List (Vector ℚ m × Vector ℚ m))
  answer : ℕ → List ComparisonIntervals → Result (Option Answer)
  anchor : List Interval → Result (Option ℚ)

structure Correct (K : Kernels) : Prop where
  sweep : ∀ {m} (L U : StoredSystem m) S ts, (K.sweep L U S ts).value =
    (PolylogEnclosureWork.evaluate L U S ts).value
  answer : ∀ k L, (K.answer k L).value = Certificates.selectAnswer k L
  anchor : ∀ L, (K.anchor L).value = (Certificates.centralInterval L).map Certificates.roundUp

def sweepCap (B : ℕ) := 100000000*(B+2)^6

def certCap (B : ℕ) := 200*(B+1)^2*(128*(200*(B+2)+1)^3+1)

structure Priced (K : Kernels) : Prop where
  sweep : ∀ {m} (L U : StoredSystem m) (F s B : ℕ) (ts : List (Fin m)),
    (∀ i, Short F (L.system.lower i)) → (∀ i, Short F (L.system.upper i)) →
    (∀ i, Short F (U.system.lower i)) → (∀ i, Short F (U.system.upper i)) →
    m ≤ B → ts.length ≤ B → F+ts.length*s ≤ B → (2^s)^ts.length ≤ B →
    (K.sweep L U (2^s) ts).work ≤ sweepCap B
  answer : ∀ k (L : List ComparisonIntervals) B, k ≤ B → L.length ≤ B →
    (∀ I ∈ L, Fits (B+1) I.1.1 ∧ Fits (B+1) I.1.2 ∧ Fits (B+1) I.2.1 ∧ Fits (B+1) I.2.2) →
    (K.answer k L).work ≤ certCap B
  anchor : ∀ (L : List Interval) B, L.length ≤ B →
    (∀ I ∈ L, Fits (B+1) I.1 ∧ Fits (B+1) I.2) → (K.anchor L).work ≤ certCap B

def withEntries (K : Kernels) (H : Heap) (zero : ℕ → ℕ) (level D : ℕ) (P : Params)
    (lo hi : Vector ℕ m) (edges : SparseClosure.Table m) (ts : List (Fin m))
    (f : List (Vector ℚ m × Vector ℚ m) → Result α) : Result α :=
  let walls := PolylogPrefixProfile.tables H zero level D P.grid lo hi edges
  let entries := K.sweep walls.value.1 walls.value.2 (2^P.exponent) ts
  let use := f entries.value
  ⟨use.value,walls.work+entries.work+use.work+3⟩

def useAnswer (K : Kernels) (k : ℕ) (p : Probe m) (V : List (Vector ℚ m × Vector ℚ m)) : Result (Option Answer) :=
  let data := PrimitiveWork.map (fun v => ⟨p.inputs (coords v),7⟩) V
  let t := K.answer k data.value
  ⟨t.value,data.work+t.work+1⟩

def useCentral (K : Kernels) (x : Fin m) (V : List (Vector ℚ m × Vector ℚ m)) : Result (Option ℚ) :=
  let data := PrimitiveWork.map (fun v => ⟨coords v x,3⟩) V
  let t := K.anchor data.value
  ⟨t.value,data.work+t.work+1⟩

def useThreshold (K : Kernels) (heap : Heap) (zero : ℕ → ℕ) (level D : ℕ) (P : Params)
    (len addr : ℕ) (i : Fin m) (V : List (Vector ℚ m × Vector ℚ m)) : Result (Option Answer) :=
  let cut := PolylogPrefixProfile.read heap zero level addr D (P.grid+len*P.exponent)
  let ans := useAnswer K P.k (.threshold i cut.value.2 cut.value.1) V
  ⟨ans.value,cut.work+ans.work+2⟩

def onPair (K : Kernels) (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D : ℕ)
    (P : Params) (x y : Fin n) (p : Prepared n m) : Result (Option Answer) :=
  withIndex p x fun i => withIndex p y fun j => withWalls w p fun lo hi =>
    withEntries K heap zero level D P lo hi p.data.edge p.schedule (useAnswer K P.k (.pair i j))

def onThreshold (K : Kernels) (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D : ℕ)
    (P : Params) (x : Fin n) (c : ℕ) (p : Prepared n m) : Result (Option Answer) :=
  withIndex p x fun i => withWalls w p fun lo hi =>
    withEntries K heap zero level D P lo hi p.data.edge p.schedule
      (useThreshold K heap zero level D P p.schedule.length c i)

def onCentral (K : Kernels) (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D : ℕ)
    (P : Params) (x : Fin n) (p : Prepared n m) : Result (Option ℚ) :=
  withIndex p x fun i => withWalls w p fun lo hi =>
    withEntries K heap zero level D P lo hi p.data.edge p.schedule (useCentral K i)

def pair (K : Kernels) (g : Graph n h) (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D : ℕ)
    (P : Params) (x y : Fin n) := runWith g P [x,y] (onPair K w heap zero level D P x y)

def threshold (K : Kernels) (g : Graph n h) (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D : ℕ)
    (P : Params) (x : Fin n) (c : ℕ) := runWith g P [x] (onThreshold K w heap zero level D P x c)

def central (K : Kernels) (g : Graph n h) (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D : ℕ)
    (P : Params) (x : Fin n) := runWith g P [x] (onCentral K w heap zero level D P x)

private theorem run_congr (g : Graph n h) (P : Params) (roots : List (Fin n))
    (f u : ∀ {m}, Prepared n m → Result (Option α)) (eq : ∀ {m} (p : Prepared n m), (f p).value = (u p).value) :
    (runWith g P roots f).value = (runWith g P roots u).value := by
  unfold runWith
  split
  · exact eq _
  · rfl

private theorem index_congr (p : Prepared n m) (x : Fin n) (f u : Fin m → Result (Option α))
    (eq : ∀ i, (f i).value = (u i).value) : (withIndex p x f).value = (withIndex p x u).value := by
  simp only [withIndex]; split <;> first | apply eq | rfl

section Values
variable {K : Kernels} (ok : Correct K) (g : Graph n h) (w : Walls ℕ h) (heap : Heap)
  (zero : ℕ → ℕ) (level D : ℕ) (P : Params)
include ok

theorem pair_value (x y : Fin n) : (pair K g w heap zero level D P x y).value =
    (PolylogPrepared.pairWith g w heap zero level D P x y).value := by
  refine run_congr _ _ _ _ _ (fun p => index_congr _ _ _ _ (fun i => index_congr _ _ _ _ (fun j => ?_)))
  simp only [withWalls,withEntries,ok.sweep,PolylogPrefixProfile.tables_value,useAnswer,ok.answer,
    heapPair,answerTest,CertificateWork.selectAnswer_value]

theorem threshold_value (x : Fin n) (c : ℕ) : (threshold K g w heap zero level D P x c).value =
    (PolylogPrepared.thresholdWith g w heap zero level D P x c).value := by
  refine run_congr _ _ _ _ _ (fun p => index_congr _ _ _ _ (fun i => ?_))
  simp only [withWalls,withEntries,ok.sweep,PolylogPrefixProfile.tables_value,useThreshold,
    PolylogPrefixProfile.read_value,useAnswer,ok.answer,heapThreshold,answerTest,CertificateWork.selectAnswer_value]

theorem central_value (x : Fin n) : (central K g w heap zero level D P x).value =
    (PolylogPrepared.centralWith g w heap zero level D P x).value := by
  refine run_congr _ _ _ _ _ (fun p => index_congr _ _ _ _ (fun i => ?_))
  simp only [withWalls,withEntries,ok.sweep,PolylogPrefixProfile.tables_value,useCentral,ok.anchor,
    heapCentral,anchorTest,CertificateWork.centralInterval_value]
  split <;> simp_all

end Values


private abbrev ShortList (G B : ℕ) (V : List (Vector ℚ m × Vector ℚ m)) :=
  V.length ≤ B ∧ ∀ v ∈ V, ∀ i, Short G (coords v i).1 ∧ Short G (coords v i).2

private def probeFits (p : Probe m) (B : ℕ) : Prop :=
  match p with
  | .pair .. => True
  | .threshold _ a b => Fits (B+3) a ∧ Fits (B+3) b

private theorem useAnswer_work {K : Kernels} (price : Priced K) (k B G : ℕ) (hk : k ≤ B)
    (g : G ≤ B) (p : Probe m) (hp : probeFits p B) (V : List (Vector ℚ m × Vector ℚ m))
    (hv : ShortList G B V) : (useAnswer K k p V).work ≤ 9*B+certCap (B+2)+2 := by
  let data := PrimitiveWork.map (fun v : Vector ℚ m × Vector ℚ m => (⟨p.inputs (coords v),7⟩ : Result _)) V
  have le := PrimitiveWork.map_work_le (fun v : Vector ℚ m × Vector ℚ m => (⟨p.inputs (coords v),7⟩ : Result _))
    V 7 (fun _ _ => le_rfl)
  have fit (v) (mem : v ∈ V) (i) : Fits (B+3) (coords v i).1 ∧ Fits (B+3) (coords v i).2 :=
    ⟨(hv.2 v mem i).1.fits.mono (by omega),(hv.2 v mem i).2.fits.mono (by omega)⟩
  have ct := price.answer k data.value (B+2) (by omega) (by simpa [data] using hv.1.trans (Nat.le_add_right B 2))
    (fun I hI => by
      obtain ⟨v,mem,rfl⟩ := List.mem_map.mp (by simpa only [data,PrimitiveWork.map_value] using hI)
      cases p with
      | pair i j => exact ⟨(fit v mem i).1,(fit v mem i).2,fit v mem j⟩
      | threshold i a b => exact ⟨(fit v mem i).1,(fit v mem i).2,hp⟩)
  change data.work ≤ _ at le
  change data.work+(K.answer k data.value).work+1 ≤ _
  have := hv.1
  omega

private theorem useCentral_work {K : Kernels} (price : Priced K) (B G : ℕ) (g : G ≤ B)
    (x : Fin m) (V : List (Vector ℚ m × Vector ℚ m)) (hv : ShortList G B V) :
    (useCentral K x V).work ≤ 9*B+certCap (B+2)+2 := by
  let data := PrimitiveWork.map (fun v : Vector ℚ m × Vector ℚ m => (⟨coords v x,3⟩ : Result _)) V
  have le := PrimitiveWork.map_work_le (fun v : Vector ℚ m × Vector ℚ m => (⟨coords v x,3⟩ : Result _))
    V 3 (fun _ _ => le_rfl)
  have ct := price.anchor data.value (B+2) (by simpa [data] using hv.1.trans (Nat.le_add_right B 2))
    (fun I hI => by
      obtain ⟨v,mem,rfl⟩ := List.mem_map.mp (by simpa only [data,PrimitiveWork.map_value] using hI)
      exact ⟨(hv.2 v mem x).1.fits.mono (by omega),(hv.2 v mem x).2.fits.mono (by omega)⟩)
  change data.work ≤ _ at le
  change data.work+(K.anchor data.value).work+1 ≤ _
  have := hv.1
  omega

private theorem prefix_mono (T level : ℕ) {G B : ℕ} (g : G ≤ B) :
    PolylogPrefixProfile.bound T level G ≤ PolylogPrefixProfile.bound T level B := by
  unfold PolylogPrefixProfile.bound PolylogPrefix.readBound
  gcongr

private def useCap (level T B : ℕ) := PolylogPrefixProfile.bound T level B+9*B+certCap (B+2)+4

private def entriesCap (level T B : ℕ) := 2*B*(PolylogPrefixProfile.bound T level B+2)+8*B+2+
  sweepCap B+useCap level T B+3

def localCap (h level T B : ℕ) := 2*(7*B+4)+2*B*(4*h+3)+3+entriesCap level T B

def total (h level T B : ℕ) := (8*h+2*B+10)*(20000*(B+1)^7)+localCap h level T B

theorem total_eq (h level T B : ℕ) : total h level T B = (8*h+2*B+10)*(20000*(B+1)^7)+
    2*(7*B+4)+2*B*(4*h+3)+3+2*B*(PolylogPrefixProfile.bound T level B+2)+8*B+2+
    sweepCap B+PolylogPrefixProfile.bound T level B+9*B+certCap (B+2)+7 := by
  unfold total localCap entriesCap useCap; omega

private theorem withEntries_work {K : Kernels} (ok : Correct K) (price : Priced K)
    (H : Heap) (zero : ℕ → ℕ) (level D : ℕ) (P : Params)
    (lo hi : Vector ℕ m) (edges : SparseClosure.Table m) (ts : List (Fin m))
    (B T : ℕ) (v : H.Valid) (pos : 0<T) (fits : H.next < 2^T) (c : Caps P m ts.length B)
    (use : List (Vector ℚ m × Vector ℚ m) → Result α)
    (hu : ∀ V, ShortList (P.grid+ts.length*P.exponent) B V → (use V).work ≤ useCap level T B) :
    (withEntries K H zero level D P lo hi edges ts use).work ≤ entriesCap level T B := by
  let t := PolylogPrefixProfile.tables H zero level D P.grid lo hi edges
  let e := K.sweep t.value.1 t.value.2 (2^P.exponent) ts
  have hl := tables_short H zero level D P.grid lo hi edges
  dsimp only at hl
  rw [← PolylogPrefixProfile.tables_value] at hl
  change (∀ i, Short P.grid (t.value.1.system.lower i)) ∧ _ at hl
  have hw := price.sweep t.value.1 t.value.2 _ _ B ts hl.1 hl.2.1 hl.2.2.1 hl.2.2.2
    c.vertices c.length_le c.precision c.words
  have hlen : e.value.length = (2^P.exponent)^ts.length := by
    simp only [e, ok.sweep, PolylogEnclosureWork.evaluate,PrimitiveWork.map_value,List.length_map,EnclosureWork.words_length]
  have hc := hu e.value ⟨hlen.le.trans c.words, fun u mem x => by
    rw [show e.value = _ from ok.sweep ..] at mem
    exact evaluated_short _ _ _ _ _ hl.1 hl.2.1 hl.2.2.1 hl.2.2.2 mem x⟩
  have cost := PolylogPrefixProfile.tables_work H v zero level D P.grid T pos fits lo hi edges
  have pm := prefix_mono T level (show P.grid ≤ B from (Nat.le_add_right ..).trans c.precision)
  have bv := c.vertices
  have bcost : 2*m*(PolylogPrefixProfile.bound T level P.grid+2) ≤ 2*B*(PolylogPrefixProfile.bound T level B+2) := by gcongr
  change t.work ≤ _ at cost
  change e.work ≤ _ at hw
  change t.work+e.work+(use e.value).work+3 ≤ _
  unfold entriesCap
  omega

section Stored
variable {K : Kernels} (ok : Correct K) (price : Priced K)
  (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D : ℕ) (P : Params)
  (p : Prepared n m) (B T : ℕ) (v : heap.Valid) (pos : 0<T) (fits : heap.next < 2^T)
  (c : Caps P m p.schedule.length B) (hk : P.k ≤ B)

private theorem cap_indices (c : m ≤ B) : 2*(7*m+4)+(2*m*(4*h+3)+3+entriesCap level T B) ≤ localCap h level T B := by
  unfold localCap
  have tables : 2*m*(4*h+3) ≤ 2*B*(4*h+3) := by gcongr
  omega

include ok price v pos fits c hk in
private theorem onPair_work (x y : Fin n) : (onPair K w heap zero level D P x y p).work ≤ localCap h level T B := by
  have use (i j : Fin m) V (hv : ShortList (P.grid+p.schedule.length*P.exponent) B V) :
      (useAnswer K P.k (.pair i j) V).work ≤ useCap level T B := by
    apply (useAnswer_work price _ _ _ hk c.precision (.pair i j) trivial V hv).trans
    unfold useCap; omega
  apply (index_work p x _ _ (fun i => index_work p y _ _ (fun j => walls_work w p _ _ (fun lo hi =>
    withEntries_work ok price heap zero level D P lo hi _ _ B T v pos fits c _ (use i j))))).trans
  have := cap_indices (h := h) (level := level) (B := B) (T := T) c.vertices
  omega

include ok price v pos fits c hk in
private theorem onThreshold_work (x : Fin n) (addr : ℕ) :
    (onThreshold K w heap zero level D P x addr p).work ≤ localCap h level T B := by
  have use (i : Fin m) V (hv : ShortList (P.grid+p.schedule.length*P.exponent) B V) :
      (useThreshold K heap zero level D P p.schedule.length addr i V).work ≤ useCap level T B := by
    let G := P.grid + p.schedule.length*P.exponent
    let cut := PolylogPrefixProfile.read heap zero level addr D G
    have sh := read_short heap zero level D G addr
    rw [← PolylogPrefixProfile.read_value] at sh
    have eq : G ≤ B := c.precision
    have good : probeFits (.threshold i cut.value.2 cut.value.1) B :=
      ⟨sh.2.fits.mono (by omega),sh.1.fits.mono (by omega)⟩
    have test := useAnswer_work price _ _ _ hk eq _ good V hv
    have rd := PolylogPrefixProfile.read_work heap v zero level addr D G T pos fits
    have bd := prefix_mono T level eq
    change cut.work ≤ _ at rd
    change cut.work+(useAnswer K P.k (.threshold i cut.value.2 cut.value.1) V).work+2 ≤ _
    unfold useCap
    omega
  apply (index_work p x _ _ (fun i => walls_work w p _ _ (fun lo hi =>
    withEntries_work ok price heap zero level D P lo hi _ _ B T v pos fits c _ (use i)))).trans
  have := cap_indices (h := h) (level := level) (B := B) (T := T) c.vertices
  omega

include ok price v pos fits c in
private theorem onCentral_work (x : Fin n) :
    (onCentral K w heap zero level D P x p).work ≤ localCap h level T B := by
  have use (i : Fin m) V (hv : ShortList (P.grid+p.schedule.length*P.exponent) B V) :
      (useCentral K i V).work ≤ useCap level T B := by
    apply (useCentral_work price _ _ c.precision i V hv).trans
    unfold useCap; omega
  apply (index_work p x _ _ (fun i => walls_work w p _ _ (fun lo hi =>
    withEntries_work ok price heap zero level D P lo hi _ _ B T v pos fits c _ (use i)))).trans
  have := cap_indices (h := h) (level := level) (B := B) (T := T) c.vertices
  omega

end Stored

open PolylogSchedule PolylogCompareWork

section Stage
variable {K : Kernels} (ok : Correct K) (price : Priced K) (extra : CappedArithmetic.Expr)
  (hk : 64 ≤ parameter extra n) {g : Graph n h} (sh : Shape g (parameter extra n))
  (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D T : ℕ)
  (v : heap.Valid) (pos : 0<T) (fits : heap.next < 2^T)
include ok price hk sh v pos fits

theorem pair_work (x y : Fin n) : (pair K g w heap zero level D (Params.stage (parameter extra n)) x y).work ≤
    total h level T (Parameters.logCap n) := by
  apply run_stage_priced extra hk sh _ _ (by simp)
  intro m p c
  exact onPair_work ok price _ _ _ _ _ _ p _ T v pos fits c ((stage_bounds extra n 2 (by decide) hk).2.2.2) x y

theorem threshold_work (x : Fin n) (addr : ℕ) :
    (threshold K g w heap zero level D (Params.stage (parameter extra n)) x addr).work ≤ total h level T (Parameters.logCap n) := by
  apply run_stage_priced extra hk sh _ _ (by simp)
  intro m p c
  exact onThreshold_work ok price _ _ _ _ _ _ p _ T v pos fits c ((stage_bounds extra n 1 (by decide) hk).2.2.2) x addr

theorem central_work (x : Fin n) : (central K g w heap zero level D (Params.stage (parameter extra n)) x).work ≤
    total h level T (Parameters.logCap n) := by
  apply run_stage_priced extra hk sh _ _ (by simp)
  intro m p c
  exact onCentral_work ok price _ _ _ _ _ _ p _ T v pos fits c x

end Stage

end SortingAdversary.Continuous.PolylogLocalProfile
