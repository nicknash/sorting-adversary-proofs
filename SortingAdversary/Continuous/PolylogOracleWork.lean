import SortingAdversary.Continuous.PolylogPrefix
import SortingAdversary.Continuous.SelectionKernelWork

/-!
# Finite comparison and central tests on prepared short inputs

For an exact threshold, comparing a short grid value strictly below it uses
its grid ceiling. Comparing strictly above uses its grid floor. Reading these
two short values once suffices for every digit word, including equality at
a grid point. The word-loop costs are independent of the original wall and
threshold precision.
-/

namespace SortingAdversary.Continuous.PolylogOracleWork

open SortingAdversary.Optimal FiniteAveraging Certificates PolylogEnclosure PolylogEnclosureWork
open EnclosureWork

variable {m : ℕ}

theorem below_gridCeil {G : ℕ} {q : ℚ} (hq : OnDyadicGrid G q) (c : ℚ) :
    q < PolylogEnclosure.roundUp G c ↔ q < c := by
  obtain ⟨z, rfl⟩ := hq
  have hp : (0 : ℚ) < 2 ^ G := by positivity
  rw [PolylogEnclosure.roundUp, div_lt_div_iff_of_pos_right hp, div_lt_iff₀ hp,
    Int.cast_lt, Int.lt_ceil]

theorem above_gridFloor {G : ℕ} {q : ℚ} (hq : OnDyadicGrid G q) (c : ℚ) :
    roundDown G c < q ↔ c < q := by
  obtain ⟨z, rfl⟩ := hq
  have hp : (0 : ℚ) < 2 ^ G := by positivity
  rw [roundDown, div_lt_div_iff_of_pos_right hp, lt_div_iff₀ hp,
    Int.cast_lt, Int.floor_lt]

/-- The two limits in the threshold variant are a ceiling and a floor,
in the order that the strict separation tests consume them. -/
inductive Probe (m : ℕ)
  | pair (x y : Fin m)
  | threshold (x : Fin m) (ceiling floor : ℚ)

def Probe.inputs (p : Probe m) (I : Fin m → Interval) : ComparisonIntervals :=
  match p with
  | .pair x y => (I x, I y)
  | .threshold x hi lo => (I x, (hi, lo))

theorem threshold_prefix_exact (R : List (Fin m → Interval)) (x : Fin m) (k G : ℕ) (c : ℚ)
    (hgrid : ∀ I ∈ R, OnDyadicGrid G (I x).1 ∧ OnDyadicGrid G (I x).2) :
    Certificates.selectAnswer k (R.map (Probe.inputs (.threshold x (PolylogEnclosure.roundUp G c)
      (roundDown G c)))) = Certificates.selectAnswer k (R.map (fun I => (I x, (c, c)))) := by
  let short := Probe.inputs (.threshold x (PolylogEnclosure.roundUp G c) (roundDown G c))
  let point := fun I : Fin m → Interval => (I x, (c, c))
  have low : (R.map short).countP separated = (R.map point).countP separated := by
    simp only [List.countP_map]
    apply List.countP_congr
    intro I hI
    simp [short, point, Probe.inputs, separated, below_gridCeil (hgrid I hI).2]
  have upp : (R.map short).countP reverseSeparated = (R.map point).countP reverseSeparated := by
    simp only [List.countP_map]
    apply List.countP_congr
    intro I hI
    simp [short, point, Probe.inputs, reverseSeparated, above_gridFloor (hgrid I hI).1]
  change Certificates.selectAnswer k (R.map short) = Certificates.selectAnswer k (R.map point)
  simp only [Certificates.selectAnswer, lowerFraction, upperFraction, List.length_map,
    List.isEmpty_map, low, upp]

/-- Both selected coordinate pairs and prepared threshold limits need at
most four vector reads and the pair constructors. -/
def answerTest (L U : StoredSystem m) (S : ℕ) (schedule : List (Fin m)) (k : ℕ) (p : Probe m) :
    PrimitiveWork.Result (Option Answer) :=
  let entries := evaluate L U S schedule
  let data := PrimitiveWork.map (fun v => ⟨p.inputs (coords v), 7⟩) entries.value
  let test := CertificateWork.selectAnswer k data.value
  ⟨test.value, entries.work + data.work + test.work⟩

theorem answerTest_value (D : System (Fin m) ℚ) (F : ℕ) (L U : StoredSystem m)
    (hL : L.system = mapWalls (roundDown F) D)
    (hU : U.system = mapWalls (PolylogEnclosure.roundUp F) D)
    (S : ℕ) (schedule : List (Fin m)) (k : ℕ) (p : Probe m) :
    (answerTest L U S schedule k p).value =
      Certificates.selectAnswer k ((roundedEnclose D F S schedule).map p.inputs) := by
  rw [← evaluate_value D F L U hL hU]
  simp only [answerTest, PrimitiveWork.map_value, CertificateWork.selectAnswer_value, List.map_map,
    Function.comp_def]

/-- The certificate on the two short limits makes the same choice as the
semantic program comparing all words directly against the exact anchor. -/
theorem thresholdTest_value (D : System (Fin m) ℚ) (F s : ℕ) (L U : StoredSystem m)
    (hL : L.system = mapWalls (roundDown F) D)
    (hU : U.system = mapWalls (PolylogEnclosure.roundUp F) D)
    (schedule : List (Fin m)) (k : ℕ) (x : Fin m) (c : ℚ) :
    let G := F + schedule.length * s
    (answerTest L U (2 ^ s) schedule k
      (.threshold x (PolylogEnclosure.roundUp G c) (roundDown G c))).value =
      Certificates.selectAnswer k ((roundedEnclose D F (2 ^ s) schedule).map (fun I => (I x, (c,c)))) := by
  dsimp only
  rw [answerTest_value D F L U hL hU]
  apply threshold_prefix_exact
  intro I hI
  obtain ⟨digits, _, rfl⟩ := List.mem_map.mp hI
  exact roundedEntry_grid D F s schedule digits x

private theorem evaluate_length (L U : StoredSystem m) (S : ℕ) (schedule : List (Fin m)) :
    (evaluate L U S schedule).value.length = S ^ schedule.length := by
  simp [evaluate, PrimitiveWork.map_value, EnclosureWork.words_length]

theorem answerTest_work (L U : StoredSystem m) (S : ℕ) (hS : 0 < S)
    (schedule : List (Fin m)) (k : ℕ) (p : Probe m) :
    (answerTest L U S schedule k p).work ≤ listBound m S schedule.length +
      30 * (S ^ schedule.length + 1) := by
  let entries := evaluate L U S schedule
  let data := PrimitiveWork.map (fun v => (⟨p.inputs (coords v), 7⟩ : PrimitiveWork.Result _)) entries.value
  have hd := PrimitiveWork.map_work_le (fun v => (⟨p.inputs (coords v), 7⟩ : PrimitiveWork.Result _))
    entries.value 7 (fun _ _ => le_rfl)
  have ht := CertificateWork.selectAnswer_work k data.value
  have hn : entries.value.length = S ^ schedule.length := evaluate_length L U S schedule
  have hlen : data.value.length = S ^ schedule.length := by simp [data, hn]
  rw [hn] at hd
  rw [hlen] at ht
  have hw := evaluate_work L U S hS schedule
  change entries.work + data.work + (CertificateWork.selectAnswer k data.value).work ≤ _
  change data.work ≤ _ at hd
  change entries.work ≤ _ at hw
  omega

/-- A failed central test requests the exact fallback. Its successful branch
performs the short dyadic anchor rounding and returns the result. -/
def anchorTest (L U : StoredSystem m) (S : ℕ) (schedule : List (Fin m)) (x : Fin m) :
    PrimitiveWork.Result (Option ℚ) :=
  let entries := evaluate L U S schedule
  let data := PrimitiveWork.map (fun v => ⟨coords v x, 3⟩) entries.value
  let test := CertificateWork.centralInterval data.value
  match test.value with
  | none => ⟨none, entries.work + data.work + test.work + 1⟩
  | some J =>
      let anchor := RoundingWork.roundUp J
      ⟨some anchor.value, entries.work + data.work + test.work + anchor.work + 1⟩

theorem anchorTest_value (D : System (Fin m) ℚ) (F : ℕ) (L U : StoredSystem m)
    (hL : L.system = mapWalls (roundDown F) D)
    (hU : U.system = mapWalls (PolylogEnclosure.roundUp F) D)
    (S : ℕ) (schedule : List (Fin m)) (x : Fin m) :
    (anchorTest L U S schedule x).value =
      (Certificates.centralInterval ((roundedEnclose D F S schedule).map (fun I => I x))).map
        Certificates.roundUp := by
  rw [← evaluate_value D F L U hL hU]
  simp only [anchorTest, PrimitiveWork.map_value, CertificateWork.centralInterval_value, List.map_map,
    Function.comp_def]
  split <;> simp_all

theorem anchorTest_work (D : System (Fin m) ℚ) (F s : ℕ) (L U : StoredSystem m)
    (hL : L.system = mapWalls (roundDown F) D)
    (hU : U.system = mapWalls (PolylogEnclosure.roundUp F) D)
    (schedule : List (Fin m)) (x : Fin m) (hw : ∀ v, D.lower v < D.upper v)
    (hlo : D.WeaklyFeasible D.lower) (hup : D.WeaklyFeasible D.upper)
    (h0 : 0 ≤ D.lower x) (h1 : D.upper x ≤ 1) :
    let S := 2 ^ s
    (anchorTest L U S schedule x).work ≤ listBound m S schedule.length +
      72 * (S ^ schedule.length + 1) ^ 2 + 6 * (F + schedule.length * s) + 20 := by
  let S := 2 ^ s
  let entries := evaluate L U S schedule
  let data := PrimitiveWork.map (fun v => (⟨coords v x, 3⟩ : PrimitiveWork.Result _)) entries.value
  have hd := PrimitiveWork.map_work_le (fun v => (⟨coords v x, 3⟩ : PrimitiveWork.Result _))
    entries.value 3 (fun _ _ => le_rfl)
  have ht := CertificateWork.centralInterval_work data.value
  have hn : entries.value.length = S ^ schedule.length := evaluate_length L U S schedule
  have hlen : data.value.length = S ^ schedule.length := by simp [data, hn]
  have hvalue : data.value = (roundedEnclose D F S schedule).map (fun I => I x) := by
    rw [← evaluate_value D F L U hL hU]
    simp [data, entries, Function.comp_def]
  rw [hn] at hd
  rw [hlen] at ht
  have he := evaluate_work L U S (by dsimp [S]; positivity) schedule
  change data.work ≤ _ at hd
  change entries.work ≤ _ at he
  change (anchorTest L U S schedule x).work ≤ _
  unfold anchorTest
  change (match (CertificateWork.centralInterval data.value).value with
    | none => ⟨none, entries.work + data.work + (CertificateWork.centralInterval data.value).work + 1⟩
    | some J => ⟨some (RoundingWork.roundUp J).value, entries.work + data.work +
        (CertificateWork.centralInterval data.value).work + (RoundingWork.roundUp J).work + 1⟩ :
      PrimitiveWork.Result (Option ℚ)).work ≤ _
  split
  · dsimp only [S] at hd he ht ⊢
    nlinarith
  · rename_i J hJ
    rw [CertificateWork.centralInterval_value, hvalue] at hJ
    have hi := roundedCentral_intervalInterior D F S schedule x hw hlo hup hJ
    have hg := Precision.centralInterval_onGrid (F + schedule.length * s) (hgrid := by
      intro I hI
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hI
      obtain ⟨digits, _, rfl⟩ := List.mem_map.mp hb
      exact roundedEntry_grid D F s schedule digits x) hJ
    have cost := RoundingWork.roundUp_work_grid J _ hg (h0.trans_lt hi.1) (hi.2.trans_le h1)
      (centralInterval_inside hJ).1
    dsimp only [S] at hd he ht ⊢
    nlinarith

open PolylogBits

/-- The runtime input for a threshold call contains one retained adjacency
table and the addresses of its walls and of the previously stored anchor. -/
def heapThreshold (H : Heap) (zero : ℕ → ℕ) (height D F s : ℕ)
    (lo hi : Vector ℕ m) (edges : SparseClosure.Table m)
    (schedule : List (Fin m)) (k : ℕ) (x : Fin m) (addr : ℕ) :
    PrimitiveWork.Result (Option Answer) :=
  let tables := PolylogPrefix.tables H zero height D F lo hi edges
  let threshold := PolylogPrefix.read H zero height addr D (F + schedule.length*s)
  let test := answerTest tables.value.1 tables.value.2 (2^s) schedule k
    (.threshold x threshold.value.2 threshold.value.1)
  ⟨test.value, tables.work + threshold.work + test.work + 3⟩

theorem heapThreshold_work (H : Heap) (zero : ℕ → ℕ) (height D F s : ℕ)
    (lo hi : Vector ℕ m) (edges : SparseClosure.Table m)
    (schedule : List (Fin m)) (k : ℕ) (x : Fin m) (addr : ℕ) :
    (heapThreshold H zero height D F s lo hi edges schedule k x addr).work ≤
      2*m*(PolylogPrefix.readBound height F + 2) + 8*m + 2 +
      PolylogPrefix.readBound height (F + schedule.length*s) +
      listBound m (2^s) schedule.length + 30*((2^s)^schedule.length+1) + 3 := by
  let t := PolylogPrefix.tables H zero height D F lo hi edges
  let b := PolylogPrefix.read H zero height addr D (F + schedule.length*s)
  have ht := PolylogPrefix.tables_work H zero height D F lo hi edges
  have hb := PolylogPrefix.read_work H zero height addr D (F + schedule.length*s)
  have ha := answerTest_work t.value.1 t.value.2 (2^s) (by positivity) schedule k
    (.threshold x b.value.2 b.value.1)
  change t.work + b.work + (answerTest t.value.1 t.value.2 _ schedule k (.threshold x b.value.2 b.value.1)).work + 3 ≤ _
  change t.work ≤ _ at ht
  change b.work ≤ _ at hb
  omega

/-- The complete counted threshold test agrees with using the exact anchor
in the rounded enclosure of the represented rational graph. -/
theorem heapThreshold_value {S : Store} {H : Heap} {height cap : ℕ}
    (v : H.Valid) (cache : Cached S H cap) (hd : height ≤ cap)
    (D F s : ℕ) (hD : D < 2^height)
    (lo hi : Vector ℕ m) (edges : SparseClosure.Table m) (schedule : List (Fin m))
    (k : ℕ) (x : Fin m) (addr : ℕ) (hF : F + schedule.length*s ≤ D)
    (a b : Fin m → S.Ref height) (cut : S.Ref height)
    (hl : ∀ i : Fin m, Represents S H lo[i] (a i)) (hu : ∀ i : Fin m, Represents S H hi[i] (b i))
    (hc : Represents S H addr cut) (hbound : ∀ i, value S height (a i) ≤ 2^D ∧ value S height (b i) ≤ 2^D)
    (hcut : value S height cut ≤ 2^D) :
    let sys := System.mk (fun i => PolylogPrefix.coordinate S D (a i))
      (fun i => PolylogPrefix.coordinate S D (b i)) (SparseClosure.lookup edges)
    let c := PolylogPrefix.coordinate S D cut
    (heapThreshold H (fun j => cache.lookup j false) height D F s lo hi edges schedule k x addr).value =
      Certificates.selectAnswer k ((roundedEnclose sys F (2^s) schedule).map (fun I => (I x, (c,c)))) := by
  have walls := PolylogPrefix.tables_value v cache hd D F (by omega) hD lo hi edges a b hl hu hbound
  have limits := PolylogPrefix.bounds_value v cache hd (⟨addr,hc⟩ : Cell S H cut) D
    (F + schedule.length*s) hF hD hcut
  dsimp only at limits
  simp only [heapThreshold, limits]
  exact thresholdTest_value _ _ _ _ _ walls.1 walls.2 schedule k x _

section Prepared

variable (H : Heap) (zero : ℕ → ℕ) (height D F s : ℕ)
  (lo hi : Vector ℕ m) (edges : SparseClosure.Table m) (schedule : List (Fin m))

def heapPair (k : ℕ) (x y : Fin m) : PrimitiveWork.Result (Option Answer) :=
  let tables := PolylogPrefix.tables H zero height D F lo hi edges
  let test := answerTest tables.value.1 tables.value.2 (2^s) schedule k (.pair x y)
  ⟨test.value, tables.work + test.work + 1⟩

def heapCentral (x : Fin m) : PrimitiveWork.Result (Option ℚ) :=
  let tables := PolylogPrefix.tables H zero height D F lo hi edges
  let test := anchorTest tables.value.1 tables.value.2 (2^s) schedule x
  ⟨test.value, tables.work + test.work + 1⟩

theorem heapPair_work (k : ℕ) (x y : Fin m) :
    (heapPair H zero height D F s lo hi edges schedule k x y).work ≤
      2*m*(PolylogPrefix.readBound height F + 2) + 8*m + 2 +
      listBound m (2^s) schedule.length + 30*((2^s)^schedule.length+1) + 1 := by
  let t := PolylogPrefix.tables H zero height D F lo hi edges
  have ht := PolylogPrefix.tables_work H zero height D F lo hi edges
  have ha := answerTest_work t.value.1 t.value.2 (2^s) (by positivity) schedule k (.pair x y)
  change t.work + (answerTest t.value.1 t.value.2 _ schedule k _).work + 1 ≤ _
  change t.work ≤ _ at ht
  omega

end Prepared

section Values

variable {S : Store} {H : Heap} {height cap : ℕ} (v : H.Valid) (cache : Cached S H cap)
  (hd : height ≤ cap) (D F s : ℕ) (hD : D < 2^height) (hF : F ≤ D)
  (lo hi : Vector ℕ m) (edges : SparseClosure.Table m) (schedule : List (Fin m))
  (a b : Fin m → S.Ref height)
  (hl : ∀ i : Fin m, Represents S H lo[i] (a i)) (hu : ∀ i : Fin m, Represents S H hi[i] (b i))
  (hbound : ∀ i, value S height (a i) ≤ 2^D ∧ value S height (b i) ≤ 2^D)

private abbrev system := System.mk (fun i => PolylogPrefix.coordinate S D (a i))
  (fun i => PolylogPrefix.coordinate S D (b i)) (SparseClosure.lookup edges)

include v hd hD hF hl hu hbound in
theorem heapPair_value (k : ℕ) (x y : Fin m) :
    (heapPair H (fun j => cache.lookup j false) height D F s lo hi edges schedule k x y).value =
      Certificates.selectAnswer k ((roundedEnclose (system D edges a b) F (2^s) schedule).map
        (fun I => (I x, I y))) := by
  have walls := PolylogPrefix.tables_value v cache hd D F hF hD lo hi edges a b hl hu hbound
  exact answerTest_value _ _ _ _ walls.1 walls.2 _ schedule k (.pair x y)

include v hd hD hF hl hu hbound in
theorem heapCentral_value (x : Fin m) :
    (heapCentral H (fun j => cache.lookup j false) height D F s lo hi edges schedule x).value =
      (Certificates.centralInterval ((roundedEnclose (system D edges a b) F (2^s) schedule).map
        (fun I => I x))).map Certificates.roundUp := by
  have walls := PolylogPrefix.tables_value v cache hd D F hF hD lo hi edges a b hl hu hbound
  exact anchorTest_value _ _ _ _ walls.1 walls.2 _ schedule x

include v hd hD hF hl hu hbound in
theorem heapCentral_work (x : Fin m)
    (hw : ∀ z, (system D edges a b).lower z < (system D edges a b).upper z)
    (hlo : (system D edges a b).WeaklyFeasible (system D edges a b).lower)
    (hup : (system D edges a b).WeaklyFeasible (system D edges a b).upper)
    (h0 : 0 ≤ (system D edges a b).lower x) (h1 : (system D edges a b).upper x ≤ 1) :
    (heapCentral H (fun j => cache.lookup j false) height D F s lo hi edges schedule x).work ≤
      2*m*(PolylogPrefix.readBound height F + 2) + 8*m + 2 +
      listBound m (2^s) schedule.length + 72*((2^s)^schedule.length+1)^2 +
        6*(F+schedule.length*s)+21 := by
  let t := PolylogPrefix.tables H (fun j => cache.lookup j false) height D F lo hi edges
  have walls := PolylogPrefix.tables_value v cache hd D F hF hD lo hi edges a b hl hu hbound
  have ht := PolylogPrefix.tables_work H (fun j => cache.lookup j false) height D F lo hi edges
  have ha := anchorTest_work (system D edges a b) F s t.value.1 t.value.2 walls.1 walls.2
    schedule x hw hlo hup h0 h1
  change t.work + (anchorTest t.value.1 t.value.2 (2^s) schedule x).work + 1 ≤ _
  change t.work ≤ _ at ht
  omega

end Values

end SortingAdversary.Continuous.PolylogOracleWork
