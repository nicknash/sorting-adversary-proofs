import SortingAdversary.Continuous.PolylogLocalBudget
import SortingAdversary.Continuous.PolylogOracleWork
import SortingAdversary.Continuous.PolylogOracle
import SortingAdversary.Continuous.StateOperandBounds

/-!
# Bit widths in the short rounded enclosure

The admitted stage bounds the precision and number of digit words by the
binary logarithmic cap. Monotonicity of each outward rounding operation
also preserves feasibility, including for the rounded walls used inside an
unfinished trajectory. The bounds therefore cover every coordinate, both
conditional scans, and the unreduced arithmetic of each digit.
-/

namespace SortingAdversary.Continuous.PolylogOperands

open Optimal FiniteAveraging EnclosureWork OperandBounds Precision PolylogEnclosure
open ArbitraryLabels (pathHeight widthThreshold_pos)
open EnclosureParameters (alphabet alphabetExponent)
open PolylogSchedule (parameter)
open PolylogOracle (grid cutoff)

variable {n m : ℕ}

/-- The wall rounding and starting endpoint used on each side of a digit word. -/
def wallRound (upper : Bool) (F : ℕ) : ℚ → ℚ :=
  if upper then PolylogEnclosure.roundUp F else roundDown F

def start (T : StoredSystem m) (upper : Bool) : Vector ℚ m := if upper then T.upper else T.lower

theorem wallRound_mono (upper : Bool) (F : ℕ) : Monotone (wallRound upper F) := by
  intro a b hab
  have hp : (0 : ℚ) < 2 ^ F := by positivity
  have hm := mul_le_mul_of_nonneg_right hab hp.le
  cases upper
  · exact (div_le_div_iff_of_pos_right hp).2 (Int.cast_le.mpr (Int.floor_mono hm))
  · exact (div_le_div_iff_of_pos_right hp).2 (Int.cast_le.mpr (Int.ceil_mono hm))

theorem wallRound_grid (upper : Bool) (F : ℕ) (q : ℚ) : OnDyadicGrid F (wallRound upper F q) := by
  cases upper <;> exact ⟨_, rfl⟩

theorem wallRound_exact {F : ℕ} {q : ℚ} (upper : Bool) (hq : OnDyadicGrid F q) :
    wallRound upper F q = q := by
  obtain ⟨z, rfl⟩ := hq
  cases upper <;> simp [wallRound, roundDown, PolylogEnclosure.roundUp]

theorem wallRound_unit (upper : Bool) (F : ℕ) (q : ℚ) (hl : 0 ≤ q) (hu : q ≤ 1) :
    0 ≤ wallRound upper F q ∧ wallRound upper F q ≤ 1 := by
  have hzero : OnDyadicGrid F 0 := ⟨0, by simp⟩
  have hone : OnDyadicGrid F 1 := ⟨(2 : ℤ)^F, by simp⟩
  exact ⟨(wallRound_exact upper hzero) ▸ wallRound_mono upper F hl,
    (wallRound_exact upper hone) ▸ wallRound_mono upper F hu⟩

private theorem map_feasible (D : System (Fin m) ℚ) (f : ℚ → ℚ) (hm : Monotone f)
    (v : Fin m → ℚ) (hv : D.WeaklyFeasible v) :
    (mapWalls f D).WeaklyFeasible (f ∘ v) :=
  ⟨fun x => ⟨hm (hv.1 x).1, hm (hv.1 x).2⟩, fun x y e => hm (hv.2 x y e)⟩

def prefixState (T : StoredSystem m) (side : Bool) (s : ℕ)
    (p : List (Fin m × Fin (2^s))) := (EnclosureWork.fullSteps T (2^s) p (start T side)).value

/-- A single statement covers the lower trajectory with both walls rounded down
and the upper trajectory with both walls rounded up. -/
theorem rounded_prefix (D : System (Fin m) ℚ) (T : StoredSystem m) (side : Bool) (F s G : ℕ)
    (hT : T.system = mapWalls (wallRound side F) D)
    (hl : D.WeaklyFeasible D.lower) (hu : D.WeaklyFeasible D.upper)
    (hunit : ∀ x, 0 ≤ D.lower x ∧ D.upper x ≤ 1)
    (p : List (Fin m × Fin (2^s))) (hlen : F + s * p.length ≤ G) (x : Fin m) :
    let Y := prefixState T side s p
    Fits (G+1) Y[x] ∧ Fits (G+1) (EnclosureWork.conditionalLower T x Y).value ∧
      Fits (G+1) (EnclosureWork.conditionalUpper T x Y).value := by
  have hg : BoundsOnGrid T.system F := by
    rw [hT]
    exact ⟨fun _ => wallRound_grid .., fun _ => wallRound_grid ..⟩
  have hstart : ∀ i : Fin m, OnDyadicGrid F (start T side)[i] := by
    cases side
    · exact hg.1
    · exact hg.2
  have hfeas : T.system.WeaklyFeasible (values (start T side)) := by
    cases side
    · change T.system.WeaklyFeasible T.system.lower
      rw [hT]
      exact map_feasible _ _ (wallRound_mono ..) _ hl
    · change T.system.WeaklyFeasible T.system.upper
      rw [hT]
      exact map_feasible _ _ (wallRound_mono ..) _ hu
  have hunit' : ∀ i, 0 ≤ T.system.lower i ∧ T.system.upper i ≤ 1 := by
    rw [hT]
    intro i
    have hw := (hl.1 i).2
    exact ⟨(wallRound_unit side F _ (hunit i).1 (hw.trans (hunit i).2)).1,
      (wallRound_unit side F _ ((hunit i).1.trans hw) (hunit i).2).2⟩
  have hcoord := prefix_coordinate_bits T F s p.length hg (start T side) hstart hfeas hunit' p le_rfl x
  refine ⟨hcoord.mono (Nat.add_le_add_right hlen 1), ?_⟩
  apply conditional_bits _ _ _ (bounds_mono hg (by omega)) _ _ hunit' x
  · intro i
    change OnDyadicGrid G (values (EnclosureWork.fullSteps T (2^s) p (start T side)).value i)
    rw [EnclosureWork.fullSteps_value]
    exact grid_mono (fullSteps_onGrid T.system F s p _ hg hstart i) hlen
  · change T.system.WeaklyFeasible (values (EnclosureWork.fullSteps T (2^s) p (start T side)).value)
    rw [EnclosureWork.fullSteps_value]
    exact fullSteps_feasible _ _ _ _ hfeas

variable (extra : CappedArithmetic.Expr) (D : System (Fin n) ℚ) (hk : 64 ≤ parameter extra n)
    (Q : Finset (Fin n))

local notation "k" => parameter extra n
local notation "H" => pathHeight k
local notation "s" => alphabetExponent k H
local notation "F" => grid k
local notation "cap" => Parameters.logCap n
local notation "N" => Neighborhood.system D k H (Nat.lt_of_lt_of_le (by decide : 0 < 64) hk) (cutoff k / 2)
  (half_pos (widthThreshold_pos ..)) Q
local notation "schedule" => Neighborhood.schedule D k H (Nat.lt_of_lt_of_le (by decide : 0 < 64) hk) (cutoff k / 2)
  (half_pos (widthThreshold_pos ..)) Q
local notation "verts" => Neighborhood.labels D k H (Nat.lt_of_lt_of_le (by decide : 0 < 64) hk) (cutoff k / 2)
  (half_pos (widthThreshold_pos ..)) Q

include hk in
private theorem stage_scalars : k ≤ cap ∧ 2^s ≤ cap := by
  have h := CappedStageScan.stage_need (PolylogSchedule.recipe extra) n (PolylogSchedule.active_stage hk)
  change max (max _ (UniformStages.Recipe.budget.need (PolylogSchedule.stage extra n))) _ ≤ _ at h
  have ha := UniformStages.admitted_scalar_bounds _ _ (max_le_iff.mp (max_le_iff.mp h).1).2
  exact ⟨ha.1,ha.2.2.2.2.1⟩

variable (hQ : Q.card ≤ 2) (hd : ∀ x, (GraphBalls.neighbors D.edge x).card ≤ parameter extra n)
    (hl : D.WeaklyFeasible D.lower) (hu : D.WeaklyFeasible D.upper)
    (hunit : ∀ x, 0 ≤ D.lower x ∧ D.upper x ≤ 1)

include hk hQ hd hl hu hunit in
theorem admitted_prefix (T : StoredSystem (verts).card) (side : Bool)
    (hT : T.system = mapWalls (wallRound side F) N)
    (p : List (Fin (verts).card × Fin (2^s))) (hp : p.length ≤ (schedule).length) (x : Fin (verts).card) :
    let Y := prefixState T side s p
    Fits (cap+1) Y[x] ∧ Fits (cap+1) (EnclosureWork.conditionalLower T x Y).value ∧
      Fits (cap+1) (EnclosureWork.conditionalUpper T x Y).value := by
  have hprec := PolylogLocalBudget.endpoint_precision extra D hk Q hQ hd
  change F + (schedule).length * s ≤ cap at hprec
  rw [Nat.mul_comm (schedule).length s] at hprec
  have plen : F + s * p.length ≤ cap :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hp) _).trans hprec
  let e := Neighborhood.embedding D k H (Nat.lt_of_lt_of_le (by decide : 0 < 64) hk) (cutoff k / 2) (half_pos (widthThreshold_pos ..)) Q
  exact rounded_prefix N T side F s cap hT ⟨fun i => hl.1 (e i), fun i j => hl.2 (e i) (e j)⟩
    ⟨fun i => hu.1 (e i), fun i j => hu.2 (e i) (e j)⟩ (fun i => hunit (e i)) p plen x

include hk hQ hd hl hu hunit in
/-- Every partial min/max fold in a conditional scan has the same short
width as a completed coordinate, for any traversal order of the neighbors. -/
theorem conditional_scan (T : StoredSystem (verts).card) (side : Bool)
    (hT : T.system = mapWalls (wallRound side F) N)
    (p : List (Fin (verts).card × Fin (2^s))) (hp : p.length ≤ (schedule).length)
    (A : Finset (Fin (verts).card)) (x : Fin (verts).card) :
    let Y := values (prefixState T side s p)
    Fits (cap+1) (A.fold max (T.system.lower x) Y) ∧
      Fits (cap+1) (A.fold min (T.system.upper x) Y) := by
  have he := PolylogLocalBudget.endpoint_precision extra D hk Q hQ hd
  have hf : F ≤ cap := (Nat.le_add_right F _).trans he
  let e := Neighborhood.embedding D k H (Nat.lt_of_lt_of_le (by decide : 0 < 64) hk)
    (cutoff k / 2) (half_pos (widthThreshold_pos ..)) Q
  have wall (a : ℚ) (ha : 0 ≤ a) (hb : a ≤ 1) : Fits (cap+1) (wallRound side F a) := by
    have h := wallRound_unit side F a ha hb
    exact (Fits.of_grid (wallRound_grid side F a) h.1 h.2).mono (Nat.add_le_add_right hf 1)
  have wy := (hl.1 (e x)).2
  have w := hunit (e x)
  have hy (i : Fin (verts).card) := (admitted_prefix extra D hk Q hQ hd hl hu hunit
    T side hT p hp i).1
  apply And.intro
  · apply StateOperandBounds.maxFold_fits _ _ _ _ (fun i _ => hy i)
    rw [hT]
    exact wall _ w.1 (wy.trans w.2)
  · apply StateOperandBounds.minFold_fits _ _ _ _ (fun i _ => hy i)
    rw [hT]
    exact wall _ (w.1.trans wy) w.2

include hk hQ hd hl hu hunit in
theorem admitted_digit (T : StoredSystem (verts).card) (side : Bool)
    (hT : T.system = mapWalls (wallRound side F) N)
    (p : List (Fin (verts).card × Fin (2^s))) (hp : p.length ≤ (schedule).length)
    (x : Fin (verts).card) (digit : Fin (2^s)) :
    let Y := prefixState T side s p
    ∀ q ∈ digitOperands (2^s) digit Y[x] (EnclosureWork.conditionalLower T x Y).value
      (EnclosureWork.conditionalUpper T x Y).value, Fits (8*(cap+1)+4) q := by
  have h := admitted_prefix extra D hk Q hQ hd hl hu hunit T side hT p hp x
  have hS := (stage_scalars extra hk).2
  exact digit_operands _ _ _ _ _ _ (by omega) h.1 h.2.1 h.2.2
    (fits_natCast _ cap hS) (fits_natCast _ cap (digit.isLt.le.trans hS))

open PolylogEnclosureWork (evaluate coords)
open Certificates

include hk hQ hd hl hu hunit in
theorem evaluated_endpoint (L U : StoredSystem (verts).card)
    (hL : L.system = mapWalls (roundDown F) N)
    (hU : U.system = mapWalls (PolylogEnclosure.roundUp F) N)
    {v} (hv : v ∈ (evaluate L U (2^s) schedule).value) (x : Fin (verts).card) :
    Fits (cap+1) (coords v x).1 ∧ Fits (cap+1) (coords v x).2 := by
  simp only [evaluate, PrimitiveWork.map_value, List.mem_map] at hv
  obtain ⟨word, _, rfl⟩ := hv
  let p := (word.assign schedule).value
  have hp : p.length ≤ (schedule).length := (word.assign_length schedule).le
  exact ⟨(admitted_prefix extra D hk Q hQ hd hl hu hunit L false hL p hp x).1,
    (admitted_prefix extra D hk Q hQ hd hl hu hunit U true hU p hp x).1⟩

include hk hQ hd in
theorem threshold_operands {c : ℚ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    let G := F + (schedule).length * s
    Fits (cap+1) (roundDown G c) ∧ Fits (cap+1) (PolylogEnclosure.roundUp G c) := by
  have hprec := PolylogLocalBudget.endpoint_precision extra D hk Q hQ hd
  have h (side : Bool) := wallRound_unit side (F + (schedule).length*s) c h0 h1
  exact ⟨(Fits.of_grid (wallRound_grid false _ c) (h false).1 (h false).2).mono
    (Nat.add_le_add_right hprec 1),
    (Fits.of_grid (wallRound_grid true _ c) (h true).1 (h true).2).mono
    (Nat.add_le_add_right hprec 1)⟩

include hk hQ hd in
theorem evaluated_length (L U : StoredSystem (verts).card) :
    (evaluate L U (2^s) schedule).value.length ≤ cap := by
  simp only [evaluate, PrimitiveWork.map_value, List.length_map, EnclosureWork.words_length]
  exact (PolylogLocalBudget.word_count extra D hk Q hQ hd).trans (PolylogSchedule.admitted_costs hk).1

include hk hQ hd in
/-- The two frequency counts, conditional maximum, and acceptance cutoff of
the computed answer test are all short, for both choices of queried intervals. -/
theorem answer_operands (L U : StoredSystem (verts).card) (probe : PolylogOracleWork.Probe (verts).card) :
    let entries := (evaluate L U (2^s) schedule).value.map (fun v => probe.inputs (coords v))
    ∀ q ∈ answerOperands k entries, Fits (200*(cap+1)) q := by
  apply OperandBounds.answer_operands _ _ _ (stage_scalars extra hk).1
  simpa only [List.length_map] using evaluated_length extra D hk Q hQ hd L U

include hk hQ hd in
theorem central_indices (L U : StoredSystem (verts).card) (x : Fin (verts).card) (J : Interval) :
    let entries := (evaluate L U (2^s) schedule).value.map (fun v => coords v x)
    (entries.length / 4 - 1).size ≤ 3*cap+1 ∧ (3*entries.length / 4 - 1).size ≤ 3*cap+1 ∧
    (insideCount entries J).size ≤ cap ∧ (4*insideCount entries J).size ≤ 4*cap := by
  apply certificate_indices
  simpa only [List.length_map] using evaluated_length extra D hk Q hQ hd L U

private theorem sorted_lookup {B : ℕ} (L : List ℚ) (i : ℕ)
    (h : ∀ q ∈ L, Fits (B+1) q) :
    Fits (B+1) ((L.mergeSort (· ≤ ·))[i]?.getD 0) := by
  cases he : (L.mergeSort (· ≤ ·))[i]? with
  | none => simpa only [he, Option.getD_none, Nat.cast_zero] using fits_natCast 0 B (Nat.zero_le _)
  | some q =>
    simpa only [he, Option.getD_some] using h q (List.mem_mergeSort.mp (List.mem_of_getElem? he))

include hk hQ hd hl hu hunit in
/-- Both order statistics and default zero are short even when the candidate
fails the central-interval test. All sort comparisons select input endpoints. -/
theorem central_candidate (L U : StoredSystem (verts).card)
    (hL : L.system = mapWalls (roundDown F) N)
    (hU : U.system = mapWalls (PolylogEnclosure.roundUp F) N) (x : Fin (verts).card) :
    let entries := (evaluate L U (2^s) schedule).value.map (fun v => coords v x)
    let J := (CertificateWork.centralCandidate entries).value
    Fits (cap+1) J.1 ∧ Fits (cap+1) J.2 := by
  dsimp only
  rw [CertificateWork.centralCandidate_value]
  constructor
  · apply sorted_lookup
    intro q hq
    obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hq
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hI
    exact (evaluated_endpoint extra D hk Q hQ hd hl hu hunit L U hL hU hv x).2
  · apply sorted_lookup
    intro q hq
    obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hq
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hI
    exact (evaluated_endpoint extra D hk Q hQ hd hl hu hunit L U hL hU hv x).1

include hk hQ hd hl hu hunit in
/-- The exponent loop, reciprocal ceiling, and each rational in central
dyadic rounding have logarithmic-width operands on an actual successful call. -/
theorem central_rounding (L U : StoredSystem (verts).card) (x : Fin (verts).card)
    (hL : L.system = mapWalls (roundDown F) N)
    (hU : U.system = mapWalls (PolylogEnclosure.roundUp F) N)
    (hw : ∀ v, D.lower v < D.upper v) {J : Interval}
    (hJ : centralInterval ((evaluate L U (2^s) schedule).value.map (fun v => coords v x)) = some J) :
    (Int.log 2 (J.2 - J.1)).natAbs.size ≤ cap ∧
    (Nat.ceil (J.2 - J.1)⁻¹).size ≤ 2*cap+3 ∧
    (∀ q ∈ roundingOperands J, Fits (4*cap+5) q) ∧
    (∀ a ≤ Nat.ceil (J.2 - J.1)⁻¹ + 1, a.size ≤ 2*cap+4) ∧
    ∀ e ≤ (Int.log 2 (J.2-J.1)).natAbs, (StateWork.powTwo e).value.size ≤ cap+1 := by
  have eqv := PolylogEnclosureWork.evaluate_value N F L U hL hU (2^s) schedule
  have hc : centralInterval ((roundedEnclose N F (2^s) schedule).map (fun I => I x)) = some J := by
    rw [← eqv, List.map_map]
    exact hJ
  let e := Neighborhood.embedding D k H (Nat.lt_of_lt_of_le (by decide : 0 < 64) hk) (cutoff k / 2) (half_pos (widthThreshold_pos ..)) Q
  have hi := roundedCentral_intervalInterior N F (2^s) schedule x (fun i => hw (e i))
    ⟨fun i => hl.1 (e i), fun i j => hl.2 (e i) (e j)⟩
    ⟨fun i => hu.1 (e i), fun i j => hu.2 (e i) (e j)⟩ hc
  have hprec := PolylogLocalBudget.endpoint_precision extra D hk Q hQ hd
  have hg := centralInterval_onGrid cap (hgrid := by
    intro I hI
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hI
    obtain ⟨digits, _, rfl⟩ := List.mem_map.mp hb
    have h := roundedEntry_grid N F s schedule digits x
    exact ⟨grid_mono h.1 hprec, grid_mono h.2 hprec⟩) hc
  have h0 : 0 < J.1 := (hunit (e x)).1.trans_lt hi.1
  have h1 : J.2 < 1 := hi.2.trans_le (hunit (e x)).2
  have hlt := (centralInterval_inside hc).1
  have h := rounding_operands J cap hg h0 h1 hlt
  refine ⟨h.1, h.2.1, h.2.2, ?_, ?_⟩
  · intro a ha
    have hs := (Nat.size_le_size ha).trans (RationalWork.size_add_le (Nat.ceil (J.2-J.1)⁻¹) 1)
    simp only [Nat.size_one] at hs
    omega
  · intro t ht
    rw [RoundingWork.log_natAbs_eq_roundingExponent (by linarith)] at ht
    rw [StateWork.powTwo_value, Nat.size_pow]
    have hb := roundingExponent_le hg h0 h1 hlt
    omega

/-- Each accumulator of the physical prefix reader contains at most the
number of bits already read, even for a malformed address. -/
theorem leading_width (heap : PolylogBits.Heap) (height addr D len : ℕ) :
    (PolylogPrefix.readLeading heap height addr D len).1.size ≤ len := by
  apply Nat.size_le.mpr
  induction len with
  | zero => simp [PolylogPrefix.readLeading]
  | succ j ih =>
    have hb : (PolylogPrefix.readBit heap height (D-j) addr).1.toNat ≤ 1 := by
      cases (PolylogPrefix.readBit heap height (D-j) addr).1 <;> decide
    simp only [PolylogPrefix.readLeading, pow_succ]
    omega

include hk hQ hd in
/-- The output pair of the threshold/prefix reader uses a short power of two
and a short successor even before reduction to canonical rationals. -/
theorem read_operands (heap : PolylogBits.Heap) (height addr D' : ℕ) :
    let G := F + (schedule).length * s
    let top := (PolylogPrefix.readLeading heap height addr D' (G+1)).1
    top.size ≤ cap+1 ∧ (top+1).size ≤ cap+2 ∧ Fits (cap+1) ((2 : ℚ)^G) := by
  let G := F + (schedule).length * s
  have he : G ≤ cap := PolylogLocalBudget.endpoint_precision extra D hk Q hQ hd
  have ht := leading_width heap height addr D' (G+1)
  have hs := RationalWork.size_add_le (PolylogPrefix.readLeading heap height addr D' (G+1)).1 1
  simp only [Nat.size_one] at hs
  exact ⟨ht.trans (Nat.add_le_add_right he 1), by
    change ((PolylogPrefix.readLeading heap height addr D' (G+1)).1+1).size ≤ cap+2
    omega,
    (fits_powTwo G).mono (Nat.add_le_add_right he 1)⟩

/-- A single short scalar word bound for coordinates, digits, counts and successful rounding. -/
def scalarBits (n : ℕ) := 200 * (Parameters.logCap n + 1)

/-- Bounds on the unreduced cross products, sum numerator, product numerator,
and common denominator before normalization. -/
theorem unreduced_operands {q r : ℚ} (hq : Fits (scalarBits n) q) (hr : Fits (scalarBits n) r) :
    (q.num * r.den).natAbs.size ≤ 2 * scalarBits n ∧
    (r.num * q.den).natAbs.size ≤ 2 * scalarBits n ∧
    (q.num * r.den + r.num * q.den).natAbs.size ≤ 2 * scalarBits n + 1 ∧
    (q.num * r.num).natAbs.size ≤ 2 * scalarBits n ∧
    (q.den * r.den).size ≤ 2 * scalarBits n := by
  have hc := comparison_operands hq hr
  have ha := RationalWork.size_int_add_le (q.num * r.den) (r.num * q.den)
  have hm := RationalWork.size_int_mul_le q.num r.num
  have hd' := RationalWork.size_mul_le q.den r.den
  obtain ⟨hq₁,hq₂⟩ := hq
  obtain ⟨hr₁,hr₂⟩ := hr
  exact ⟨hc.1, hc.2, by omega, by omega, by omega⟩

/-- Each rational primitive in the short computation admits the repository's
schoolbook bit simulation, including Euclid and exact quotient normalization. -/
theorem scalar_simulation {q r : ℚ} (hq : Fits (scalarBits n) q) (hr : Fits (scalarBits n) r) :
    let cost := 128 * (scalarBits n + 1)^3
    (addProfile q r).bitWork ≤ cost ∧ (subProfile q r).bitWork ≤ cost ∧
    (mulProfile q r).bitWork ≤ cost ∧ (divProfile q r).bitWork ≤ cost ∧
    (RationalBitWork.lessEqual q r).bitWork + 2 * RationalBitWork.Model.unit (binaryWidth q r) ≤ cost ∧
    (ceilProfile q).bitWork ≤ cost := by
  have hB : 1 ≤ scalarBits n := by unfold scalarBits; omega
  exact ⟨(addProfile_bits hq hr).trans (Nat.mul_le_mul_right _ (by decide)), subProfile_bits hq hr,
    (mulProfile_bits hq hr).trans (Nat.mul_le_mul_right _ (by decide)), divProfile_bits hq hr hB,
    minmax_bit_charge hq hr, ceilProfile_bits hq⟩

/-- Direct composition of the seven profiled operations in the affine digit.
Each intermediate feeds the next operation through its computed result. -/
def digitProfile (S : ℕ) (j : Fin S) (y l u : ℚ) : RationalBitWork.Profile ℚ :=
  let a := subProfile (S : ℚ) 1
  let b := subProfile a.result.value j.val
  let lo := mulProfile b.result.value l
  let hi := mulProfile j.val u
  let v := addProfile y lo.result.value
  let w := addProfile v.result.value hi.result.value
  let out := divProfile w.result.value S
  ⟨⟨out.result.value, a.result.work+b.result.work+lo.result.work+hi.result.work+
    v.result.work+w.result.work+out.result.work⟩,
    a.bitWork+b.bitWork+lo.bitWork+hi.bitWork+v.bitWork+w.bitWork+out.bitWork⟩

theorem digitProfile_value (S : ℕ) (j : Fin S) (y l u : ℚ) :
    (digitProfile S j y l u).result.value = FiniteAveraging.digit S j y l u := by
  simp only [digitProfile, subProfile_value, addProfile_value, mulProfile_value, divProfile_value,
    FiniteAveraging.digit]

private theorem digitProfile_bits (S B : ℕ) (hb : 1 ≤ B) (j : Fin S) (y l u : ℚ)
    (hf : ∀ q ∈ digitOperands S j y l u, Fits B q) :
    (digitProfile S j y l u).bitWork ≤ 7 * 128 * (B+1)^3 := by
  simp only [digitOperands, List.forall_mem_cons] at hf
  obtain ⟨hy, hl, hu, hS, hj, h1, ha, hb', hlo, hhi, hv, hw, _, _⟩ := hf
  have c1 := subProfile_bits hS h1
  have c2 := subProfile_bits ha hj
  have c3 := mulProfile_bits hb' hl
  have c4 := mulProfile_bits hj hu
  have c5 := addProfile_bits hy hlo
  have c6 := addProfile_bits hv hhi
  have c7 := divProfile_bits hw hS hb
  simp only [digitProfile, subProfile_value, mulProfile_value, addProfile_value]
  omega

include hk hQ hd hl hu hunit in
/-- At any position of either actual rounded sweep, an exact value-equivalent
bit simulation of the affine digit costs cubically many logarithmic bits. -/
theorem admitted_digit_simulation (T : StoredSystem (verts).card) (side : Bool)
    (hT : T.system = mapWalls (wallRound side F) N)
    (p : List (Fin (verts).card × Fin (2^s))) (hp : p.length ≤ (schedule).length)
    (x : Fin (verts).card) (j : Fin (2^s)) :
    let Y := prefixState T side s p
    let l := (EnclosureWork.conditionalLower T x Y).value
    let u := (EnclosureWork.conditionalUpper T x Y).value
    let run := digitProfile (2^s) j Y[x] l u
    run.result.value = FiniteAveraging.digit (2^s) j Y[x] l u ∧
    run.bitWork ≤ 7 * 128 * (8*(cap+1)+5)^3 :=
  ⟨digitProfile_value .., digitProfile_bits _ _ (by omega) _ _ _ _
    (admitted_digit extra D hk Q hQ hd hl hu hunit T side hT p hp x j)⟩

end SortingAdversary.Continuous.PolylogOperands
