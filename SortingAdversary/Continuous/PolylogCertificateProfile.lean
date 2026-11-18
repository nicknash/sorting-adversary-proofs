import SortingAdversary.Continuous.PolylogOperands

/-!
# Profiled finite certificates

Rational comparisons, arithmetic and normalization use the exact schoolbook
profiles. Lists are counted using the computed comparisons; quantiles use
stable insertion sort. Short integer counters and list accesses cost one
word operation. The input length and the scalar widths are parameters.
-/

namespace SortingAdversary.Continuous.PolylogCertificateProfile

open Optimal Certificates OperandBounds
open Optimal.PrimitiveWork (Result)

def tariff (B : ℕ) := 128*(B+1)^3
def budget (B : ℕ) := tariff (200*(B+2))
def cap (B : ℕ) := 200*(B+1)^2*(budget B+1)

theorem cap_polynomial (B : ℕ) : cap B ≤ 2*10^12*(B+1)^5 := by
  unfold cap budget tariff
  calc
    _ ≤ 200*(B+1)^2*(128*(401*(B+1))^3+(B+1)^3) := by
      have hw : 200*(B+2)+1 ≤ 401*(B+1) := by omega
      have ho : 1 ≤ (B+1)^3 := Nat.pow_pos (Nat.zero_lt_succ _)
      gcongr
    _ = (200*(128*401^3+1))*(B+1)^5 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (by decide)

def leTest (a b : ℚ) : Result Bool :=
  let p := RationalBitWork.lessEqual a b
  ⟨p.result.value, p.bitWork⟩

def ltTest (a b : ℚ) : Result Bool :=
  let p := leTest b a
  ⟨!p.value, p.work+1⟩

@[simp] theorem leTest_value (a b : ℚ) : (leTest a b).value = decide (a ≤ b) := by
  simp [leTest]
@[simp] theorem ltTest_value (a b : ℚ) : (ltTest a b).value = decide (a < b) := by
  by_cases h : b ≤ a <;> simp [ltTest, h, lt_iff_not_ge]

theorem leTest_work {B : ℕ} {a b : ℚ} (ha : Fits B a) (hb : Fits B b) :
    (leTest a b).work ≤ tariff B := comparison_bit_charge ha hb
theorem ltTest_work {B : ℕ} {a b : ℚ} (ha : Fits B a) (hb : Fits B b) :
    (ltTest a b).work ≤ tariff B + 1 := Nat.add_le_add_right (leTest_work hb ha) 1

private theorem widen {B : ℕ} {x : ℚ} (h : Fits (B+1) x) : Fits (200*(B+2)) x :=
  h.mono (by omega)

/-- Strict comparisons are implemented by one integer cross-product comparator. -/
def left (I : ComparisonIntervals) := ltTest I.1.2 I.2.1
def right (I : ComparisonIntervals) := ltTest I.2.2 I.1.1

def finish (k l r size : ℕ) : Result (Option Answer) :=
  let p := divProfile l size
  let q := divProfile r size
  let hk := mulProfile 100 k
  let inv := divProfile 1 hk.result.value
  let half := divProfile 1 2
  let limit := subProfile half.result.value inv.result.value
  let order := leTest q.result.value p.result.value
  let mx := if order.value then p.result.value else q.result.value
  let test := ltTest mx limit.result.value
  ⟨if test.value then none else if order.value then some .less else some .greater,
    p.bitWork+q.bitWork+hk.bitWork+inv.bitWork+half.bitWork+limit.bitWork+order.work+test.work+8⟩

@[simp] theorem finish_value (k l r size : ℕ) :
    (finish k l r size).value =
      (if max ((l:ℚ)/size) ((r:ℚ)/size) < 1/2-1/(100*(k:ℚ)) then none
        else if (r:ℚ)/size ≤ (l:ℚ)/size then some .less else some .greater) := by
  simp only [finish, divProfile_value, mulProfile_value, subProfile_value, leTest_value,
    ltTest_value, decide_eq_true_eq]
  by_cases h : (r:ℚ)/size ≤ (l:ℚ)/size
  · simp [h]
  · simp [h, max_eq_right (le_of_not_ge h)]

abbrev PairFits (B : ℕ) (I : ComparisonIntervals) :=
  (Fits B I.1.1 ∧ Fits B I.1.2) ∧ Fits B I.2.1 ∧ Fits B I.2.2

private theorem finish_work (k l r size B : ℕ) (hk : k ≤ B) (hl : l ≤ B) (hr : r ≤ B) (hn : size ≤ B) :
    (finish k l r size).work ≤ 8*budget B+9 := by
  let W := 200*(B+2)
  have wk := fits_natCast k B hk
  have wl := fits_natCast l B hl
  have wr := fits_natCast r B hr
  have wn := fits_natCast size B hn
  have wc : Fits 101 (100:ℚ) := by simpa using fits_natCast 100 100 le_rfl
  have one := fits_one (B:=1) (by decide)
  have two : Fits 3 (2:ℚ) := by simpa using fits_natCast 2 2 le_rfl
  have hw : 1 ≤ W := by dsimp [W]; omega
  have wy : Fits W ((l:ℚ)/size) := (wl.div wn (by omega)).mono (by dsimp [W]; omega)
  have wz : Fits W ((r:ℚ)/size) := (wr.div wn (by omega)).mono (by dsimp [W]; omega)
  have fs := wc.mul wk
  have fi := one.div fs (by omega)
  have fh := one.div two (by omega)
  have ft : Fits W (1/2-1/(100*(k:ℚ))) := (fh.sub fi).mono (by dsimp [W]; omega)
  have hx : Fits W (if decide ((r:ℚ)/size ≤ (l:ℚ)/size) then (l:ℚ)/size else (r:ℚ)/size) := by
    split <;> assumption
  have c1 := divProfile_bits (widen wl) (widen wn) hw
  have c2 := divProfile_bits (widen wr) (widen wn) hw
  have c3 := mulProfile_bits (wc.mono (show 101 ≤ W by dsimp [W]; omega)) (widen wk)
  have c4 := divProfile_bits (one.mono hw) (fs.mono (show 101+(B+1) ≤ W by dsimp [W]; omega)) hw
  have c5 := divProfile_bits (one.mono hw) (two.mono (show 3 ≤ W by dsimp [W]; omega)) hw
  have c6 := subProfile_bits (fh.mono (show 1+3 ≤ W by dsimp [W]; omega))
    (fi.mono (show 1+(101+(B+1)) ≤ W by dsimp [W]; omega))
  have c7 := leTest_work wz wy
  have c8 := ltTest_work hx ft
  simp only [finish, divProfile_value, mulProfile_value, subProfile_value, leTest_value]
  change _ ≤ 8*(128*(W+1)^3)+9
  unfold tariff at c7 c8
  change _ ≤ 128*(W+1)^3 at c1 c2
  omega

def answer (k : ℕ) (L : List ComparisonIntervals) : Result (Option Answer) :=
  if L.isEmpty then ⟨none,1⟩ else
    let size := CertificateWork.length L
    let l := PrimitiveWork.count left L
    let r := PrimitiveWork.count right L
    let f := finish k l.value r.value size.value
    ⟨f.value,size.work+l.work+r.work+f.work+1⟩

@[simp] theorem answer_value (k : ℕ) (L : List ComparisonIntervals) :
    (answer k L).value = selectAnswer k L := by
  simp only [answer,selectAnswer]
  split
  · rfl
  · simp only [finish_value, PrimitiveWork.count_value, CertificateWork.length_value, left, right,
      ltTest_value, lowerFraction, upperFraction, List.countP_eq_length_filter]
    rfl

theorem answer_work (k : ℕ) (L : List ComparisonIntervals) (B : ℕ) (hk : k ≤ B) (hn : L.length ≤ B)
    (hf : ∀ I ∈ L, PairFits (B+1) I) : (answer k L).work ≤ cap B := by
  have lc := PrimitiveWork.count_work_le left L (budget B+1) (fun I h =>
    ltTest_work (widen (hf I h).1.2) (widen (hf I h).2.1))
  have rc := PrimitiveWork.count_work_le right L (budget B+1) (fun I h =>
    ltTest_work (widen (hf I h).2.2) (widen (hf I h).1.1))
  have lf : (PrimitiveWork.count left L).value ≤ B := by simp; exact (List.length_filter_le ..).trans hn
  have rf : (PrimitiveWork.count right L).value ≤ B := by simp; exact (List.length_filter_le ..).trans hn
  have hw := finish_work k _ _ L.length B hk lf rf hn
  have hm := Nat.mul_le_mul_right (budget B+1+3) hn
  simp only [answer]
  split
  · change 1 ≤ 200*(B+1)^2*(budget B+1)
    exact Nat.mul_pos (Nat.mul_pos (by decide) (pow_pos (Nat.zero_lt_succ B) _)) (Nat.zero_lt_succ _)
  · simp only [CertificateWork.length_value,CertificateWork.length_work]
    calc
      _ ≤ 2*B+1 + (B*(budget B+1+3)+1) + (B*(budget B+1+3)+1) + (8*budget B+9)+1 := by omega
      _ ≤ cap B := by unfold cap; nlinarith [Nat.zero_le (B^2*budget B)]

def insert (a : ℚ) : List ℚ → Result (List ℚ)
  | [] => ⟨[a],2⟩
  | b :: bs =>
    let c := leTest a b
    if c.value then ⟨a :: b :: bs, c.work+4⟩ else
      let r := insert a bs
      ⟨b::r.value,c.work+r.work+4⟩

@[simp] theorem insert_value (a : ℚ) (xs : List ℚ) :
    (insert a xs).value = List.orderedInsert (· ≤ ·) a xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [insert,leTest_value,decide_eq_true_eq,List.orderedInsert_cons]; split <;> simp_all

theorem insert_work {a : ℚ} {B : ℕ} (ha : Fits B a) (xs : List ℚ) (hf : ∀ x ∈ xs, Fits B x) :
    (insert a xs).work ≤ xs.length*(tariff B+4)+2 := by
  induction xs with
  | nil => simp [insert]
  | cons b bs ih =>
    have hb := leTest_work ha (hf b (by simp))
    have hs := ih (fun x hx => hf x (by simp [hx]))
    simp only [insert, List.length_cons]
    rw [Nat.succ_mul]
    split <;> dsimp only <;> omega

def sort : List ℚ → Result (List ℚ)
  | [] => ⟨[],1⟩
  | a::xs =>
    let t := sort xs
    let r := insert a t.value
    ⟨r.value, t.work+r.work+1⟩

@[simp] theorem sort_value (xs : List ℚ) : (sort xs).value = xs.mergeSort (· ≤ ·) := by
  rw [List.mergeSort_eq_insertionSort]
  induction xs <;> simp_all [sort,List.insertionSort_cons]

theorem sort_work (xs : List ℚ) (B : ℕ) (hf : ∀ x ∈ xs, Fits B x) :
    (sort xs).work ≤ (xs.length+1)^2*(tariff B+4) := by
  induction xs with
  | nil => simp [sort]
  | cons a xs ih =>
    have hb := ih (fun x hx => hf x (by simp [hx]))
    have hi := insert_work (hf a (by simp)) (sort xs).value (fun x hx =>
      hf x (by simpa using Or.inr (List.mem_mergeSort.mp ((sort_value xs) ▸ hx)) : x ∈ a::xs))
    have hlen : (sort xs).value.length = xs.length := by simp
    rw [hlen] at hi
    simp only [sort,List.length_cons]
    nlinarith [Nat.zero_le (xs.length*tariff B)]

def candidate (L : List Interval) : Result Interval :=
  let n := CertificateWork.length L
  let u := PrimitiveWork.map (fun I : Interval => ⟨I.2,1⟩) L
  let l := PrimitiveWork.map (fun I : Interval => ⟨I.1,1⟩) L
  let us := sort u.value
  let ls := sort l.value
  let a := CertificateWork.get? us.value (n.value/4-1)
  let b := CertificateWork.get? ls.value (3*n.value/4-1)
  ⟨(a.value.getD 0,b.value.getD 0),n.work+u.work+l.work+us.work+ls.work+a.work+b.work+10⟩

@[simp] theorem candidate_value (L : List Interval) : (candidate L).value = centralCandidate L := by
  simp [candidate,centralCandidate]

abbrev IntervalFits (B : ℕ) (I : Interval) := Fits B I.1 ∧ Fits B I.2

private theorem lookup_fits {B : ℕ} (hB : 1 ≤ B) (xs : List ℚ) (i : ℕ) (hf : ∀ x ∈ xs, Fits B x) :
    Fits B (xs[i]?.getD 0) := by
  cases he : xs[i]? with
  | none => simpa [Fits] using hB
  | some a => exact hf a (List.mem_of_getElem? he)

theorem candidate_fits (L : List Interval) {B : ℕ} (hB : 1 ≤ B) (hf : ∀ I ∈ L, IntervalFits B I) :
    IntervalFits B (candidate L).value := by
  rw [candidate_value]
  constructor <;> apply lookup_fits hB <;> intro q hq <;>
    obtain ⟨I, hI, rfl⟩ := List.mem_map.mp (List.mem_mergeSort.mp hq)
  · exact (hf I hI).2
  · exact (hf I hI).1

theorem candidate_work (L : List Interval) {B : ℕ} (hf : ∀ I ∈ L, IntervalFits B I) :
    (candidate L).work ≤ 20*(L.length+1)^2*(tariff B+4) := by
  have hsort (f : Interval → ℚ) (hh : ∀ I ∈ L, Fits B (f I)) :
      (sort (L.map f)).work ≤ (L.length+1)^2*(tariff B+4) := by
    simpa only [List.length_map] using sort_work (L.map f) B
      (fun x hx => by obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hx; exact hh I hI)
  have mu := PrimitiveWork.map_work_le (fun I : Interval => (⟨I.2,1⟩ : Result ℚ)) L 1 (fun _ _ => le_rfl)
  have ml := PrimitiveWork.map_work_le (fun I : Interval => (⟨I.1,1⟩ : Result ℚ)) L 1 (fun _ _ => le_rfl)
  have su := hsort Prod.snd (fun I h => (hf I h).2)
  have sl := hsort Prod.fst (fun I h => (hf I h).1)
  have gu := CertificateWork.get?_work ((L.map Prod.snd).mergeSort (· ≤ ·)) (L.length/4-1)
  have gl := CertificateWork.get?_work ((L.map Prod.fst).mergeSort (· ≤ ·)) (3*L.length/4-1)
  simp only [List.length_mergeSort,List.length_map] at gu gl
  simp only [candidate, CertificateWork.length_work, CertificateWork.length_value, PrimitiveWork.map_value, sort_value]
  nlinarith [Nat.zero_le (L.length^2*tariff B)]

def inside (J I : Interval) : Result Bool :=
  let l := leTest J.1 I.1
  let r := leTest I.2 J.2
  ⟨l.value && r.value,l.work+r.work+2⟩

@[simp] theorem inside_value (J I : Interval) :
    (inside J I).value = decide (J.1≤I.1 ∧ I.2≤J.2) := by simp [inside]

def central (L : List Interval) : Result (Option Interval) :=
  let n := CertificateWork.length L
  if n.value=0 ∨ ¬4 ∣ n.value then ⟨none,n.work+5⟩ else
    let c := candidate L
    let f := PrimitiveWork.count (inside c.value) L
    let valid := ltTest c.value.1 c.value.2
    ⟨if valid.value && decide (n.value ≤ 4*f.value) then some c.value else none,
      n.work+c.work+f.work+valid.work+10⟩

@[simp] theorem central_value (L : List Interval) : (central L).value = centralInterval L := by
  simp only [central, centralInterval, CertificateWork.length_value]
  split
  · rfl
  · simp [insideCount,List.countP_eq_length_filter]

theorem central_work (L : List Interval) {B : ℕ} (hB : 1 ≤ B) (hf : ∀ I ∈ L, IntervalFits B I) :
    (central L).work ≤ 40*(L.length+1)^2*(tariff B+4) := by
  have c := candidate_fits L hB hf
  have inside_cost (I : Interval) (hi : I ∈ L) : (inside (candidate L).value I).work ≤ 2*tariff B+2 :=
    by have l := leTest_work c.1 (hf I hi).1; have u := leTest_work (hf I hi).2 c.2
       dsimp only [inside]; omega
  have hh := PrimitiveWork.count_work_le _ L _ inside_cost
  have hc := candidate_work L hf
  have hv := ltTest_work c.1 c.2
  simp only [central,CertificateWork.length_work]
  split <;> dsimp only <;> nlinarith [Nat.zero_le (L.length^2*tariff B)]

/-- The exponent is small in *value* for any fraction with short
numerator and denominator, without requiring a lower bound on its sign. -/
private theorem exponent_bound {w : ℚ} {B : ℕ} (hw : Fits B w) (hB : 1 ≤ B) :
    (Int.log 2 w).natAbs ≤ B := by
  have lg (m : ℕ) (hm : m.size ≤ B) : Nat.clog 2 m ≤ B :=
    Nat.clog_le_of_le_pow (Nat.size_le.mp hm).le
  have f := (Nat.size_le_size (Nat.floor_le_ceil w)).trans (hw.natCeil hB)
  have c := (hw.inv hB).natCeil hB
  simp only [Int.log]
  split
  · exact (Nat.log_le_clog 2 _).trans (lg _ f)
  · simpa using lg _ c

/-- Explicit binary floor/ceiling logarithm. The positive and negative
branches profile the signed quotient used to extract their integer operand.
All halving iterations operate on integers at most the input plus one. -/
def integerLog (w : ℚ) : Result ℤ :=
  let test := leTest 1 w
  if test.value then
    let z := ceilProfile (-w)
    let m := (-z.result.value).toNat
    let t := StateWork.logTwo m
    ⟨(t.value : ℤ), test.work + z.bitWork + t.work*(m.size+2)^2 + 4⟩
  else
    let i := divProfile 1 w
    let z := ceilProfile i.result.value
    let m := z.result.value.toNat
    let t := RoundingWork.clogTwo m
    ⟨-(t.value : ℤ), test.work + i.bitWork + z.bitWork + t.work*(m.size+2)^2 + 5⟩

@[simp] theorem integerLog_value (w : ℚ) : (integerLog w).value = Int.log 2 w := by
  simp only [integerLog, Int.log, leTest_value, decide_eq_true_eq]
  split <;> simp [Int.ceil_neg,Int.floor_toNat,Int.ceil_toNat]

theorem integerLog_work {w : ℚ} {B : ℕ} (hw : Fits B w) (hB : 1 ≤ B) :
    (integerLog w).work ≤ 5*tariff B+5 := by
  have hc := leTest_work (fits_one hB) hw
  have hneg := ceilProfile_bits hw.neg
  have hinv := hw.inv hB
  have hdiv := divProfile_bits (fits_one hB) hw hB
  have hceil := ceilProfile_bits hinv
  have lg (m : ℕ) (hm : m.size ≤ B) : Nat.clog 2 m ≤ B :=
    Nat.clog_le_of_le_pow (Nat.size_le.mp hm).le
  have hf := (Nat.size_le_size (Nat.floor_le_ceil w)).trans (hw.natCeil hB)
  have hi := hinv.natCeil hB
  have wf := (Nat.log_le_clog 2 _).trans (lg _ hf)
  have wi := lg _ hi
  simp only [integerLog]
  split
  · simp only [ceilProfile_value,Int.ceil_neg,neg_neg,Int.floor_toNat,StateWork.logTwo_work]
    have bound : (3*Nat.log 2 ⌊w⌋₊+1)*(⌊w⌋₊.size+2)^2 ≤ (3*B+1)*(B+2)^2 := by gcongr
    unfold tariff at *
    nlinarith [Nat.zero_le (B^2),Nat.zero_le (B^3)]
  · simp only [divProfile_value,one_div,ceilProfile_value,Int.ceil_toNat,RoundingWork.clogTwo_work]
    have bound : (4*Nat.clog 2 ⌈w⁻¹⌉₊+1)*(⌈w⁻¹⌉₊.size+2)^2 ≤ (4*B+1)*(B+2)^2 := by gcongr
    unfold tariff at *
    nlinarith [Nat.zero_le (B^2),Nat.zero_le (B^3)]

/-- Computed signed power of two, with a normalized reciprocal on the
negative branch. The doubling loop visits powers of width ≤ |e|+1. -/
def powTwo (e : ℤ) : Result ℚ :=
  let t := StateWork.powTwo e.natAbs
  let pos := (t.value : ℚ)
  let w := t.work*(e.natAbs+2)^2
  if 0 ≤ e then ⟨pos,w+2⟩ else
    let i := divProfile 1 pos
    ⟨i.result.value,w+i.bitWork+3⟩

@[simp] theorem powTwo_value (e : ℤ) : (powTwo e).value = (2:ℚ)^e := by
  cases e with
  | ofNat m => simp [powTwo]
  | negSucc m => simp [powTwo,zpow_negSucc]

theorem powTwo_fits (e : ℤ) : Fits (e.natAbs+1) ((2:ℚ)^e) := by
  cases e with
  | ofNat m => simpa using fits_powTwo m
  | negSucc m => simpa [zpow_negSucc] using (fits_powTwo (m+1)).inv (by omega)

theorem powTwo_work (e : ℤ) : (powTwo e).work ≤ 2*tariff (e.natAbs+1)+3 := by
  have d := divProfile_bits (fits_one (B:=e.natAbs+1) (by omega)) (fits_powTwo e.natAbs) (by omega)
  have pw : (((StateWork.powTwo e.natAbs).value : ℕ) : ℚ) = (2:ℚ)^e.natAbs := by simp
  simp only [powTwo,pw,StateWork.powTwo_work]
  split <;> dsimp only <;> unfold tariff <;> nlinarith [Nat.zero_le (e.natAbs^2),Nat.zero_le (e.natAbs^3)]

def round (J : Interval) : Result ℚ :=
  let w := subProfile J.2 J.1
  let e := integerLog w.result.value
  let p := powTwo e.value
  let q := divProfile J.1 p.value
  let c := ceilProfile q.result.value
  let v := mulProfile p.value c.result.value
  ⟨v.result.value,w.bitWork+e.work+p.work+q.bitWork+c.bitWork+v.bitWork+4⟩

@[simp] theorem round_value (J : Interval) : (round J).value = Certificates.roundUp J := by
  simp only [round,subProfile_value,integerLog_value,powTwo_value,divProfile_value,ceilProfile_value,
    mulProfile_value,Certificates.roundUp,spacing]

private theorem tariff_mono {a b : ℕ} (h : a ≤ b) : tariff a ≤ tariff b := by unfold tariff; gcongr

theorem round_work (J : Interval) (B : ℕ) (hf : IntervalFits (B+1) J) :
    (round J).work ≤ 12*budget B+12 := by
  let W := 200*(B+2)
  let w := J.2-J.1
  let e := Int.log 2 w
  have ww : Fits ((B+1)+(B+1)+1) w := hf.2.sub hf.1
  have ep : e.natAbs ≤ (B+1)+(B+1)+1 := exponent_bound ww (by omega)
  have ps := powTwo_fits e
  have qr := hf.1.div ps (by omega)
  have ce := qr.ceil (by omega)
  have hW : 1 ≤ W := by dsimp [W]; omega
  have wh := ww.mono (show (B+1)+(B+1)+1 ≤ W by dsimp [W]; omega)
  have ph := ps.mono (show e.natAbs+1 ≤ W by dsimp [W]; omega)
  have qt := qr.mono (show (B+1)+(e.natAbs+1) ≤ W by dsimp [W]; omega)
  have ct := ce.mono (show (B+1)+(e.natAbs+1) ≤ W by dsimp [W]; omega)
  have s1 := subProfile_bits (widen hf.2) (widen hf.1)
  have s2 := integerLog_work wh hW
  have sp := tariff_mono (show e.natAbs+1 ≤ W by dsimp [W]; omega)
  have s3 := powTwo_work e
  have s4 := divProfile_bits (widen hf.1) ph hW
  have s5 := ceilProfile_bits qt
  have s6 := mulProfile_bits ph ct
  simp only [round,subProfile_value,integerLog_value,powTwo_value,divProfile_value,ceilProfile_value]
  change (subProfile J.2 J.1).bitWork + (integerLog w).work + (powTwo e).work +
    (divProfile J.1 ((2:ℚ)^e)).bitWork + (ceilProfile (J.1/(2:ℚ)^e)).bitWork +
    (mulProfile ((2:ℚ)^e) ⌈J.1/(2:ℚ)^e⌉).bitWork + 4 ≤ 12*(tariff W)+12
  change _ ≤ 128*(W+1)^3 at s1 s4
  unfold tariff at *
  omega

def anchor (L : List Interval) : Result (Option ℚ) :=
  let c := central L
  match c.value with
  | none => ⟨none,c.work+1⟩
  | some J => let r := round J; ⟨some r.value, c.work+r.work+1⟩

@[simp] theorem anchor_value (L : List Interval) :
    (anchor L).value = (centralInterval L).map Certificates.roundUp := by
  simp only [anchor,central_value]
  cases centralInterval L <;> simp

theorem anchor_work (L : List Interval) (B : ℕ) (hn : L.length ≤ B)
    (hf : ∀ I ∈ L, IntervalFits (B+1) I) : (anchor L).work ≤ cap B := by
  have cf := candidate_fits L (by omega : 1 ≤ B+1) hf
  have wide (I : Interval) (hi : I ∈ L) : IntervalFits (200*(B+2)) I :=
    ⟨widen (hf I hi).1,widen (hf I hi).2⟩
  have hc := central_work L (by omega : 1 ≤ 200*(B+2)) wide
  change _ ≤ 40*(L.length+1)^2*(budget B+4) at hc
  have hcap : 40*(L.length+1)^2*(budget B+4)+12*budget B+13 ≤ cap B := by
    unfold cap
    have hpos : 1 ≤ budget B := by unfold budget tariff; exact Nat.succ_le_of_lt (by positivity)
    calc
      _ ≤ 40*(B+1)^2*(budget B+4)+12*budget B+13 := by gcongr
      _ ≤ _ := by nlinarith [Nat.zero_le (B^2*budget B), Nat.mul_le_mul_left (B^2) hpos,
        Nat.mul_le_mul_left B hpos]
  cases hj : (central L).value with
  | none => simp only [anchor, hj]; omega
  | some J =>
    simp only [anchor, hj]
    have eq : centralCandidate L = J := by
      by_cases empty : L.length=0 ∨ ¬4 ∣ L.length
      · simp only [central_value, centralInterval, if_pos empty, reduceCtorEq] at hj
      · simp only [central_value, centralInterval, if_neg empty] at hj
        split at hj
        · exact Option.some.inj hj
        · cases hj
    have rr := round_work J B ((candidate_value L).trans eq ▸ cf)
    omega

end SortingAdversary.Continuous.PolylogCertificateProfile
