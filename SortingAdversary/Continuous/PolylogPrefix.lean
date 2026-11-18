import SortingAdversary.Continuous.PolylogBits
import SortingAdversary.Continuous.PolylogEnclosureWork

/-!
# Reading a short outward-rounded rational from a shared bit block

The binary point is at position `D` (positions count from the right).
Read the integer bit and the first `F` fractional bits at their heap
addresses. On the boundary path, compare each excluded right sibling to its
cached all-zero address. This detects an exact grid point without traversing
the excluded suffix. No long numerator is materialized by the reader.
-/

namespace SortingAdversary.Continuous.PolylogPrefix

open PolylogBits PolylogEnclosure

/-- One descent from the root to the addressed bit. The counter measures
record probes and operations on indices; the integer precision of a height
or level width is bounded by the height of the bit tree. -/
def readBit (H : Heap) : (h index addr : ℕ) → Bool × ℕ
  | 0, _, addr => (decide (addr = 1), 1)
  | h+1, index, addr =>
    let width := 2^h
    let children := H.children addr
    let rest := if index < width then readBit H h index children.2
      else readBit H h (index-width) children.1
    (rest.1, rest.2 + h + 5)

theorem readBit_work (H : Heap) (h index addr : ℕ) :
    (readBit H h index addr).2 ≤ (h+1)*(h+5) := by
  induction h generalizing index addr with
  | zero => simp [readBit]
  | succ h ih =>
    simp only [readBit]
    split
    · nlinarith [ih index (H.children addr).2]
    · nlinarith [ih (index-2^h) (H.children addr).1]

theorem readBit_value {S : Store} {H : Heap} {h addr : ℕ} {a : S.Ref h}
    (rep : Represents S H addr a) (i : ℕ) (hi : i < 2^h) :
    (readBit H h i addr).1 = (value S h a).testBit i := by
  induction rep generalizing i with
  | leaf b =>
    have he : i = 0 := by simpa only [pow_zero, Nat.lt_one_iff] using hi
    subst i
    cases b <;> simp [readBit, value, S.read_leaf]
  | @node j addr l r a b fetch rl rr il ir =>
    have hval : value S (j+1) (S.join a b) =
        2^(2^j) * value S j a + value S j b := by
      rw [value_join, radix_eq, Nat.mul_comm]
    have hb : value S j b < 2^(2^j) := by simpa only [radix_eq] using value_lt S j b
    rw [hval, Nat.testBit_two_pow_mul_add _ hb]
    simp only [readBit, Heap.children, fetch, Option.getD_some]
    split
    · exact ir i (by assumption)
    · have hi' : i - 2^j < 2^j := by rw [pow_succ] at hi; omega
      exact il _ hi'

/-- The unscaled integer formed by the first `len` bits starting at `D`. -/
def readLeading (H : Heap) (h addr D : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | len+1 =>
    let before := readLeading H h addr D len
    let next := readBit H h (D-len) addr
    (2*before.1 + next.1.toNat, before.2 + next.2 + 4)

theorem readLeading_work (H : Heap) (h addr D len : ℕ) :
    (readLeading H h addr D len).2 ≤ 1 + len*((h+1)*(h+5)+4) := by
  induction len with
  | zero => simp [readLeading]
  | succ len ih =>
    have hw := readBit_work H h (D-len) addr
    change (readLeading H h addr D len).2 + (readBit H h (D-len) addr).2 + 4 ≤ _
    rw [Nat.succ_mul len]
    omega

theorem readLeading_value {S : Store} {H : Heap} {h addr : ℕ} {a : S.Ref h}
    (rep : Represents S H addr a) (D : ℕ) (hD : D < 2^h) (hunit : value S h a ≤ 2^D)
    (len : ℕ) (hlen : len ≤ D+1) :
    (readLeading H h addr D len).1 = value S h a / 2^(D+1-len) := by
  induction len with
  | zero =>
    simp only [readLeading, Nat.sub_zero]
    rw [Nat.div_eq_of_lt]
    have hpos : 0 < 2 ^ D := by positivity
    rw [pow_succ]
    omega
  | succ len ih =>
    have hsmall : len ≤ D := by omega
    have hidx : D-len < 2^h := by omega
    have he : D+1-len = (D-len)+1 := by omega
    have he' : D+1-(len+1) = D-len := by omega
    simp only [readLeading, ih (by omega), readBit_value rep _ hidx, Nat.toNat_testBit, he, he',
      pow_succ, ← Nat.div_div_eq_div_mul]
    omega

/-- All right siblings excluded by the cut must have the all-zero address.
A left sibling lies before the cut and is never inspected. -/
def tailClear (H : Heap) (zero : ℕ → ℕ) : (h index addr : ℕ) → Bool × ℕ
  | 0, _, _ => (true, 1)
  | h+1, index, addr =>
    let children := H.children addr
    if index < 2^h then
      let rest := tailClear H zero h index children.2
      (rest.1, rest.2 + h + 7)
    else
      let rest := tailClear H zero h (index - 2^h) children.1
      (rest.1 && decide (children.2 = zero h), rest.2 + h + 7)

theorem tailClear_work (H : Heap) (zero : ℕ → ℕ) (h i addr : ℕ) :
    (tailClear H zero h i addr).2 ≤ (h+1)*(h+7) := by
  induction h generalizing i addr with
  | zero => simp [tailClear]
  | succ h ih =>
    simp only [tailClear]
    split
    · nlinarith [ih i (H.children addr).2]
    · nlinarith [ih (i-2^h) (H.children addr).1]

private theorem join_eq_iff (S : Store) {h} {a b c d : S.Ref h} :
    S.join a b = S.join c d ↔ a = c ∧ b = d := by
  constructor
  · intro e
    simpa only [S.split_join, Prod.mk.injEq] using congrArg S.split e
  · rintro ⟨rfl, rfl⟩
    rfl

theorem tailClear_iff {S : Store} {H : Heap} {h cap addr : ℕ} {a : S.Ref h}
    (v : H.Valid) (cache : Cached S H cap) (hd : h ≤ cap) (rep : Represents S H addr a) (i : ℕ) :
    (tailClear H (fun j => cache.lookup j false) h i addr).1 = true ↔
      (truncate S (uniformSpec S) (atBit h i) a).1 = a := by
  induction rep generalizing i with
  | leaf b => simp [tailClear, atBit, truncate]
  | @node j addr l r a b fetch rl rr il ir =>
    have hj : j ≤ cap := by omega
    by_cases hi : i < 2^j
    · simp only [tailClear, atBit, hi, if_true, truncate, S.split_join, Heap.children, fetch,
        Option.getD_some, join_eq_iff, true_and, ir hj]
    · simp only [tailClear, atBit, hi, if_false, truncate, S.split_join, Heap.children, fetch,
        Option.getD_some, Bool.and_eq_true, decide_eq_true_eq, join_eq_iff, il hj]
      exact and_congr_right (fun _ => (rr.same_iff v (cache.spec hj false)).trans eq_comm)

/-- The exact represented number belongs only to the specification. -/
def coordinate (S : Store) {h : ℕ} (D : ℕ) (a : S.Ref h) : ℚ :=
  (value S h a : ℚ) / (2:ℚ)^D

/-- Read both short grid neighbors from an address. The arithmetic constructs
only short integers. The charge includes the descent work, constructing the
short power of two, and the short scalar arithmetic. -/
def read (H : Heap) (zero : ℕ → ℕ) (h addr D F : ℕ) : Optimal.PrimitiveWork.Result (ℚ × ℚ) :=
  let top := readLeading H h addr D (F+1)
  let exact := tailClear H zero h (D-F) addr
  let den := (2:ℚ)^F
  let next := if exact.1 then top.1 else top.1+1
  ⟨((top.1 : ℚ)/den, (next : ℚ)/den), top.2 + exact.2 + 2*F + 9⟩

def readBound (h F : ℕ) : ℕ :=
  1 + (F+1)*((h+1)*(h+5)+4) + (h+1)*(h+7) + 2*F + 9

theorem read_work (H : Heap) (zero : ℕ → ℕ) (h addr D F : ℕ) :
    (read H zero h addr D F).work ≤ readBound h F := by
  unfold read readBound
  dsimp only
  have step := readLeading_work H h addr D (F+1)
  have tail := tailClear_work H zero h (D-F) addr
  omega

theorem bounds_value {S : Store} {H : Heap} {h cap : ℕ} {a : S.Ref h} (v : H.Valid)
    (cache : Cached S H cap) (hd : h ≤ cap) (c : Cell S H a)
    (D F : ℕ) (hF : F ≤ D) (hD : D < 2^h) (hunit : value S h a ≤ 2^D) :
    (read H (fun j => cache.lookup j false) h c.addr D F).value = (roundDown F (coordinate S D a), roundUp F (coordinate S D a)) := by
  let P := 2^(D-F)
  let z := value S h a
  have hP : 0 < P := by dsimp [P]; positivity
  have hDpow : (2:ℚ)^D = 2^(D-F) * 2^F := by rw [← pow_add, Nat.sub_add_cancel hF]
  have hscale : coordinate S D a * 2^F = (z:ℚ) / (P:ℚ) := by
    simp only [coordinate, z, hDpow, P, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  have top := readLeading_value c.rep D hD hunit (F+1) (by omega)
  rw [show D+1-(F+1) = D-F by omega] at top
  have key := tailClear_iff v cache hd c.rep (D-F)
  have w : weight (atBit h (D-F)) = P := by rw [weight_eq, place_atBit _ _ (by omega)]
  have same : (tailClear H (fun j => cache.lookup j false) h (D-F) c.addr).1 = true ↔ z % P = 0 := by
    rw [key]
    constructor
    · intro hh
      have hv := congrArg (value S h) hh
      rw [value_truncate, w] at hv
      change z / P * P = z at hv
      exact Nat.mod_eq_zero_of_dvd ⟨z/P, by rw [Nat.mul_comm]; exact hv.symm⟩
    · intro hm
      apply value_injective
      rw [value_truncate, w]
      exact Nat.div_mul_cancel ((Nat.dvd_iff_mod_eq_zero).2 hm)
  have hfloor : ⌊(z:ℚ) / P⌋ = (z/P : ℕ) := by
    simpa only [Int.ofNat_ediv_ofNat] using Rat.floor_natCast_div_natCast z P
  have hceil : ⌈(z:ℚ) / P⌉ = ((if z%P = 0 then z/P else z/P+1 : ℕ) : ℤ) := by
    have hb := Int.floor_le ((z:ℚ) / P)
    have ha := Int.lt_floor_add_one ((z:ℚ) / P)
    rw [hfloor] at hb ha
    have hrat : ((z:ℚ) / P = (z/P : ℕ)) ↔ z%P=0 := by
      rw [div_eq_iff (by exact_mod_cast hP.ne')]
      constructor
      · intro hh
        have hn : z = z/P*P := by exact_mod_cast hh
        exact Nat.mod_eq_zero_of_dvd ⟨z/P, by rw [Nat.mul_comm]; exact hn⟩
      · intro hm
        exact_mod_cast (Nat.div_mul_cancel ((Nat.dvd_iff_mod_eq_zero).2 hm)).symm
    split
    · rename_i hm
      rw [hrat.mpr hm]
      simp
    · rename_i hn
      have hx := lt_of_le_of_ne hb (Ne.symm (fun eq => hn (hrat.mp eq)))
      apply Int.ceil_eq_iff.mpr
      push_cast at *
      constructor <;> linarith
  simp only [read, roundDown, roundUp, hscale, hfloor, hceil, top, ← same, z, P, Int.cast_natCast]

open Optimal EnclosureWork

/-- Read the wall pointers of the retained graph. The adjacency table is
shared by the two prepared systems. Each of the four resulting vectors has
one component per retained vertex. -/
def tables {m : ℕ} (H : Heap) (zero : ℕ → ℕ) (h D F : ℕ)
    (lo hi : Vector ℕ m) (edges : SparseClosure.Table m) :
    PrimitiveWork.Result (StoredSystem m × StoredSystem m) :=
  let low := PrimitiveWork.vector (fun i => read H zero h lo[i] D F)
  let high := PrimitiveWork.vector (fun i => read H zero h hi[i] D F)
  ⟨(⟨low.value.map Prod.fst, high.value.map Prod.fst, edges⟩,
    ⟨low.value.map Prod.snd, high.value.map Prod.snd, edges⟩), low.work + high.work + 8*m + 2⟩

theorem tables_work {m : ℕ} (H : Heap) (zero : ℕ → ℕ) (h D F : ℕ)
    (lo hi : Vector ℕ m) (edges : SparseClosure.Table m) :
    (tables H zero h D F lo hi edges).work ≤ 2*m*(readBound h F + 2) + 8*m + 2 := by
  have low := PrimitiveWork.vector_work_le (fun i : Fin m => read H zero h lo[i] D F)
    (readBound h F) (fun i => read_work H zero h lo[i] D F)
  have high := PrimitiveWork.vector_work_le (fun i : Fin m => read H zero h hi[i] D F)
    (readBound h F) (fun i => read_work H zero h hi[i] D F)
  simp only [tables]
  nlinarith

/-- The relations required by the counted sweep hold for the actual
prepared vectors obtained by reading the long dyadic heap addresses. -/
theorem tables_value {m : ℕ} {S : Store} {H : Heap} {h cap : ℕ}
    (v : H.Valid) (cache : Cached S H cap) (hd : h ≤ cap)
    (D F : ℕ) (hF : F ≤ D) (hD : D < 2^h)
    (lo hi : Vector ℕ m) (edges : SparseClosure.Table m)
    (a b : Fin m → S.Ref h)
    (hl : ∀ i : Fin m, Represents S H lo[i] (a i))
    (hu : ∀ i : Fin m, Represents S H hi[i] (b i))
    (hbound : ∀ i, value S h (a i) ≤ 2^D ∧ value S h (b i) ≤ 2^D) :
    let exact := FiniteAveraging.System.mk (fun i => coordinate S D (a i))
      (fun i => coordinate S D (b i)) (SparseClosure.lookup edges)
    let result := (tables H (fun j => cache.lookup j false) h D F lo hi edges).value
    result.1.system = mapWalls (roundDown F) exact ∧ result.2.system = mapWalls (roundUp F) exact := by
  have low (i : Fin m) := bounds_value v cache hd (⟨lo[i], hl i⟩ : Cell S H (a i))
    D F hF hD (hbound i).1
  have high (i : Fin m) := bounds_value v cache hd (⟨hi[i], hu i⟩ : Cell S H (b i))
    D F hF hD (hbound i).2
  simp only [Fin.getElem_fin] at low high
  simp only [tables, StoredSystem.system, mapWalls, PrimitiveWork.vector_value, Fin.getElem_fin,
    Vector.getElem_map, Vector.getElem_ofFn, low, high, and_self]

end SortingAdversary.Continuous.PolylogPrefix
