import SortingAdversary.Continuous.PolylogSweepScan
import SortingAdversary.Continuous.PolylogOperands
import SortingAdversary.Continuous.PolylogTestWork

/-!
# Bit costs of all digit trajectories in a local enclosure

Each coordinate update performs two measured scans, computes the seven
rational operations of its affine digit, and writes the resulting vector.
The local proof uses only the range and dyadic precision of the input
tables. In particular it applies to both rounded ends of the trajectory.
-/

namespace SortingAdversary.Continuous.PolylogSweepProfile

open EnclosureWork OperandBounds PolylogTestWork Optimal
open Optimal.PrimitiveWork (Result)
variable {m : ℕ}

def update (T : StoredSystem m) (S : ℕ) (j : Fin S) (x : Fin m) (Y : Vector ℚ m) :
    Result (Vector ℚ m) :=
  let lo := scan true T x Y
  let hi := scan false T x Y
  let z := PolylogOperands.digitProfile S j Y[x] lo.value hi.value
  let out := PrimitiveWork.vector fun y => (⟨if y=x then z.result.value else Y[y],3⟩ : Result ℚ)
  ⟨out.value,lo.work+hi.work+z.bitWork+out.work+4⟩

theorem update_value (T : StoredSystem m) (S : ℕ) (j : Fin S) (x : Fin m) (Y : Vector ℚ m) :
    (update T S j x Y).value = (EnclosureWork.update T S j x Y).value := by
  simp only [update,EnclosureWork.update,scan_lower_value,scan_upper_value,PolylogOperands.digitProfile_value]

private theorem fin_cast_fit (s : ℕ) (j : Fin (2^s)) : Fits (s+1) (j.val:ℚ) := by
  constructor
  · simpa only [Rat.num_natCast, Int.natAbs_natCast, Nat.size_pow] using Nat.size_le_size j.isLt.le
  · simp

def updateBound (B : ℕ) := 4000000*(B+2)^4

private theorem update_work (T : StoredSystem m) (F s B : ℕ) (j : Fin (2^s)) (x : Fin m)
    (Y : Vector ℚ m) (hl : ∀ i, Short F (T.system.lower i))
    (hu : ∀ i, Short F (T.system.upper i)) (hy : ∀ i : Fin m, Short F (values Y i))
    (hf : F ≤ B) (hs : s ≤ B) (hm : m ≤ B) : (update T (2^s) j x Y).work ≤ updateBound B := by
  let b := B+2
  have yfit (i : Fin m) : Fits b Y[i] := (hy i).fits.mono (by dsimp [b]; omega)
  have lfit (i : Fin m) : Fits b T.lower[i] := (hl i).fits.mono (by dsimp [b]; omega)
  have ufit (i : Fin m) : Fits b T.upper[i] := (hu i).fits.mono (by dsimp [b]; omega)
  let l := scan true T x Y
  let u := scan false T x Y
  have ml : Fits b l.value := scan_fits true T x Y yfit (lfit x) (ufit x)
  have mu : Fits b u.value := scan_fits false T x Y yfit (lfit x) (ufit x)
  have base : Fits b ((2^s : ℕ):ℚ) := by
    rw [Nat.cast_pow,Nat.cast_ofNat]
    exact (fits_powTwo s).mono (by dsimp [b]; omega)
  have jj : Fits b (j.val:ℚ) := (fin_cast_fit s j).mono (by dsimp [b]; omega)
  have dig := digit_operands (2^s) b j Y[x] l.value u.value (by dsimp[b]; omega) (yfit x) ml mu base jj
  let z := PolylogOperands.digitProfile (2^s) j Y[x] l.value u.value
  have zw : z.bitWork ≤ 7*128*(8*b+4+1)^3 :=
    PolylogOperands.digitProfile_bits _ _ (by omega) _ _ _ _ dig
  have wl := scan_work true T x Y yfit (lfit x) (ufit x)
  have wu := scan_work false T x Y yfit (lfit x) (ufit x)
  let f (y : Fin m) : Result ℚ := ⟨if y=x then z.result.value else Y[y],3⟩
  have wo := PrimitiveWork.vector_work_le f 3 (fun _ => le_rfl)
  change l.work + u.work + z.bitWork + (PrimitiveWork.vector f).work+4 ≤ _
  change l.work ≤ _ at wl
  change u.work ≤ _ at wu
  have scanMax : (m+1)*(128*(b+1)^3+15) ≤ (B+1)*(128*(b+1)^3+15) := by gcongr
  apply le_trans (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (wl.trans scanMax) (wu.trans scanMax)) zw) wo) 4)
  dsimp [b,updateBound]
  nlinarith [Nat.zero_le (B^4),Nat.zero_le (B^3),Nat.zero_le (B^2)]

def fullSteps (T : StoredSystem m) (S : ℕ) : List (Fin m × Fin S) → Vector ℚ m → Result (Vector ℚ m)
  | [], Y => ⟨Y,1⟩
  | (x,j)::rest, Y =>
    let v := update T S j x Y
    let r := fullSteps T S rest v.value
    ⟨r.value,v.work+r.work+1⟩

theorem fullSteps_value (T : StoredSystem m) (S : ℕ) (ts : List (Fin m × Fin S)) (Y : Vector ℚ m) :
    (fullSteps T S ts Y).value = (EnclosureWork.fullSteps T S ts Y).value := by
  induction ts generalizing Y with
  | nil => rfl
  | cons a ts ih => cases a; simp only [fullSteps,EnclosureWork.fullSteps,update_value,ih]

private theorem short_mono {F G : ℕ} {q : ℚ} (h : Short F q) (le : F ≤ G) : Short G q :=
  ⟨Precision.grid_mono h.1 le,h.2⟩

theorem fullSteps_work (T : StoredSystem m) (F s B : ℕ) (ts : List (Fin m × Fin (2^s)))
    (Y : Vector ℚ m) (hl : ∀ i, Short F (T.system.lower i))
    (hu : ∀ i, Short F (T.system.upper i)) (hy : ∀ i, Short F (values Y i))
    (hm : m ≤ B) (prec : F+ts.length*s ≤ B) :
    (fullSteps T (2^s) ts Y).work ≤ ts.length*(updateBound B+1)+1 := by
  induction ts generalizing F Y with
  | nil => simp [fullSteps]
  | cons a ts ih =>
    obtain ⟨x,j⟩ := a
    simp only [List.length_cons,Nat.succ_mul] at prec ⊢
    let v := update T (2^s) j x Y
    have hu' := update_work T F s B j x Y hl hu hy (by omega) (by omega) hm
    have hy' (i : Fin m) : Short (F+s) (values v.value i) := by
      have h := steps_short T F s [(x,j)] Y hl hu hy i
      simpa only [List.length_cons,List.length_nil,zero_add,one_mul,EnclosureWork.fullSteps,
        v,update_value] using h
    have htail := ih (F+s) v.value (fun i => short_mono (hl i) (by omega))
      (fun i => short_mono (hu i) (by omega)) hy' (by omega)
    change v.work + (fullSteps T (2^s) ts v.value).work+1 ≤ _
    change v.work ≤ updateBound B at hu'
    omega

def entry (L U : StoredSystem m) (S : ℕ) (ts : List (Fin m)) (w : Word S ts.length) :
    Result (Vector ℚ m × Vector ℚ m) :=
  let st := w.assign ts
  let low := fullSteps L S st.value L.lower
  let high := fullSteps U S st.value U.upper
  ⟨(low.value,high.value),st.work+low.work+high.work+1⟩

def evaluate (L U : StoredSystem m) (S : ℕ) (ts : List (Fin m)) :
    Result (List (Vector ℚ m × Vector ℚ m)) :=
  let digitWords := EnclosureWork.words S ts.length
  let out := PrimitiveWork.map (entry L U S ts) digitWords.value
  ⟨out.value,digitWords.work+out.work⟩

theorem evaluate_value (L U : StoredSystem m) (S : ℕ) (ts : List (Fin m)) :
    (evaluate L U S ts).value = (PolylogEnclosureWork.evaluate L U S ts).value := by
  simp only [evaluate, PolylogEnclosureWork.evaluate, PrimitiveWork.map_value, entry,
    PolylogEnclosureWork.wordEntry, fullSteps_value]

theorem evaluate_work (L U : StoredSystem m) (F s B : ℕ) (ts : List (Fin m))
    (ll : ∀ i, Short F (L.system.lower i)) (lu : ∀ i, Short F (L.system.upper i))
    (ul : ∀ i, Short F (U.system.lower i)) (uu : ∀ i, Short F (U.system.upper i))
    (hm : m ≤ B) (hLen : ts.length ≤ B) (prec : F+ts.length*s ≤ B)
    (words : (2^s)^ts.length ≤ B) : (evaluate L U (2^s) ts).work ≤ 100000000*(B+2)^6 := by
  let E := 3*B+1+2*(B*(updateBound B+1)+1)+1
  have hw (w : Word (2^s) ts.length) : (entry L U (2^s) ts w).work ≤ E := by
    have a := fullSteps_work L F s B (w.assign ts).value L.lower ll lu ll hm (by rwa [Word.assign_length])
    have b := fullSteps_work U F s B (w.assign ts).value U.upper ul uu uu hm (by rwa [Word.assign_length])
    rw [Word.assign_length] at a b
    have h := Nat.mul_le_mul_right (updateBound B+1) hLen
    simp only [entry,Word.assign_work]
    dsimp only [E]; omega
  have mapWork := PrimitiveWork.map_work_le (entry L U (2^s) ts)
    (EnclosureWork.words (2^s) ts.length).value E (fun w _ => hw w)
  rw [EnclosureWork.words_length] at mapWork
  have wWork := EnclosureWork.words_work (2^s) ts.length (by positivity)
  have mapped := mapWork.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (E+2) words) 1)
  have enu := wWork.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 20 (Nat.add_le_add_right hLen 1)) words)
  apply (Nat.add_le_add enu mapped).trans
  dsimp [E,updateBound]
  ring_nf; omega

end SortingAdversary.Continuous.PolylogSweepProfile
