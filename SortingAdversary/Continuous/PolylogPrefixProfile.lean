import SortingAdversary.Continuous.PolylogWordWork
import SortingAdversary.Continuous.PolylogOperands

/-! Dictionary paths and rational reductions for each short prefix of a long wall or threshold. -/

namespace SortingAdversary.Continuous.PolylogPrefixProfile

open PolylogBits PolylogWordWork Optimal
open EnclosureWork (StoredSystem)
open PrimitiveWork (Result)
variable {m : ℕ}

def read (H : Heap) (zero : ℕ → ℕ) (h addr D F : ℕ) : Result (ℚ × ℚ) :=
  let top := PolylogPrefix.readLeading H h addr D (F+1)
  let exact := PolylogPrefix.tailClear H zero h (D-F) addr
  let den := 2^F
  let lo := RationalBitWork.ratio top.1 den
  let hi := RationalBitWork.ratio (if exact.1 then top.1 else top.1+1) den
  let paths := prefixReadTrace H h addr D F
  ⟨(lo.result.value,hi.result.value), top.2 + exact.2 + 2*F+9 + (paths.run H).work + lo.bitWork+hi.bitWork⟩

@[simp] theorem read_value (H : Heap) (zero : ℕ → ℕ) (h addr D F : ℕ) :
    (read H zero h addr D F).value = (PolylogPrefix.read H zero h addr D F).value := by
  simp [read,PolylogPrefix.read]

def bound (T h G : ℕ) := (3*T+2)*PolylogPrefix.readBound h G + 2*((6*(G+2)+10)*(G+3)^2)

theorem read_work (H : Heap) (valid : H.Valid) (zero : ℕ → ℕ) (h addr D F T : ℕ)
    (pos : 0 < T) (fits : H.next < 2^T) : (read H zero h addr D F).work ≤ bound T h F := by
  let a := (PolylogPrefix.readLeading H h addr D (F+1)).1
  let b := if (PolylogPrefix.tailClear H zero h (D-F) addr).1 then a else a+1
  let c := (PolylogPrefix.read H zero h addr D F).work
  have af : a.size ≤ F+1 := PolylogOperands.leading_width ..
  have bf : b.size ≤ F+2 := by
    have hh := RationalWork.size_add_le a 1
    simp only [Nat.size_one] at hh
    dsimp only [b]; split <;> omega
  have den : (2^F).size ≤ F+2 := by rw [Nat.size_pow]; omega
  have lo := RationalBitWork.ratio_bitWork_polynomial a (2^F) (F+2) (by omega) den
  have hi := RationalBitWork.ratio_bitWork_polynomial b (2^F) (F+2) bf den
  have paths := prefixRead_dictionary H valid pos fits zero h addr D F
  have small := PolylogPrefix.read_work H zero h addr D F
  change c ≤ _ at small
  change _ ≤ (3*T+1)*c at paths
  change c + ((prefixReadTrace H h addr D F).run H).work + _ + _ ≤ _
  unfold bound
  nlinarith [Nat.mul_le_mul_left (3*T+1) small]

def tables (H : Heap) (zero : ℕ → ℕ) (h D F : ℕ)
    (lo hi : Vector ℕ m) (edges : SparseClosure.Table m) : Result (StoredSystem m × StoredSystem m) :=
  let l := PrimitiveWork.vector (fun i => read H zero h lo[i] D F)
  let u := PrimitiveWork.vector (fun i => read H zero h hi[i] D F)
  ⟨(⟨l.value.map Prod.fst,u.value.map Prod.fst,edges⟩,⟨l.value.map Prod.snd,u.value.map Prod.snd,edges⟩),
    l.work+u.work+8*m+2⟩

theorem tables_value (H : Heap) (zero : ℕ → ℕ) (h D F : ℕ) (lo hi : Vector ℕ m) (edges : SparseClosure.Table m) :
    (tables H zero h D F lo hi edges).value = (PolylogPrefix.tables H zero h D F lo hi edges).value := by
  simp [tables,PolylogPrefix.tables]

theorem tables_work (H : Heap) (valid : H.Valid) (zero : ℕ → ℕ) (h D F T : ℕ)
    (pos : 0<T) (fits : H.next<2^T) (lo hi : Vector ℕ m) (edges : SparseClosure.Table m) :
    (tables H zero h D F lo hi edges).work ≤ 2*m*(bound T h F+2)+8*m+2 := by
  have l := PrimitiveWork.vector_work_le (fun i : Fin m => read H zero h lo[i] D F) (bound T h F)
    (fun _ => read_work H valid zero h _ D F T pos fits)
  have u := PrimitiveWork.vector_work_le (fun i : Fin m => read H zero h hi[i] D F) (bound T h F)
    (fun _ => read_work H valid zero h _ D F T pos fits)
  dsimp only [tables]
  nlinarith

end SortingAdversary.Continuous.PolylogPrefixProfile
