import SortingAdversary.Continuous.PolylogEnclosure
import SortingAdversary.Continuous.EnclosureWork

/-!
# Counted evaluation of the rounded local enclosure

The inputs are the two retained wall tables on the short grid. The same
explicit digit word drives both endpoint sweeps. Work below covers the finite
enumeration after the wall tables have been read; its parameters are the local
vertex count, alphabet, and schedule length.
-/

namespace SortingAdversary.Continuous.PolylogEnclosureWork

open SortingAdversary.Optimal EnclosureWork PolylogEnclosure

variable {m : ℕ}

def wordEntry (L U : StoredSystem m) (S : ℕ) (schedule : List (Fin m))
    (w : Word S schedule.length) : PrimitiveWork.Result (Vector ℚ m × Vector ℚ m) :=
  let steps := w.assign schedule
  let lo := EnclosureWork.fullSteps L S steps.value L.lower
  let hi := EnclosureWork.fullSteps U S steps.value U.upper
  ⟨(lo.value, hi.value), steps.work + lo.work + hi.work + 1⟩

def coords (p : Vector ℚ m × Vector ℚ m) (x : Fin m) : ℚ × ℚ := (p.1[x], p.2[x])

theorem wordEntry_value (D : FiniteAveraging.System (Fin m) ℚ) (F : ℕ) (L U : StoredSystem m)
    (hL : L.system = mapWalls (roundDown F) D) (hU : U.system = mapWalls (roundUp F) D)
    (S : ℕ) (schedule : List (Fin m)) (w : Word S schedule.length) :
    coords (wordEntry L U S schedule w).value = roundedEntry D F S schedule w.eval := by
  funext x
  have hl := congrFun (fullSteps_value L S (w.assign schedule).value L.lower) x
  have hu := congrFun (fullSteps_value U S (w.assign schedule).value U.upper) x
  change _ = FiniteAveraging.fullSteps L.system S _ L.system.lower x at hl
  change _ = FiniteAveraging.fullSteps U.system S _ U.system.upper x at hu
  rw [w.assign_value, hL] at hl
  rw [w.assign_value, hU] at hu
  apply Prod.ext
  · simpa only [coords, wordEntry, Word.assign_value, roundedEntry, FiniteAveraging.endpointEntry, values] using hl
  · simpa only [coords, wordEntry, Word.assign_value, roundedEntry, FiniteAveraging.endpointEntry, values] using hu

theorem wordEntry_work (L U : StoredSystem m) (S : ℕ) (schedule : List (Fin m))
    (w : Word S schedule.length) :
    (wordEntry L U S schedule w).work ≤ endpointBound m schedule.length := by
  have hl := fullSteps_work L S (w.assign schedule).value L.lower
  have hu := fullSteps_work U S (w.assign schedule).value U.upper
  rw [w.assign_length] at hl hu
  simp only [wordEntry, Word.assign_work, endpointBound]
  nlinarith

def evaluate (L U : StoredSystem m) (S : ℕ) (schedule : List (Fin m)) :
    PrimitiveWork.Result (List (Vector ℚ m × Vector ℚ m)) :=
  let digits := EnclosureWork.words S schedule.length
  let entries := PrimitiveWork.map (wordEntry L U S schedule) digits.value
  ⟨entries.value, digits.work + entries.work⟩

theorem evaluate_value (D : FiniteAveraging.System (Fin m) ℚ) (F : ℕ) (L U : StoredSystem m)
    (hL : L.system = mapWalls (roundDown F) D) (hU : U.system = mapWalls (roundUp F) D)
    (S : ℕ) (schedule : List (Fin m)) :
    (evaluate L U S schedule).value.map coords = roundedEnclose D F S schedule := by
  simp only [evaluate, PrimitiveWork.map_value, List.map_map, Function.comp_def,
    wordEntry_value D F L U hL hU, roundedEnclose]
  rw [← words_value S schedule.length, List.map_map]
  rfl

theorem evaluate_work (L U : StoredSystem m) (S : ℕ) (hS : 0 < S) (schedule : List (Fin m)) :
    (evaluate L U S schedule).work ≤ listBound m S schedule.length := by
  have hw := words_work S schedule.length hS
  have hm := PrimitiveWork.map_work_le (wordEntry L U S schedule)
    (EnclosureWork.words S schedule.length).value (endpointBound m schedule.length)
    (fun w _ => wordEntry_work L U S schedule w)
  rw [words_length] at hm
  simp only [evaluate, listBound]
  nlinarith

end SortingAdversary.Continuous.PolylogEnclosureWork
