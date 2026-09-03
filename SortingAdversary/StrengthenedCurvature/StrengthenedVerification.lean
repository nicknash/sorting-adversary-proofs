import SortingAdversary.StrengthenedCurvature.StrengthenedCertificateData

/-!
# Replay and coverage of the strengthened certificate
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open RationalInterval

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def strengthenedRootD (i : Fin 22) : SRI :=
  ⟨scheduleDelta i.castSucc, scheduleDelta i.succ⟩

def strengthenedRootR : SRI := ⟨0, 1⟩

/-- The complete exact-rational replay. -/
theorem strengthened_certificate_check :
    ∀ i : Fin 22,
      checkStrengthenedTree 40 i (strengthenedTreeAt i)
        (strengthenedRootD i) strengthenedRootR = true := by
  native_decide

theorem strengthened_segment_certificate (i : Fin 22) {delta r : ℝ}
    (hdelta : InScheduleSegment i delta) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    StrengthenedCellConclusion i delta r := by
  apply checkStrengthenedTree_sound (strengthened_certificate_check i)
  · exact hdelta
  · simpa only [strengthenedRootR, Contains, Rat.cast_zero, Rat.cast_one] using
      (show 0 ≤ r ∧ r ≤ 1 from ⟨hr0, hr1⟩)

/-- The 22 rational schedule segments cover the certified offset range. -/
theorem strengthened_schedule_cover {delta : ℝ} (hd0 : 0 ≤ delta)
    (hd1 : delta ≤ (411 / 1000 : ℝ)) :
    ∃ i : Fin 22, InScheduleSegment i delta := by
  by_cases h1 : delta ≤ scheduleDelta (1 : Fin 23)
  · refine ⟨0, ?_⟩
    constructor
    · simpa [scheduleDelta, deltaNumerators] using hd0
    · simpa using h1
  by_cases h2 : delta ≤ scheduleDelta (2 : Fin 23)
  · refine ⟨1, ?_⟩
    constructor
    · simpa using (le_of_not_ge h1)
    · simpa using h2
  by_cases h3 : delta ≤ scheduleDelta (3 : Fin 23)
  · refine ⟨2, ?_⟩
    constructor
    · simpa using (le_of_not_ge h2)
    · simpa using h3
  by_cases h4 : delta ≤ scheduleDelta (4 : Fin 23)
  · refine ⟨3, ?_⟩
    constructor
    · simpa using (le_of_not_ge h3)
    · simpa using h4
  by_cases h5 : delta ≤ scheduleDelta (5 : Fin 23)
  · refine ⟨4, ?_⟩
    constructor
    · simpa using (le_of_not_ge h4)
    · simpa using h5
  by_cases h6 : delta ≤ scheduleDelta (6 : Fin 23)
  · refine ⟨5, ?_⟩
    constructor
    · simpa using (le_of_not_ge h5)
    · simpa using h6
  by_cases h7 : delta ≤ scheduleDelta (7 : Fin 23)
  · refine ⟨6, ?_⟩
    constructor
    · simpa using (le_of_not_ge h6)
    · simpa using h7
  by_cases h8 : delta ≤ scheduleDelta (8 : Fin 23)
  · refine ⟨7, ?_⟩
    constructor
    · simpa using (le_of_not_ge h7)
    · simpa using h8
  by_cases h9 : delta ≤ scheduleDelta (9 : Fin 23)
  · refine ⟨8, ?_⟩
    constructor
    · simpa using (le_of_not_ge h8)
    · simpa using h9
  by_cases h10 : delta ≤ scheduleDelta (10 : Fin 23)
  · refine ⟨9, ?_⟩
    constructor
    · simpa using (le_of_not_ge h9)
    · simpa using h10
  by_cases h11 : delta ≤ scheduleDelta (11 : Fin 23)
  · refine ⟨10, ?_⟩
    constructor
    · simpa using (le_of_not_ge h10)
    · simpa using h11
  by_cases h12 : delta ≤ scheduleDelta (12 : Fin 23)
  · refine ⟨11, ?_⟩
    constructor
    · simpa using (le_of_not_ge h11)
    · simpa using h12
  by_cases h13 : delta ≤ scheduleDelta (13 : Fin 23)
  · refine ⟨12, ?_⟩
    constructor
    · simpa using (le_of_not_ge h12)
    · simpa using h13
  by_cases h14 : delta ≤ scheduleDelta (14 : Fin 23)
  · refine ⟨13, ?_⟩
    constructor
    · simpa using (le_of_not_ge h13)
    · simpa using h14
  by_cases h15 : delta ≤ scheduleDelta (15 : Fin 23)
  · refine ⟨14, ?_⟩
    constructor
    · simpa using (le_of_not_ge h14)
    · simpa using h15
  by_cases h16 : delta ≤ scheduleDelta (16 : Fin 23)
  · refine ⟨15, ?_⟩
    constructor
    · simpa using (le_of_not_ge h15)
    · simpa using h16
  by_cases h17 : delta ≤ scheduleDelta (17 : Fin 23)
  · refine ⟨16, ?_⟩
    constructor
    · simpa using (le_of_not_ge h16)
    · simpa using h17
  by_cases h18 : delta ≤ scheduleDelta (18 : Fin 23)
  · refine ⟨17, ?_⟩
    constructor
    · simpa using (le_of_not_ge h17)
    · simpa using h18
  by_cases h19 : delta ≤ scheduleDelta (19 : Fin 23)
  · refine ⟨18, ?_⟩
    constructor
    · simpa using (le_of_not_ge h18)
    · simpa using h19
  by_cases h20 : delta ≤ scheduleDelta (20 : Fin 23)
  · refine ⟨19, ?_⟩
    constructor
    · simpa using (le_of_not_ge h19)
    · simpa using h20
  by_cases h21 : delta ≤ scheduleDelta (21 : Fin 23)
  · refine ⟨20, ?_⟩
    constructor
    · simpa using (le_of_not_ge h20)
    · simpa using h21
  · refine ⟨21, ?_⟩
    constructor
    · simpa using (le_of_not_ge h21)
    · simpa [scheduleDelta, deltaNumerators] using hd1

end StrengthenedCurvature
end SortingAdversary
