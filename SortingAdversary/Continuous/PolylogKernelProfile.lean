import SortingAdversary.Continuous.PolylogLocalProfile
import SortingAdversary.Continuous.PolylogSweepProfile
import SortingAdversary.Continuous.PolylogCertificateProfile

/-!
# Stored local queries with priced dictionary and scalar operations

The neighborhood still comes from the original incidence lists. Every wall
and threshold read includes the actual dictionary paths and rational
reductions. The finite sweep and the final certificate use the measured
scalar implementations. These bounds apply even to the temporary graphs
and wall addresses visited by the three selection trials.
-/

namespace SortingAdversary.Continuous.PolylogKernelProfile

open PolylogLocalProfile PolylogBits PolylogPrepared PolylogRows PolylogWallTables
open PolylogSchedule PolylogCompareWork Optimal

def kernels : Kernels := ⟨PolylogSweepProfile.evaluate,PolylogCertificateProfile.answer,
  PolylogCertificateProfile.anchor⟩

theorem correct : Correct kernels :=
  ⟨PolylogSweepProfile.evaluate_value,PolylogCertificateProfile.answer_value,
    PolylogCertificateProfile.anchor_value⟩

theorem priced : Priced kernels := by
  constructor
  · exact PolylogSweepProfile.evaluate_work
  · intro k L B hk hn hf
    exact PolylogCertificateProfile.answer_work k L B hk hn (fun I hI =>
      ⟨⟨(hf I hI).1,(hf I hI).2.1⟩,(hf I hI).2.2⟩)
  · exact PolylogCertificateProfile.anchor_work

variable {n h : ℕ}

abbrev pair (g : Graph n h) (w : Walls ℕ h) (H : Heap) (z : ℕ → ℕ) (level D : ℕ) (P : Params) :=
  PolylogLocalProfile.pair kernels g w H z level D P
abbrev threshold (g : Graph n h) (w : Walls ℕ h) (H : Heap) (z : ℕ → ℕ) (level D : ℕ) (P : Params) :=
  PolylogLocalProfile.threshold kernels g w H z level D P
abbrev central (g : Graph n h) (w : Walls ℕ h) (H : Heap) (z : ℕ → ℕ) (level D : ℕ) (P : Params) :=
  PolylogLocalProfile.central kernels g w H z level D P

section Values
variable (g : Graph n h) (w : Walls ℕ h) (H : Heap) (z : ℕ → ℕ) (level D : ℕ) (P : Params)

theorem pair_value (x y : Fin n) : (pair g w H z level D P x y).value =
    (PolylogPrepared.pairWith g w H z level D P x y).value :=
  PolylogLocalProfile.pair_value correct g w H z level D P x y

theorem threshold_value (x : Fin n) (addr : ℕ) : (threshold g w H z level D P x addr).value =
    (PolylogPrepared.thresholdWith g w H z level D P x addr).value :=
  PolylogLocalProfile.threshold_value correct g w H z level D P x addr

theorem central_value (x : Fin n) : (central g w H z level D P x).value =
    (PolylogPrepared.centralWith g w H z level D P x).value :=
  PolylogLocalProfile.central_value correct g w H z level D P x

end Values

section Budget
variable (extra : CappedArithmetic.Expr) (hk : 64 ≤ parameter extra n) {g : Graph n h}
  (sh : Shape g (parameter extra n)) (w : Walls ℕ h) (H : Heap) (z : ℕ → ℕ) (level D T : ℕ)
  (valid : H.Valid) (pos : 0<T) (fits : H.next < 2^T)

include hk sh valid pos fits

theorem pair_work (x y : Fin n) :
    (pair g w H z level D (Params.stage (parameter extra n)) x y).work ≤ total h level T (Parameters.logCap n) :=
  PolylogLocalProfile.pair_work correct priced extra hk sh w H z level D T valid pos fits x y

theorem threshold_work (x : Fin n) (addr : ℕ) :
    (threshold g w H z level D (Params.stage (parameter extra n)) x addr).work ≤ total h level T (Parameters.logCap n) :=
  PolylogLocalProfile.threshold_work correct priced extra hk sh w H z level D T valid pos fits x addr

theorem central_work (x : Fin n) :
    (central g w H z level D (Params.stage (parameter extra n)) x).work ≤ total h level T (Parameters.logCap n) :=
  PolylogLocalProfile.central_work correct priced extra hk sh w H z level D T valid pos fits x

end Budget

end SortingAdversary.Continuous.PolylogKernelProfile
