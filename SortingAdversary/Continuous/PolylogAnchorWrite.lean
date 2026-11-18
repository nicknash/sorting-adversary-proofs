import SortingAdversary.Continuous.PolylogEmbed
import SortingAdversary.Continuous.PolylogBlockAnchor
import SortingAdversary.Continuous.PolylogOracleWork
import SortingAdversary.Continuous.PolylogPrecision

/-!
# Writing an anchor selected by the rounded controller

The central test consumes only the short wall tables of the retained node.
Its success branch embeds a short grid numerator. Its failure branch reads
the two exact walls using the persistent-block width search. All prior heap
addresses remain valid in either result.
-/

namespace SortingAdversary.Continuous.PolylogAnchorWrite

open Controller FiniteAveraging OrderRegion EnclosureWork PolylogBits PolylogBlockAnchor
open PolylogOracle (grid cutoff)
open ArbitraryLabels (widthThreshold_pos pathHeight)
open Optimal

variable {n : ℕ}

private abbrev localWidth (k : ℕ) : ℚ := cutoff k / 2
private theorem width_pos (k : ℕ) : 0 < localWidth k := half_pos (widthThreshold_pos ..)

abbrev localSystem (M : Memory n) (k : ℕ) (hk : 0 < k) (x : Fin n) :=
  Neighborhood.system M.tree.system k (pathHeight k) hk (localWidth k) (width_pos k) {x}

abbrev localSize (M : Memory n) (k : ℕ) (hk : 0 < k) (x : Fin n) : ℕ :=
  (Neighborhood.labels M.tree.system k (pathHeight k) hk (localWidth k) (width_pos k) {x}).card

/-- The actual finite anchor test on the retained vertex tables. -/
def evaluate (M : Memory n) (k : ℕ) (hk : 0 < k) (x : Fin n)
    (lo hi : StoredSystem (localSize M k hk x)) : PrimitiveWork.Result (Option ℚ) :=
  PolylogOracleWork.anchorTest lo hi (EnclosureParameters.alphabet k (pathHeight k))
    (Neighborhood.schedule M.tree.system k (pathHeight k) hk (localWidth k) (width_pos k) {x})
    (Neighborhood.query M.tree.system k (pathHeight k) hk (localWidth k) (width_pos k) {x} x (by simp))

theorem evaluate_value (M : Memory n) (k : ℕ) (hk : 0 < k) (x : Fin n)
    (lo hi : StoredSystem (localSize M k hk x))
    (hlo : lo.system = PolylogEnclosure.mapWalls (PolylogEnclosure.roundDown (grid k)) (localSystem M k hk x))
    (hhi : hi.system = PolylogEnclosure.mapWalls (PolylogEnclosure.roundUp (grid k)) (localSystem M k hk x)) :
    (evaluate M k hk x lo hi).value = (PolylogOracle.centralTest M k x).map Certificates.roundUp := by
  rw [evaluate, PolylogOracleWork.anchorTest_value _ _ _ _ hlo hhi]
  simp only [PolylogOracle.centralTest, dif_pos hk]
  rfl

/-- The small scalar passed to the bit writer. -/
def numerator (q : ℚ) (e : ℕ) := ⌊q * (2 : ℚ) ^ e⌋₊

theorem numerator_correct {q : ℚ} {e : ℕ} (hq : OnDyadicGrid e q) (h0 : 0 ≤ q) :
    (numerator q e : ℚ) / (2 : ℚ)^e = q := by
  obtain ⟨z, hz⟩ := hq
  have hp : (0 : ℚ) < 2^e := by positivity
  have he : q * (2 : ℚ)^e = z := (eq_div_iff hp.ne').mp hz
  have hz0 : 0 ≤ z := by
    exact_mod_cast (show (0 : ℚ) ≤ z by rw [← he]; positivity)
  lift z to ℕ using hz0 with t
  unfold numerator
  rw [he]
  simpa only [Int.cast_natCast, Nat.floor_natCast] using hz.symm

theorem numerator_le {q : ℚ} {e : ℕ} (hq : OnDyadicGrid e q) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    numerator q e ≤ 2 ^ e := by
  have h := (numerator_correct hq h0).le.trans h1
  have hp : (0 : ℚ) < 2^e := by positivity
  exact_mod_cast (div_le_one hp).mp h

/-- Heap output of a refinement. The interpretation of the address is
recovered from the branch taken, independently of its internal reference type. -/
structure Written (H : Heap) where
  heap : Heap
  addr : ℕ
  valid : heap.Valid
  growth : heap.Extends H

variable {S : Store} {H : Heap} {cap h : ℕ}

def Written.ofWrite {a : S.Ref h} (w : Write S H a) : Written H :=
  ⟨w.heap, w.cell.addr, w.valid, w.growth⟩

def Written.Represents (out : Written H) (S : Store) (h D : ℕ) (q : ℚ) : Prop :=
  ∃ z : S.Ref h, PolylogBits.Represents S out.heap out.addr z ∧ coord S D z = q

/-- Failed selections and failed central tests use the same bit operation. -/
theorem write_prefix (M : Memory n) (x : Fin n) (D F : ℕ)
    (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap)
    {a b : S.Ref h} (left : Cell S H a) (right : Cell S H b)
    (hl : coord S D a = M.tree.system.lower x) (hr : coord S D b = M.tree.system.upper x)
    (hM : Geometric M) (hg : M.OnGrid F) (hD : D < 2^h) (hF : F+2 ≤ D) :
    (Written.ofWrite (fallbackAddr D F v cache hc left right)).Represents S h D (PolylogOracle.prefixAnchor M x) := by
  have hw := hM.widths x
  have bounds := hM.rationalBounds x
  have hu : M.tree.system.upper x - M.tree.system.lower x ≤ 1 := by linarith
  have hcap := Precision.interval_width_ge (hg.1.1 x) (hg.1.2 x) hw
  have hresult := fallbackAddr_represents D F v cache hc left right hD hF
    (by simpa only [hl,hr,PolylogAnchor.unit] using hcap) (by simpa only [hl,hr] using hu)
  obtain ⟨z,rep,eq⟩ := hresult
  refine ⟨z,rep,?_⟩
  rw [hl,hr] at eq
  exact eq.trans (PolylogAnchor.fallback_eq_reference hcap hw hu)

/-- A refinement actually requested by the two-label or threshold test
writes an address for the rational coordinate returned by that request. -/
theorem write_selection (M : Memory n) (k : ℕ) (q : Query n) (x : Fin n) (c : ℚ)
    (req : PolylogOracle.attempt M k q = .refine x c) (D F : ℕ) (v : H.Valid)
    (cache : Cached S H cap) (hc : h ≤ cap) {a b : S.Ref h}
    (left : Cell S H a) (right : Cell S H b) (hl : coord S D a = M.tree.system.lower x)
    (hr : coord S D b = M.tree.system.upper x) (hM : Geometric M) (hg : M.OnGrid F)
    (hD : D < 2^h) (hF : F+2 ≤ D) :
    (Written.ofWrite (fallbackAddr D F v cache hc left right)).Represents S h D c := by
  rw [(PolylogOracle.attempt_refine_output M k q x c req).2]
  exact write_prefix M x D F v cache hc left right hl hr hM hg hD hF

/-- Complete the short test in the heap: a certified central coordinate
is embedded by its short numerator; a failed test runs the prefix fallback. -/
def finish (D F e : ℕ) (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap)
    {a b : S.Ref h} (left : Cell S H a) (right : Cell S H b) : Option ℚ → Written H
  | none => Written.ofWrite (fallbackAddr D F v cache hc left right)
  | some q =>
    let w := PolylogEmbed.embedAddr D e (numerator q e) v cache hc
    ⟨w.heap,w.cell.addr,w.valid,w.growth⟩

def repairAddr (M : Memory n) (k : ℕ) (hk : 0 < k) (x : Fin n)
    (lo hi : StoredSystem (localSize M k hk x)) (D F e : ℕ) (v : H.Valid)
    (cache : Cached S H cap) (hc : h ≤ cap) {a b : S.Ref h}
    (left : Cell S H a) (right : Cell S H b) : Written H :=
  finish D F e v cache hc left right (evaluate M k hk x lo hi).value

/-- The heap write can consume any certified evaluator of the identical
central test, including implementations that read their wall rows by address. -/
theorem finish_represents (extra : CappedArithmetic.Expr) (M : Memory n)
    (hk : 64 ≤ PolylogSchedule.parameter extra n) (hM : Admissible (PolylogSchedule.parameter extra n) M)
    (x : Fin n) (test : Option ℚ)
    (htest : test = (PolylogOracle.centralTest M (PolylogSchedule.parameter extra n) x).map Certificates.roundUp)
    (D F : ℕ) (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap)
    {a b : S.Ref h} (left : Cell S H a) (right : Cell S H b)
    (hl : coord S D a = M.tree.system.lower x) (hr : coord S D b = M.tree.system.upper x)
    (hg : M.OnGrid F) (hD : D < 2^h) (hF : F+2 ≤ D) (he : Parameters.logCap n ≤ D) :
    let k := PolylogSchedule.parameter extra n
    (finish D F (Parameters.logCap n) v cache hc left right test).Represents S h D
      (PolylogOracle.anchor M k x) := by
  let k := PolylogSchedule.parameter extra n
  let e := Parameters.logCap n
  dsimp only
  rw [htest]
  change (finish D F e v cache hc left right ((PolylogOracle.centralTest M k x).map Certificates.roundUp)).Represents S h D (PolylogOracle.anchor M k x)
  cases ht : PolylogOracle.centralTest M k x with
  | none =>
    simpa only [PolylogOracle.anchor, ht, Option.map_none, finish] using
      write_prefix M x D F v cache hc left right hl hr hM.toGeometric hg hD hF
  | some J =>
    have hq := PolylogPrecision.scheduled_central extra hk M hM x J ht
    have hind := PolylogOracle.anchor_move_spec M k hk hM x
    have hb := hM.rationalBounds x
    have hv : PolylogOracle.anchor M k x = Certificates.roundUp J := by simp [PolylogOracle.anchor, ht]
    let q := Certificates.roundUp J
    have h0 : 0 ≤ q := hb.1.trans ((hind.2.1.trans_eq hv).le)
    have h1 : q ≤ 1 := (hv ▸ hind.2.2.1).le.trans hb.2
    have hin := PolylogEmbed.embedAddr_represents D e (numerator q e) v cache hc
      hD he (numerator_le hq h0 h1)
    obtain ⟨z, hrep, hval⟩ := hin
    rw [hv]
    exact ⟨z,hrep,hval.trans (numerator_correct hq h0)⟩

/-- End-to-end agreement for the heap address written by a path or degree
repair. The test is evaluated on the retained graph's short wall tables. -/
theorem repairAddr_represents (extra : CappedArithmetic.Expr) (M : Memory n)
    (hk : 64 ≤ PolylogSchedule.parameter extra n) (hM : Admissible (PolylogSchedule.parameter extra n) M)
    (x : Fin n) (lo hi : StoredSystem (localSize M (PolylogSchedule.parameter extra n) (by omega) x))
    (hlo : lo.system = PolylogEnclosure.mapWalls
      (PolylogEnclosure.roundDown (grid (PolylogSchedule.parameter extra n)))
      (localSystem M (PolylogSchedule.parameter extra n) (by omega) x))
    (hhi : hi.system = PolylogEnclosure.mapWalls
      (PolylogEnclosure.roundUp (grid (PolylogSchedule.parameter extra n)))
      (localSystem M (PolylogSchedule.parameter extra n) (by omega) x))
    (D F : ℕ) (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap)
    {a b : S.Ref h} (left : Cell S H a) (right : Cell S H b)
    (hl : coord S D a = M.tree.system.lower x) (hr : coord S D b = M.tree.system.upper x)
    (hg : M.OnGrid F) (hD : D < 2^h) (hF : F+2 ≤ D) (he : Parameters.logCap n ≤ D) :
    let k := PolylogSchedule.parameter extra n
    (repairAddr M k (by omega) x lo hi D F (Parameters.logCap n) v cache hc left right).Represents S h D
      (PolylogOracle.anchor M k x) :=
  finish_represents extra M hk hM x _ (evaluate_value M _ (by omega) x lo hi hlo hhi)
    D F v cache hc left right hl hr hg hD hF he

/-- The successive bit probes on the deterministic bisection branch. -/
def probes (test : ℕ → Bool) : (j lo hi : ℕ) → Fin j → ℕ
  | 0, _, _, i => i.elim0
  | j+1, lo, hi, i =>
    let mid := (lo + hi) / 2
    Fin.cases mid (if test mid then probes test j lo mid else probes test j (mid+1) hi) i

/-- Charges for the operations in the failed-test branch: each probe adds
one unit and compares; the final bit position is used for truncation and
the three-unit write. Costs count block primitives as in `PolylogBits`. -/
def fallbackWork (D F : ℕ) (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap)
    {a b : S.Ref h} (left : Cell S H a) (right : Cell S H b) : ℕ :=
  let pos := fun j => placeFor h D (min j F)
  let path := probes (fun j => fits v cache hc left right (pos j)) (Nat.log 2 F + 1) 0 F
  let last := placeFor h D ((widthSearchAddr D F v cache hc left right).1 + 2)
  let U := uniformSpec S
  (∑ i, ((addUnit S U (pos (path i)) a).work + (less S h b (addUnit S U (pos (path i)) a).result).2)) +
    (truncate S U last a).2 + (advance S U last (truncate S U last a).1 3).work

theorem fallbackWork_le (D F : ℕ) (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap)
    {a b : S.Ref h} (left : Cell S H a) (right : Cell S H b) :
    fallbackWork D F v cache hc left right ≤
      (Nat.log 2 F + 1) * (13*h+4) + (33*h+6) := by
  unfold fallbackWork
  apply fallback_block_work

/-- Compose the finite test's arithmetic work with the branch it actually
takes. Heap operations here charge block primitives; the dictionary
comparison bounds multiply those primitives by the balanced-map height. -/
def repairWork (test : PrimitiveWork.Result (Option ℚ)) (D F e : ℕ)
    (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap) {a b : S.Ref h}
    (left : Cell S H a) (right : Cell S H b) : ℕ :=
  test.work + 1 + match test.value with
    | none => fallbackWork D F v cache hc left right
    | some q => (PolylogEmbed.embedAddr D e (numerator q e) v cache hc).work

theorem repairWork_le (test : PrimitiveWork.Result (Option ℚ)) (D F e : ℕ)
    (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap) {a b : S.Ref h}
    (left : Cell S H a) (right : Cell S H b) :
    repairWork test D F e v cache hc left right ≤ test.work + 1 +
      max ((Nat.log 2 F + 1) * (13*h+4) + (33*h+6)) (1 + (e+1)*((h+1)^2+10*h+6)) := by
  unfold repairWork
  apply Nat.add_le_add_left
  cases ht : test.value with
  | none => exact (fallbackWork_le D F v cache hc left right).trans (le_max_left ..)
  | some q => exact (PolylogEmbed.embedAddr_work D e (numerator q e) v cache hc).trans (le_max_right ..)

/-- With the common workspace height, writing either kind of repair
anchor costs a cubic polynomial in the input logarithm beyond the test. -/
theorem repairWork_budget (test : PrimitiveWork.Result (Option ℚ)) (D F e : ℕ)
    (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap) {a b : S.Ref h}
    (left : Cell S H a) (right : Cell S H b) (hF : F ≤ D) (hD : D < 2 ^ h)
    (hheight : h ≤ 5 + (e + 1) * 3) :
    repairWork test D F e v cache hc left right ≤ test.work + 200 * (e + 2) ^ 3 := by
  have hf : Nat.log 2 F ≤ h := by
    by_cases hz : F = 0
    · simp [hz]
    · exact (Nat.log_lt_of_lt_pow hz (hF.trans_lt hD)).le
  apply (repairWork_le test D F e v cache hc left right).trans
  simp only [Nat.add_assoc]
  apply Nat.add_le_add_left
  rw [← Nat.add_max_add_left, max_le_iff]
  constructor
  · have hb := Nat.mul_le_mul (Nat.add_le_add_right (hf.trans hheight) 1)
      (Nat.add_le_add_right (Nat.mul_le_mul_left 13 hheight) 4)
    nlinarith [Nat.zero_le (e ^ 3), Nat.zero_le (e ^ 2)]
  · have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hheight 1) 2
    have hb := Nat.mul_le_mul_left (e + 1)
      (Nat.add_le_add_right (Nat.add_le_add hp (Nat.mul_le_mul_left 10 hheight)) 6)
    nlinarith [Nat.zero_le (e ^ 3), Nat.zero_le (e ^ 2)]

end SortingAdversary.Continuous.PolylogAnchorWrite
