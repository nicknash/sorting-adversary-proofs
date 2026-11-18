import SortingAdversary.Continuous.PolylogCompare

/-!
# Interpreting the actual selected and repair handles

Both old wall addresses are read from the sparse tables. Two spare fractional
bits let the runtime width search use its fixed capacity independently of the
current grid. A successful central test writes the short grid numerator.
-/

namespace SortingAdversary.Continuous.PolylogCompare

open PolylogBits PolylogAnchorWrite PolylogAddressOrder
open Optimal.CappedArithmetic (Expr)
variable {n t b D F : ℕ} {m : Memory n t b} {M : Controller.Memory n}
    {nodes : List (List ℕ)}

/-- Decoding the newly written address uses the new heap. -/
noncomputable abbrev WriteResult.coordinate (w : WriteResult m) (D : ℕ) : ℚ :=
  decode blockStore w.out.heap D b w.out.addr

theorem prefix_value (hm : m.Represents D nodes M) (geom : Controller.Geometric M)
    (hg : M.OnGrid F) (hF : F+2 ≤ D) (hD : D < 2^b) (x : Fin n) :
    (writePrefix D m x).coordinate D = PolylogOracle.prefixAnchor M x := by
  let l := (m.spatial.walls.lower.get x.val).value
  let r := (m.spatial.walls.upper.get x.val).value
  let L := M.tree.system.lower x
  let R := M.tree.system.upper x
  have el : m.decode D l = L := hm.spatial.walls.1 x
  have er : m.decode D r = R := hm.spatial.walls.2 x
  have lb : 0 ≤ L := (geom.rationalBounds x).1
  have ub : R ≤ 1 := (geom.rationalBounds x).2
  have strict : L < R := geom.widths x
  have grid := hg.mono (show F ≤ D-2 by omega)
  have width : PolylogAnchor.unit (D-2) ≤ R - L :=
    Precision.interval_width_ge (grid.1.1 x) (grid.1.2 x) strict
  have res := PolylogRawAnchor.readback D (D-2) m.valid m.typed m.cache (le_refl b) l r hD
    (by omega) (by change 0 ≤ m.decode D l; rwa [el])
    (by change 0 ≤ m.decode D r; rw [er]; exact lb.trans strict.le)
    (by change PolylogAnchor.unit (D-2) ≤ m.decode D r - m.decode D l; rwa [er, el])
    (by change m.decode D r - m.decode D l ≤ 1; rw [er,el]; linarith)
  change _ = PolylogAnchor.fallback (D-2) (m.decode D l) (m.decode D r) at res
  rw [el,er] at res
  exact res.trans (PolylogAnchor.fallback_eq_reference width strict (by linarith))

/-- The successful branch can be checked independently, given just the
short-grid and interval certificates for the returned rational. -/
theorem mint_some_value (m : Memory n t b) (x : Fin n) (q : ℚ)
    (hq : FiniteAveraging.OnDyadicGrid (Optimal.Parameters.logCap n) q) (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (hD : D < 2^b) (he : Optimal.Parameters.logCap n ≤ D) :
    (mint D m x (some q)).coordinate D = q := by
  let e := Optimal.Parameters.logCap n
  let w := PolylogEmbed.embedAddr D e (numerator q e) m.valid m.cache (le_refl b)
  obtain ⟨z,rz,hz⟩ := PolylogEmbed.embedAddr_represents D e (numerator q e)
    m.valid m.cache (le_refl b) hD he (numerator_le hq h0 h1)
  change decode blockStore w.heap D b w.cell.addr = q
  exact (decode_of_rep w.valid rz).trans (hz.trans (numerator_correct hq h0))

/-- The actual mint returns the controller's anchor on both central-test
branches, including when the short dyadic is exactly a grid point. -/
theorem mint_value (extra : Expr) (hm : m.Represents D nodes M)
    (hk : 64 ≤ PolylogSchedule.parameter extra n)
    (hM : Controller.Admissible (PolylogSchedule.parameter extra n) M)
    (hg : M.OnGrid F) (hF : F+2 ≤ D) (hD : D < 2^b) (he : Optimal.Parameters.logCap n ≤ D)
    (x : Fin n) (test : Option ℚ)
    (htest : test = (PolylogOracle.centralTest M (PolylogSchedule.parameter extra n) x).map Certificates.roundUp) :
    (mint D m x test).coordinate D = PolylogOracle.anchor M (PolylogSchedule.parameter extra n) x := by
  let k := PolylogSchedule.parameter extra n
  change test = (PolylogOracle.centralTest M k x).map Certificates.roundUp at htest
  rw [htest]
  change _ = PolylogOracle.anchor M k x
  cases ht : PolylogOracle.centralTest M k x with
  | none =>
    simpa only [PolylogOracle.anchor, ht, Option.map_none, mint] using
      prefix_value hm hM.toGeometric hg hF hD x
  | some J =>
    let q := Certificates.roundUp J
    have ha : PolylogOracle.anchor M k x = q := by simp [PolylogOracle.anchor, ht, q]
    have spec := PolylogOracle.anchor_move_spec M k hk hM x
    have hq := PolylogPrecision.scheduled_central extra hk M hM x J ht
    have bounds := hM.rationalBounds x
    have h0 : 0 ≤ q := bounds.1.trans (spec.2.1.trans_eq ha).le
    have h1 : q ≤ 1 := (ha ▸ spec.2.2.1).le.trans bounds.2
    rw [ha]
    exact mint_some_value m x q hq h0 h1 hD he

end SortingAdversary.Continuous.PolylogCompare
