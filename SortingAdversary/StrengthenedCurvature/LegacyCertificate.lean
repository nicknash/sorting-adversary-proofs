import SortingAdversary.StrengthenedCurvature.LegacyEnvelope
import SortingAdversary.StrengthenedCurvature.DirectedInterval
import Lean.Elab.Tactic.Decide

/-!
# Kernel-checked directed-interval certificate for `K = 7.361`

The checker recursively bisects the exact rational interval
`[0,397/1000]`.  A leaf is accepted only when exact rational interval
arithmetic, together with proved Taylor bounds for every logarithm and a
squared-endpoint certificate for `√(1/3)`, places the complete scalar envelope
strictly below `log (7361/1000)`.  `native_decide` accelerates only rational
normalization; all soundness facts are ordinary Lean theorems.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open RationalInterval

abbrev RI := RationalInterval

private abbrev qI (q : ℚ) : RI := point q
private abbrev oneI : RI := qI 1
private abbrev twoI : RI := qI 2
private abbrev threeI : RI := qI 3

/-- Exact rational enclosure of `√(1/3)`. -/
def legacyRadiusI : RI :=
  ⟨5773502691896257 / 10000000000000000,
    2886751345948129 / 5000000000000000⟩

theorem legacyRadiusI_contains : legacyRadiusI.Contains legacyRadius := by
  rw [legacyRadius]
  have h := Contains.sqrt (I := point (1 / 3)) (J := legacyRadiusI)
    (contains_point (1 / 3)) (by
      norm_num [SqrtCertificate, legacyRadiusI, point])
  norm_num at h ⊢
  exact h

private abbrev iTPlus (D : RI) : RI :=
  legacyRadiusI.add ((qI (4 / 5)).mul D)

private abbrev iTMinus (D : RI) : RI :=
  legacyRadiusI.sub ((qI (4 / 5)).mul D)

private abbrev iA (D : RI) : RI :=
  legacyRadiusI.sub ((qI (1 / 5)).mul D)

private abbrev iB (D : RI) : RI :=
  legacyRadiusI.add ((qI (1 / 5)).mul D)

private abbrev iDenPlus (D : RI) : RI := oneI.add (iTPlus D).square
private abbrev iDenMinus (D : RI) : RI := oneI.add (iTMinus D).square
private abbrev iA0 (D : RI) : RI := (iA D).div (iDenPlus D)
private abbrev iB0 (D : RI) : RI := (iB D).div (iDenMinus D)
private abbrev iLambdaDen (D : RI) : RI := (iA0 D).add (iB0 D)
private abbrev iLambda (D : RI) : RI := (iB0 D).div (iLambdaDen D)

private abbrev iQueryArgPlus (D : RI) : RI :=
  oneI.add (oneI.div (iTPlus D).square)

private abbrev iQueryArgMinus (D : RI) : RI :=
  oneI.add (oneI.div (iTMinus D).square)

private abbrev iPlusLogArg (D Z : RI) : RI := oneI.add ((iA D).mul Z)
private abbrev iMinusLogArg (D Z : RI) : RI := oneI.sub ((iB D).mul Z)

private abbrev iPhiPlus (terms : ℕ) (D Z : RI) : RI :=
  let cubic := ((twoI.mul (iA D)).div (iDenPlus D)).mul (Z.square.mul Z)
  let logarithmic := threeI.mul
    (((iA D).mul Z).sub ((iPlusLogArg D Z).logarithm terms))
  cubic.add logarithmic

private abbrev iPhiMinus (terms : ℕ) (D Z : RI) : RI :=
  let cubic := (((qI (-2)).mul (iB D)).div (iDenMinus D)).mul
    (Z.square.mul Z)
  let logarithmic := threeI.mul
    ((((iB D).mul Z).neg).sub ((iMinusLogArg D Z).logarithm terms))
  cubic.add logarithmic

private abbrev iPhiAverage (terms : ℕ) (D Z : RI) : RI :=
  ((iLambda D).mul (iPhiPlus terms D Z)).add
    ((oneI.sub (iLambda D)).mul (iPhiMinus terms D Z))

/-- Directed interval evaluation of the complete one-dimensional envelope. -/
def legacyEnvelopeI (terms : ℕ) (D : RI) : RI :=
  let basePlus := (iLambda D).mul ((iQueryArgPlus D).logarithm terms)
  let baseMinus := (oneI.sub (iLambda D)).mul
    ((iQueryArgMinus D).logarithm terms)
  (basePlus.add baseMinus).add
    ((iPhiAverage terms D (qI (-1))).maximum
      (iPhiAverage terms D (qI 1)))

/-- Every strict-positivity side condition used by the interval evaluator. -/
structure LegacyCellWellFormed (D : RI) : Prop where
  tPlusSq : 0 < (iTPlus D).square.lower
  tMinusSq : 0 < (iTMinus D).square.lower
  denPlus : 0 < (iDenPlus D).lower
  denMinus : 0 < (iDenMinus D).lower
  lambdaDen : 0 < (iLambdaDen D).lower
  queryPlus : 0 < (iQueryArgPlus D).lower
  queryMinus : 0 < (iQueryArgMinus D).lower
  plusNeg : 0 < (iPlusLogArg D (qI (-1))).lower
  plusPos : 0 < (iPlusLogArg D (qI 1)).lower
  minusNeg : 0 < (iMinusLogArg D (qI (-1))).lower
  minusPos : 0 < (iMinusLogArg D (qI 1)).lower

private def legacyCellWellFormedB (D : RI) : Bool :=
  decide (0 < (iTPlus D).square.lower) &&
  (decide (0 < (iTMinus D).square.lower) &&
  (decide (0 < (iDenPlus D).lower) &&
  (decide (0 < (iDenMinus D).lower) &&
  (decide (0 < (iLambdaDen D).lower) &&
  (decide (0 < (iQueryArgPlus D).lower) &&
  (decide (0 < (iQueryArgMinus D).lower) &&
  (decide (0 < (iPlusLogArg D (qI (-1))).lower) &&
  (decide (0 < (iPlusLogArg D (qI 1)).lower) &&
  (decide (0 < (iMinusLogArg D (qI (-1))).lower) &&
    decide (0 < (iMinusLogArg D (qI 1)).lower))))))))))

private theorem legacyCellWellFormed_of_bool {D : RI}
    (h : legacyCellWellFormedB D = true) : LegacyCellWellFormed D := by
  simp only [legacyCellWellFormedB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2⟩

private theorem iTPlus_contains {D : RI} {delta : ℝ} (hD : D.Contains delta) :
    (iTPlus D).Contains (legacyTPlus delta) := by
  simpa [legacyTPlus] using
    legacyRadiusI_contains.add ((contains_point (4 / 5)).mul hD)

private theorem iTMinus_contains {D : RI} {delta : ℝ} (hD : D.Contains delta) :
    (iTMinus D).Contains (legacyTMinus delta) := by
  simpa [legacyTMinus] using
    legacyRadiusI_contains.sub ((contains_point (4 / 5)).mul hD)

private theorem iA_contains {D : RI} {delta : ℝ} (hD : D.Contains delta) :
    (iA D).Contains (legacyA delta) := by
  simpa [iA, qI, legacyA] using
    legacyRadiusI_contains.sub ((contains_point (1 / 5)).mul hD)

private theorem iB_contains {D : RI} {delta : ℝ} (hD : D.Contains delta) :
    (iB D).Contains (legacyB delta) := by
  simpa [iB, qI, legacyB] using
    legacyRadiusI_contains.add ((contains_point (1 / 5)).mul hD)

private theorem iDenPlus_contains {D : RI} {delta : ℝ} (hD : D.Contains delta) :
    (iDenPlus D).Contains (1 + legacyTPlus delta ^ 2) :=
  by simpa using (contains_point 1).add (iTPlus_contains hD).square

private theorem iDenMinus_contains {D : RI} {delta : ℝ} (hD : D.Contains delta) :
    (iDenMinus D).Contains (1 + legacyTMinus delta ^ 2) :=
  by simpa using (contains_point 1).add (iTMinus_contains hD).square

private theorem iA0_contains {D : RI} {delta : ℝ}
    (hD : D.Contains delta) (hw : LegacyCellWellFormed D) :
    (iA0 D).Contains (legacyA0 delta) :=
  (iA_contains hD).div (iDenPlus_contains hD) hw.denPlus

private theorem iB0_contains {D : RI} {delta : ℝ}
    (hD : D.Contains delta) (hw : LegacyCellWellFormed D) :
    (iB0 D).Contains (legacyB0 delta) :=
  (iB_contains hD).div (iDenMinus_contains hD) hw.denMinus

private theorem iLambda_contains {D : RI} {delta : ℝ}
    (hD : D.Contains delta) (hw : LegacyCellWellFormed D) :
    (iLambda D).Contains (legacyLambda delta) := by
  exact (iB0_contains hD hw).div
    ((iA0_contains hD hw).add (iB0_contains hD hw)) hw.lambdaDen

private theorem iQueryPlus_contains (terms : ℕ) {D : RI} {delta : ℝ}
    (hD : D.Contains delta) (hw : LegacyCellWellFormed D) :
    ((iQueryArgPlus D).logarithm terms).Contains
      (Real.log (1 + 1 / legacyTPlus delta ^ 2)) := by
  apply Contains.logarithm terms hw.queryPlus
  simpa using (contains_point 1).add
    ((contains_point 1).div (iTPlus_contains hD).square hw.tPlusSq)

private theorem iQueryMinus_contains (terms : ℕ) {D : RI} {delta : ℝ}
    (hD : D.Contains delta) (hw : LegacyCellWellFormed D) :
    ((iQueryArgMinus D).logarithm terms).Contains
      (Real.log (1 + 1 / legacyTMinus delta ^ 2)) := by
  apply Contains.logarithm terms hw.queryMinus
  simpa using (contains_point 1).add
    ((contains_point 1).div (iTMinus_contains hD).square hw.tMinusSq)

private theorem iPhiPlus_contains (terms : ℕ) {D : RI} {delta : ℝ}
    (hD : D.Contains delta) (hw : LegacyCellWellFormed D) (z : ℚ)
    (hlog : 0 < (iPlusLogArg D (qI z)).lower) :
    (iPhiPlus terms D (qI z)).Contains
      (phiPlus delta (legacyA delta) (z : ℝ)) := by
  have hz : (qI z).Contains (z : ℝ) := contains_point z
  have hden := iDenPlus_contains hD
  have hcoeff := ((contains_point 2).mul (iA_contains hD)).div hden hw.denPlus
  have hcubic := hcoeff.mul (hz.square.mul hz)
  have hlogarg : (iPlusLogArg D (qI z)).Contains
      (1 + legacyA delta * (z : ℝ)) :=
    by simpa using (contains_point 1).add ((iA_contains hD).mul hz)
  have hlogmem := hlogarg.logarithm terms hlog
  have hlinear := ((iA_contains hD).mul hz).sub hlogmem
  have htotal := hcubic.add ((contains_point 3).mul hlinear)
  rw [show phiPlus delta (legacyA delta) (z : ℝ) =
      2 * legacyA delta / (1 + legacyTPlus delta ^ 2) *
          ((z : ℝ) ^ 2 * z) +
        3 * (legacyA delta * z -
          Real.log (1 + legacyA delta * z)) by
    simp only [phiPlus]
    rw [show delta + legacyA delta = legacyTPlus delta by
      simp [legacyA, legacyTPlus]
      ring]
    ring]
  simpa using htotal

private theorem iPhiMinus_contains (terms : ℕ) {D : RI} {delta : ℝ}
    (hD : D.Contains delta) (hw : LegacyCellWellFormed D) (z : ℚ)
    (hlog : 0 < (iMinusLogArg D (qI z)).lower) :
    (iPhiMinus terms D (qI z)).Contains
      (phiMinus delta (legacyB delta) (z : ℝ)) := by
  have hz : (qI z).Contains (z : ℝ) := contains_point z
  have hden := iDenMinus_contains hD
  have hcoeff := ((contains_point (-2)).mul (iB_contains hD)).div hden hw.denMinus
  have hcubic := hcoeff.mul (hz.square.mul hz)
  have hlogarg : (iMinusLogArg D (qI z)).Contains
      (1 - legacyB delta * (z : ℝ)) :=
    by simpa using (contains_point 1).sub ((iB_contains hD).mul hz)
  have hlogmem := hlogarg.logarithm terms hlog
  have hlinear := ((iB_contains hD).mul hz).neg.sub hlogmem
  have htotal := hcubic.add ((contains_point 3).mul hlinear)
  rw [show phiMinus delta (legacyB delta) (z : ℝ) =
      (-2) * legacyB delta / (1 + legacyTMinus delta ^ 2) *
          ((z : ℝ) ^ 2 * z) +
        3 * (-(legacyB delta * z) -
          Real.log (1 - legacyB delta * z)) by
    simp only [phiMinus]
    rw [show legacyB delta - delta = legacyTMinus delta by
      simp [legacyB, legacyTMinus]
      ring]
    ring]
  simpa using htotal

private theorem iPhiAverage_contains (terms : ℕ) {D : RI} {delta : ℝ}
    (hD : D.Contains delta) (hw : LegacyCellWellFormed D) (z : ℚ)
    (hplus : 0 < (iPlusLogArg D (qI z)).lower)
    (hminus : 0 < (iMinusLogArg D (qI z)).lower) :
    (iPhiAverage terms D (qI z)).Contains
      (phiAverage delta (legacyA delta) (legacyB delta)
        (legacyLambda delta) (z : ℝ)) := by
  have hlambda := iLambda_contains hD hw
  have honeMinus := (contains_point 1).sub hlambda
  have hsecond : ((oneI.sub (iLambda D)).mul
      (iPhiMinus terms D (qI z))).Contains
        ((1 - legacyLambda delta) *
          phiMinus delta (legacyB delta) (z : ℝ)) := by
    simpa [oneI, qI] using
      (honeMinus.mul (iPhiMinus_contains terms hD hw z hminus))
  exact (hlambda.mul (iPhiPlus_contains terms hD hw z hplus)).add hsecond

/-- Soundness of a single directed interval evaluation. -/
theorem legacyEnvelopeI_contains (terms : ℕ) {D : RI} {delta : ℝ}
    (hD : D.Contains delta) (hw : LegacyCellWellFormed D) :
    (legacyEnvelopeI terms D).Contains (legacyEnvelope delta) := by
  have hlambda := iLambda_contains hD hw
  have hbasePlus := hlambda.mul (iQueryPlus_contains terms hD hw)
  have hbaseMinus := ((contains_point 1).sub hlambda).mul
    (iQueryMinus_contains terms hD hw)
  have hneg := iPhiAverage_contains terms hD hw (-1) hw.plusNeg hw.minusNeg
  have hpos := iPhiAverage_contains terms hD hw 1 hw.plusPos hw.minusPos
  have htotal := (hbasePlus.add hbaseMinus).add (hneg.maximum hpos)
  simpa [legacyEnvelopeI, legacyEnvelope, rho] using htotal

/-- The exact rational determinant ratio used by the efficient curvature
adversary. -/
def legacyK : ℚ := 7361 / 1000

def legacyCellPass (terms : ℕ) (D : RI) : Bool :=
  legacyCellWellFormedB D &&
    decide ((legacyEnvelopeI terms D).upper < logRationalLower terms legacyK)

def intervalMidpoint (D : RI) : ℚ := (D.lower + D.upper) / 2
def intervalLeft (D : RI) : RI := ⟨D.lower, intervalMidpoint D⟩
def intervalRight (D : RI) : RI := ⟨intervalMidpoint D, D.upper⟩

/-- Adaptive exact-rational certificate checker. -/
def legacyRecursiveCheck (terms : ℕ) : ℕ → RI → Bool
  | 0, D => legacyCellPass terms D
  | depth + 1, D =>
      legacyCellPass terms D ||
        (legacyRecursiveCheck terms depth (intervalLeft D) &&
          legacyRecursiveCheck terms depth (intervalRight D))

private theorem cellPass_sound {terms : ℕ} {D : RI}
    (hpass : legacyCellPass terms D = true) {delta : ℝ}
    (hD : D.Contains delta) : legacyEnvelope delta < Real.log (legacyK : ℝ) := by
  have hp : legacyCellWellFormedB D = true ∧
      (legacyEnvelopeI terms D).upper < logRationalLower terms legacyK := by
    simpa [legacyCellPass, Bool.and_eq_true, decide_eq_true_eq] using hpass
  have hw := legacyCellWellFormed_of_bool hp.1
  have hmem := legacyEnvelopeI_contains terms hD hw
  have hlog := log_rational_mem_pos terms legacyK (by norm_num [legacyK])
  have hpR : ((legacyEnvelopeI terms D).upper : ℝ) <
      (logRationalLower terms legacyK : ℝ) := by exact_mod_cast hp.2
  exact hmem.2.trans_lt (hpR.trans_le hlog.1)

private theorem left_contains_of_contains {D : RI} {x : ℝ}
    (hx : D.Contains x) (hxm : x ≤ (intervalMidpoint D : ℚ)) :
    (intervalLeft D).Contains x := ⟨hx.1, hxm⟩

private theorem right_contains_of_contains {D : RI} {x : ℝ}
    (hx : D.Contains x) (hmx : (intervalMidpoint D : ℚ) ≤ x) :
    (intervalRight D).Contains x := ⟨hmx, hx.2⟩

theorem legacyRecursiveCheck_sound {terms depth : ℕ} {D : RI}
    (hcheck : legacyRecursiveCheck terms depth D = true) {delta : ℝ}
    (hD : D.Contains delta) : legacyEnvelope delta < Real.log (legacyK : ℝ) := by
  induction depth generalizing D with
  | zero => exact cellPass_sound hcheck hD
  | succ depth ih =>
      by_cases hleaf : legacyCellPass terms D = true
      · exact cellPass_sound hleaf hD
      · have hchildren : legacyRecursiveCheck terms depth (intervalLeft D) = true ∧
            legacyRecursiveCheck terms depth (intervalRight D) = true := by
          simpa [legacyRecursiveCheck, hleaf] using hcheck
        by_cases hx : delta ≤ (intervalMidpoint D : ℚ)
        · exact ih hchildren.1 (left_contains_of_contains hD hx)
        · exact ih hchildren.2
            (right_contains_of_contains hD (le_of_not_ge hx))

def legacyCover : RI := ⟨0, 397 / 1000⟩

/-- The complete finite calculation.  The soundness theorem above is checked
by the kernel; `native_decide` evaluates only its exact rational Boolean
premise and is listed explicitly in the audit trust boundary. -/
theorem legacy_certificate_check :
    legacyRecursiveCheck 40 16 legacyCover = true := by
  native_decide

/-- Certified scalar inequality on the full near-central offset range. -/
theorem legacy_scalar_certificate {delta : ℝ} (hd0 : 0 ≤ delta)
    (hd1 : delta ≤ (397 / 1000 : ℝ)) :
    legacyEnvelope delta < Real.log (legacyK : ℝ) := by
  apply legacyRecursiveCheck_sound legacy_certificate_check
  exact ⟨by simpa [legacyCover, Contains] using hd0,
    by simpa [legacyCover, Contains] using hd1⟩

end StrengthenedCurvature
end SortingAdversary
