import SortingAdversary.StrengthenedCurvature.CrossClosed
import SortingAdversary.StrengthenedCurvature.DirectedInterval
import SortingAdversary.StrengthenedCurvature.RhoConvexity
import SortingAdversary.StrengthenedCurvature.Schedule

/-!
# Exact rational interval evaluator for the strengthened envelope

All executable quantities in this file are rational.  Square roots are
enclosed by checked squared endpoints and logarithms by the proved Taylor
bounds from `DirectedInterval`.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open RationalInterval

set_option maxHeartbeats 200000

abbrev SRI := RationalInterval

abbrev sPoint (q : ℚ) : SRI := point q
abbrev sOne : SRI := sPoint 1
abbrev sTwo : SRI := sPoint 2
abbrev sThree : SRI := sPoint 3
abbrev sHalf : SRI := sPoint (1 / 2)

/-- Rational bisection, used only to propose endpoints whose squared
inequalities are checked again by `SqrtCertificate`. -/
@[irreducible] def sqrtBisect (q : ℚ) : ℕ → SRI → SRI
  | 0, I => I
  | depth + 1, I =>
      let m := (I.lower + I.upper) / 2
      if m ^ 2 ≤ q then sqrtBisect q depth ⟨m, I.upper⟩
      else sqrtBisect q depth ⟨I.lower, m⟩

@[irreducible] def sqrtPointI (depth : ℕ) (q : ℚ) : SRI :=
  sqrtBisect q depth ⟨0, 1⟩

abbrev scheduleWeightI (i : Fin 22) (D : SRI) : SRI :=
  (D.sub (sPoint (scheduleDelta i.castSucc))).div
    (sPoint (scheduleDelta i.succ - scheduleDelta i.castSucc))

abbrev scheduleAI (i : Fin 22) (D : SRI) : SRI :=
  (sPoint (scheduleAKnot i.castSucc)).add
    ((scheduleWeightI i D).mul
      (sPoint (scheduleAKnot i.succ - scheduleAKnot i.castSucc)))

abbrev scheduleBI (i : Fin 22) (D : SRI) : SRI :=
  (sPoint (scheduleBKnot i.castSucc)).add
    ((scheduleWeightI i D).mul
      (sPoint (scheduleBKnot i.succ - scheduleBKnot i.castSucc)))

abbrev queryArgPlusI (D A : SRI) : SRI :=
  sOne.add (sOne.div (D.add A).square)

abbrev queryArgMinusI (D B : SRI) : SRI :=
  sOne.add (sOne.div (B.sub D).square)

abbrev plusLogArgI (A Z : SRI) : SRI := sOne.add (A.mul Z)
abbrev minusLogArgI (B Z : SRI) : SRI := sOne.sub (B.mul Z)

abbrev phiPlusI (terms : ℕ) (D A Z : SRI) : SRI :=
  let cubic := ((sTwo.mul A).div (sOne.add (D.add A).square)).mul
    (Z.square.mul Z)
  let logarithmic := sThree.mul
    ((A.mul Z).sub ((plusLogArgI A Z).logarithm terms))
  cubic.add logarithmic

abbrev phiMinusI (terms : ℕ) (D B Z : SRI) : SRI :=
  let cubic := (((sPoint (-2)).mul B).div
    (sOne.add (B.sub D).square)).mul (Z.square.mul Z)
  let logarithmic := sThree.mul
    (((B.mul Z).neg).sub ((minusLogArgI B Z).logarithm terms))
  cubic.add logarithmic

abbrev phiAverageI (terms : ℕ) (D A B Lambda Z : SRI) : SRI :=
  (Lambda.mul (phiPlusI terms D A Z)).add
    ((sOne.sub Lambda).mul (phiMinusI terms D B Z))

abbrev rhoZeroI (A B Lambda : SRI) : SRI :=
  (sPoint (3 / 2)).mul
    ((Lambda.mul A.square).add ((sOne.sub Lambda).mul B.square))

abbrev rhoEndpointI (terms : ℕ) (D A B Lambda Z : SRI) : SRI :=
  (phiAverageI terms D A B Lambda Z).div Z.square

abbrev positiveMaxI (terms : ℕ) (D A B Lambda Pmax : SRI) : SRI :=
  (rhoZeroI A B Lambda).maximum
    (rhoEndpointI terms D A B Lambda Pmax)

abbrev negativeMaxI (terms : ℕ) (D A B Lambda Nmax : SRI) : SRI :=
  (rhoZeroI A B Lambda).maximum
    (rhoEndpointI terms D A B Lambda (Nmax.neg))

abbrev baseI (terms : ℕ) (D A B Lambda : SRI) : SRI :=
  (Lambda.mul ((queryArgPlusI D A).logarithm terms)).add
    ((sOne.sub Lambda).mul ((queryArgMinusI D B).logarithm terms))

/-- The sharp affine upper bound for `r M₊ + (1-r) M₋` once the two
endpoint maxima have been bounded by rational upper endpoints. -/
def mixtureUpper (R MP MN : SRI) : ℚ :=
  max
    (R.lower * MP.upper + (1 - R.lower) * MN.upper)
    (R.upper * MP.upper + (1 - R.upper) * MN.upper)

def envelopeUpperI (terms : ℕ) (D A B Lambda Pmax Nmax R : SRI)
    (savingPlus savingMinus : ℚ) : SRI :=
  (baseI terms D A B Lambda).add
    (sPoint (mixtureUpper R
      (positiveMaxI terms D A B Lambda Pmax)
      (negativeMaxI terms D A B Lambda Nmax))) |>.sub
    ((Lambda.mul (sPoint savingPlus)).add
      ((sOne.sub Lambda).mul (sPoint savingMinus)))

def EnvelopeWellFormed (terms : ℕ) (i : Fin 22) (D R : SRI)
    (lambda : ℚ) : Prop :=
  let A := scheduleAI i D
  let B := scheduleBI i D
  let Pmax := sqrtPointI 44 R.upper
  let Nmax := sqrtPointI 44 (1 - R.lower)
  0 < scheduleDelta i.succ - scheduleDelta i.castSucc ∧
  SqrtCertificate (sPoint R.upper) Pmax ∧
  SqrtCertificate (sPoint (1 - R.lower)) Nmax ∧
  0 ≤ R.lower ∧ R.upper ≤ 1 ∧
  0 < A.lower ∧ A.upper < 1 ∧
  0 < B.lower ∧ B.upper < 1 ∧
  D.upper < B.lower ∧
  0 ≤ lambda ∧ lambda ≤ 1 ∧
  0 < (D.add A).square.lower ∧
  0 < (B.sub D).square.lower ∧
  0 < (queryArgPlusI D A).lower ∧
  0 < (queryArgMinusI D B).lower ∧
  0 < Pmax.square.lower ∧
  0 < Nmax.square.lower ∧
  0 < Nmax.neg.square.lower ∧
  0 < (plusLogArgI A Pmax).lower ∧
  0 < (minusLogArgI B Pmax).lower ∧
  0 < (plusLogArgI A Nmax.neg).lower ∧
  0 < (minusLogArgI B Nmax.neg).lower

theorem scheduleAI_contains {i : Fin 22} {D : SRI} {delta : ℝ}
    (hD : D.Contains delta)
    (hgap : 0 < scheduleDelta i.succ - scheduleDelta i.castSucc) :
    (scheduleAI i D).Contains (scheduleA i delta) := by
  have hw : (scheduleWeightI i D).Contains (scheduleWeight i delta) := by
    have hgapmem : (sPoint
        (scheduleDelta i.succ - scheduleDelta i.castSucc)).Contains
        ((scheduleDelta i.succ : ℝ) - scheduleDelta i.castSucc) := by
      simpa only [Rat.cast_sub] using
        (contains_point (scheduleDelta i.succ - scheduleDelta i.castSucc))
    exact (hD.sub (contains_point _)).div hgapmem hgap
  simpa [scheduleA, scheduleWeight] using
    (contains_point (scheduleAKnot i.castSucc)).add
      (hw.mul (contains_point
        (scheduleAKnot i.succ - scheduleAKnot i.castSucc)))

theorem scheduleBI_contains {i : Fin 22} {D : SRI} {delta : ℝ}
    (hD : D.Contains delta)
    (hgap : 0 < scheduleDelta i.succ - scheduleDelta i.castSucc) :
    (scheduleBI i D).Contains (scheduleB i delta) := by
  have hw : (scheduleWeightI i D).Contains (scheduleWeight i delta) := by
    have hgapmem : (sPoint
        (scheduleDelta i.succ - scheduleDelta i.castSucc)).Contains
        ((scheduleDelta i.succ : ℝ) - scheduleDelta i.castSucc) := by
      simpa only [Rat.cast_sub] using
        (contains_point (scheduleDelta i.succ - scheduleDelta i.castSucc))
    exact (hD.sub (contains_point _)).div hgapmem hgap
  simpa [scheduleB, scheduleWeight] using
    (contains_point (scheduleBKnot i.castSucc)).add
      (hw.mul (contains_point
        (scheduleBKnot i.succ - scheduleBKnot i.castSucc)))

theorem phiPlusI_contains (terms : ℕ) {D A Z : SRI}
    {delta a z : ℝ} (hD : D.Contains delta) (hA : A.Contains a)
    (hZ : Z.Contains z) (hden : 0 < (sOne.add (D.add A).square).lower)
    (hlog : 0 < (plusLogArgI A Z).lower) :
    (phiPlusI terms D A Z).Contains (phiPlus delta a z) := by
  have ht := hD.add hA
  have hdenmem := (contains_point 1).add ht.square
  have hcoeff := ((contains_point 2).mul hA).div hdenmem hden
  have hcubic := hcoeff.mul (hZ.square.mul hZ)
  have harg := (contains_point 1).add (hA.mul hZ)
  have hlogmem := harg.logarithm terms hlog
  have htotal := hcubic.add ((contains_point 3).mul ((hA.mul hZ).sub hlogmem))
  convert htotal using 1 <;> simp only [phiPlus] <;> ring

theorem phiMinusI_contains (terms : ℕ) {D B Z : SRI}
    {delta b z : ℝ} (hD : D.Contains delta) (hB : B.Contains b)
    (hZ : Z.Contains z) (hden : 0 < (sOne.add (B.sub D).square).lower)
    (hlog : 0 < (minusLogArgI B Z).lower) :
    (phiMinusI terms D B Z).Contains (phiMinus delta b z) := by
  have ht := hB.sub hD
  have hdenmem := (contains_point 1).add ht.square
  have hcoeff := ((contains_point (-2)).mul hB).div hdenmem hden
  have hcubic := hcoeff.mul (hZ.square.mul hZ)
  have harg := (contains_point 1).sub (hB.mul hZ)
  have hlogmem := harg.logarithm terms hlog
  have htotal := hcubic.add
    ((contains_point 3).mul ((hB.mul hZ).neg.sub hlogmem))
  convert htotal using 1 <;> simp only [phiMinus] <;> ring

theorem phiAverageI_contains (terms : ℕ) {D A B Lambda Z : SRI}
    {delta a b lambda z : ℝ}
    (hD : D.Contains delta) (hA : A.Contains a) (hB : B.Contains b)
    (hLambda : Lambda.Contains lambda) (hZ : Z.Contains z)
    (hdenP : 0 < (sOne.add (D.add A).square).lower)
    (hdenN : 0 < (sOne.add (B.sub D).square).lower)
    (hlogP : 0 < (plusLogArgI A Z).lower)
    (hlogN : 0 < (minusLogArgI B Z).lower) :
    (phiAverageI terms D A B Lambda Z).Contains
      (phiAverage delta a b lambda z) := by
  have hp := phiPlusI_contains terms hD hA hZ hdenP hlogP
  have hm := phiMinusI_contains terms hD hB hZ hdenN hlogN
  simpa [phiAverage] using
    (hLambda.mul hp).add (((contains_point 1).sub hLambda).mul hm)

theorem rhoZeroI_contains {A B Lambda : SRI} {delta a b lambda : ℝ}
    (hA : A.Contains a) (hB : B.Contains b)
    (hLambda : Lambda.Contains lambda) :
    (rhoZeroI A B Lambda).Contains (rho delta a b lambda 0) := by
  have h := (contains_point (3 / 2)).mul
    ((hLambda.mul hA.square).add
      (((contains_point 1).sub hLambda).mul hB.square))
  simpa [rho, phiAverage] using h

theorem rhoEndpointI_contains (terms : ℕ) {D A B Lambda Z : SRI}
    {delta a b lambda z : ℝ}
    (hD : D.Contains delta) (hA : A.Contains a) (hB : B.Contains b)
    (hLambda : Lambda.Contains lambda) (hZ : Z.Contains z)
    (hZsq : 0 < Z.square.lower)
    (hdenP : 0 < (sOne.add (D.add A).square).lower)
    (hdenN : 0 < (sOne.add (B.sub D).square).lower)
    (hlogP : 0 < (plusLogArgI A Z).lower)
    (hlogN : 0 < (minusLogArgI B Z).lower) :
    (rhoEndpointI terms D A B Lambda Z).Contains
      (rho delta a b lambda z) := by
  have hphi := phiAverageI_contains terms hD hA hB hLambda hZ
    hdenP hdenN hlogP hlogN
  have hdiv := hphi.div hZ.square hZsq
  have hz : z ≠ 0 := by
    intro hz0
    subst z
    have := hZ.square.1
    norm_num at this
    have hpos : (0 : ℝ) < Z.square.lower := by exact_mod_cast hZsq
    linarith
  simpa [rho, hz] using hdiv

abbrev crossUI (P L : SRI) : SRI := sOne.add (P.mul L)
abbrev crossVI (N L : SRI) : SRI := sOne.sub (N.mul L)

/-- Directed interval evaluation of Appendix A, equation (69). -/
def crossClosedI (terms : ℕ) (Ell P N L : SRI) : SRI :=
  let U := crossUI P L
  let V := crossVI N L
  let T1 := ((P.mul Ell).add sOne).mul
      (sOne.sub (sOne.div U)) |>.sub (U.logarithm terms)
  let T2 := ((N.mul Ell).sub sOne).mul
      ((sOne.div V).sub sOne) |>.sub (V.logarithm terms)
  let J1 := (((P.mul Ell).add sOne).mul (U.logarithm terms) |>.sub
      (U.sub sOne)).div P.square
  let J2 := ((((N.mul Ell).sub sOne).neg.mul (V.logarithm terms)).add
      (sOne.sub V)).div N.square
  let J3 := ((P.div (P.add N)).mul J1).add
      ((N.div (P.add N)).mul J2)
  sHalf.mul ((T1.add T2).sub (((sTwo.mul P).mul N).mul J3))

def CrossClosedWellFormed (Ell P N L : SRI) : Prop :=
  0 < (crossUI P L).lower ∧
  0 < (crossVI N L).lower ∧
  0 < P.square.lower ∧
  0 < N.square.lower ∧
  0 < (P.add N).lower

theorem crossClosedI_contains (terms : ℕ) {Ell P N L : SRI}
    {ell p n l : ℝ} (hEll : Ell.Contains ell) (hP : P.Contains p)
    (hN : N.Contains n) (hL : L.Contains l)
    (hw : CrossClosedWellFormed Ell P N L) :
    (crossClosedI terms Ell P N L).Contains (crossClosed ell p n l) := by
  rcases hw with ⟨hUpos, hVpos, hPsq, hNsq, hPN⟩
  have hU := (contains_point 1).add (hP.mul hL)
  have hV := (contains_point 1).sub (hN.mul hL)
  have hlogU := hU.logarithm terms hUpos
  have hlogV := hV.logarithm terms hVpos
  have hinvU := (contains_point 1).div hU hUpos
  have hinvV := (contains_point 1).div hV hVpos
  have hPE := hP.mul hEll
  have hNE := hN.mul hEll
  have hT1 := ((hPE.add (contains_point 1)).mul
    ((contains_point 1).sub hinvU)).sub hlogU
  have hT2 := ((hNE.sub (contains_point 1)).mul
    (hinvV.sub (contains_point 1))).sub hlogV
  have hJ1 := (((hPE.add (contains_point 1)).mul hlogU).sub
    (hU.sub (contains_point 1))).div hP.square hPsq
  have hJ2 := ((((hNE.sub (contains_point 1)).neg).mul hlogV).add
    ((contains_point 1).sub hV)).div hN.square hNsq
  have hsum := hP.add hN
  have hJ3 := ((hP.div hsum hPN).mul hJ1).add
    ((hN.div hsum hPN).mul hJ2)
  have htotal := (contains_point (1 / 2)).mul
    ((hT1.add hT2).sub ((((contains_point 2).mul hP).mul hN).mul hJ3))
  unfold crossClosedI crossClosed
  dsimp only
  convert htotal using 1 <;> ring

abbrev crossCutoffI (P N : SRI) : SRI :=
  (P.sub N).div ((sTwo.mul P).mul N)

@[irreducible] def crossLength (ell : ℚ) (P N : SRI) : ℚ :=
  min ell (crossCutoffI P N).lower

def crossSavingI (terms : ℕ) (ell r₀ : ℚ) : SRI :=
  let P := sqrtPointI 44 r₀
  let N := sqrtPointI 44 (1 - r₀)
  let L := crossLength ell P N
  crossClosedI terms (sPoint ell) P N (sPoint L)

def crossSavingLower (terms : ℕ) (ell r₀ : ℚ) : ℚ :=
  max 0 (crossSavingI terms ell r₀).lower

def CrossSavingWellFormed (ell r₀ : ℚ) : Prop :=
  let P := sqrtPointI 44 r₀
  let N := sqrtPointI 44 (1 - r₀)
  let L := crossLength ell P N
  SqrtCertificate (sPoint r₀) P ∧
  SqrtCertificate (sPoint (1 - r₀)) N ∧
  1 / 2 < r₀ ∧ r₀ < 1 ∧
  0 ≤ L ∧ L ≤ ell ∧
  0 < ((sTwo.mul P).mul N).lower ∧
  L ≤ (crossCutoffI P N).lower ∧
  CrossClosedWellFormed (sPoint ell) P N (sPoint L)

theorem crossSavingLower_le_gammaPlus (terms : ℕ)
    {ell r₀ : ℚ} {a r : ℝ} (hw : CrossSavingWellFormed ell r₀)
    (hella : (ell : ℝ) ≤ a) (ha1 : a < 1)
    (hrr₀ : (r₀ : ℝ) ≤ r) (hr1 : r ≤ 1) :
    (crossSavingLower terms ell r₀ : ℝ) ≤ gammaPlus a r := by
  let P := sqrtPointI 44 r₀
  let N := sqrtPointI 44 (1 - r₀)
  let L := crossLength ell P N
  change max 0 (crossSavingI terms ell r₀).lower ≤ gammaPlus a r
  rcases hw with ⟨hPsqrt, hNsqrt, hrhalf, hrone, hL0, hLell,
    hcutden, hLcut, hclosed⟩
  have hP := Contains.sqrt (contains_point r₀) hPsqrt
  have hN := Contains.sqrt (contains_point (1 - r₀)) hNsqrt
  have hden := (((contains_point 2).mul hP).mul hN)
  have hcutmem := (hP.sub hN).div hden hcutden
  have hcutR : (L : ℝ) ≤
      (Real.sqrt (r₀ : ℝ) - Real.sqrt (1 - (r₀ : ℝ))) /
        (2 * Real.sqrt (r₀ : ℝ) * Real.sqrt (1 - (r₀ : ℝ))) := by
    have hlower : (L : ℝ) ≤ ((crossCutoffI P N).lower : ℝ) := by
      exact_mod_cast hLcut
    have hmem : ((crossCutoffI P N).lower : ℝ) ≤
        (Real.sqrt (r₀ : ℝ) - Real.sqrt (1 - (r₀ : ℝ))) /
          (2 * Real.sqrt (r₀ : ℝ) * Real.sqrt (1 - (r₀ : ℝ))) := by
      simpa only [Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat] using hcutmem.1
    exact hlower.trans hmem
  have hclosedmem := crossClosedI_contains terms (contains_point ell) hP hN
    (contains_point L) hclosed
  have hlower : ((crossSavingI terms ell r₀).lower : ℝ) ≤
      crossClosed (ell : ℝ) (Real.sqrt (r₀ : ℝ))
        (Real.sqrt (1 - (r₀ : ℝ))) L := by
    change ((crossClosedI terms (sPoint ell) P N (sPoint L)).lower : ℝ) ≤ _
    simpa only [Rat.cast_sub, Rat.cast_one] using hclosedmem.1
  have hanalytic := crossClosed_le_gammaPlus_of_half_lt
    (show (1 / 2 : ℝ) < (r₀ : ℝ) by
      have h : (((1 / 2 : ℚ) : ℝ)) < (r₀ : ℝ) := by
        exact_mod_cast hrhalf
      norm_num at h ⊢
      exact h)
    (show (r₀ : ℝ) < 1 by exact_mod_cast hrone)
    hrr₀ hr1
    (show (0 : ℝ) ≤ L by exact_mod_cast hL0)
    (show (L : ℝ) ≤ ell by exact_mod_cast hLell)
    hella ha1 hcutR
  rw [Rat.cast_max, Rat.cast_zero, max_le_iff]
  exact ⟨gammaPlus_nonneg (le_trans (by exact_mod_cast hL0.trans hLell) hella),
    hlower.trans hanalytic⟩

def constantSavingLower (ell r₁ : ℚ) : ℚ :=
  let P := sqrtPointI 44 r₁
  let N := sqrtPointI 44 (1 - r₁)
  ell ^ 2 / 4 * (max 0 (N.lower - P.upper)) ^ 2

def ConstantSavingWellFormed (r₁ : ℚ) : Prop :=
  let P := sqrtPointI 44 r₁
  let N := sqrtPointI 44 (1 - r₁)
  SqrtCertificate (sPoint r₁) P ∧
  SqrtCertificate (sPoint (1 - r₁)) N ∧
  0 ≤ r₁ ∧ r₁ ≤ 1 / 2

theorem constantSavingLower_le_gammaPlus
    {ell r₁ : ℚ} {a r : ℝ} (hw : ConstantSavingWellFormed r₁)
    (hell0 : 0 ≤ ell) (hella : (ell : ℝ) ≤ a)
    (hr0 : 0 ≤ r) (hrr₁ : r ≤ (r₁ : ℝ)) :
    (constantSavingLower ell r₁ : ℝ) ≤ gammaPlus a r := by
  let P := sqrtPointI 44 r₁
  let N := sqrtPointI 44 (1 - r₁)
  rcases hw with ⟨hPsqrt, hNsqrt, hr₁0, hr₁half⟩
  have hP := Contains.sqrt (contains_point r₁) hPsqrt
  have hN := Contains.sqrt (contains_point (1 - r₁)) hNsqrt
  have hgapLower : (N.lower : ℝ) - (P.upper : ℝ) ≤
      Real.sqrt (1 - (r₁ : ℝ)) - Real.sqrt (r₁ : ℝ) := by
    simpa only [Rat.cast_sub, Rat.cast_one] using sub_le_sub hN.1 hP.2
  have hgapActual : 0 ≤
      Real.sqrt (1 - (r₁ : ℝ)) - Real.sqrt (r₁ : ℝ) := by
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by
      exact_mod_cast (show r₁ ≤ 1 - r₁ by linarith)))
  have hmaxLower : (max 0 (N.lower - P.upper) : ℚ) ≤
      Real.sqrt (1 - (r₁ : ℝ)) - Real.sqrt (r₁ : ℝ) := by
    rw [Rat.cast_max, Rat.cast_zero]
    exact max_le hgapActual (by simpa only [Rat.cast_sub] using hgapLower)
  have hmax0 : (0 : ℝ) ≤ (max 0 (N.lower - P.upper) : ℚ) := by
    exact_mod_cast (le_max_left (0 : ℚ) (N.lower - P.upper))
  have hsq := (sq_le_sq₀ hmax0 hgapActual).2 hmaxLower
  have hcoeff : (0 : ℝ) ≤ (ell : ℝ) ^ 2 / 4 := by positivity
  have hnumeric : (constantSavingLower ell r₁ : ℝ) ≤
      (ell : ℝ) ^ 2 / 4 *
        (Real.sqrt (1 - (r₁ : ℝ)) - Real.sqrt (r₁ : ℝ)) ^ 2 := by
    change (((ell ^ 2 / 4 * (max 0 (N.lower - P.upper)) ^ 2 : ℚ) : ℝ)) ≤ _
    norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_sub,
      Rat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left hsq hcoeff
  exact hnumeric.trans (constantGap_le_gammaPlus_of_le_half hr0 hrr₁
    (by
      have h : (r₁ : ℝ) ≤ (((1 / 2 : ℚ) : ℝ)) := Rat.cast_le.mpr hr₁half
      norm_num at h ⊢
      exact h)
    (Rat.cast_nonneg.mpr hell0) hella)

def positiveSavingLower (terms : ℕ) (A R : SRI) : ℚ :=
  if R.upper ≤ 1 / 2 then
    constantSavingLower A.lower R.upper
  else if 1 / 2 < R.lower then
    crossSavingLower terms A.lower R.lower
  else 0

def PositiveSavingWellFormed (A R : SRI) : Prop :=
  if R.upper ≤ 1 / 2 then ConstantSavingWellFormed R.upper
  else if 1 / 2 < R.lower then CrossSavingWellFormed A.lower R.lower
  else True

theorem positiveSavingLower_le (terms : ℕ) {A R : SRI} {a r : ℝ}
    (hw : PositiveSavingWellFormed A R) (hA0 : 0 < A.lower)
    (hA : A.Contains a) (ha1 : a < 1) (hR : R.Contains r)
    (hR0 : 0 ≤ R.lower) (hR1 : R.upper ≤ 1) :
    (positiveSavingLower terms A R : ℝ) ≤ gammaPlus a r := by
  have hR1R : (R.upper : ℝ) ≤ 1 := by
    have h : (R.upper : ℝ) ≤ (((1 : ℚ) : ℝ)) := Rat.cast_le.mpr hR1
    norm_num at h ⊢
    exact h
  by_cases hhalf : R.upper ≤ 1 / 2
  · rw [positiveSavingLower, if_pos hhalf]
    rw [PositiveSavingWellFormed, if_pos hhalf] at hw
    exact constantSavingLower_le_gammaPlus hw hA0.le hA.1
      (le_trans (Rat.cast_nonneg.mpr hR0) hR.1) hR.2
  · rw [positiveSavingLower, if_neg hhalf]
    rw [PositiveSavingWellFormed, if_neg hhalf] at hw
    by_cases hcross : 1 / 2 < R.lower
    · rw [if_pos hcross]
      rw [if_pos hcross] at hw
      exact crossSavingLower_le_gammaPlus terms hw hA.1 ha1 hR.1
        (hR.2.trans hR1R)
    · rw [if_neg hcross]
      simpa only [Rat.cast_zero] using
        (gammaPlus_nonneg (r := r) ((Rat.cast_nonneg.mpr hA0.le).trans hA.1))

def negativeSavingLower (terms : ℕ) (B R : SRI) : ℚ :=
  if 1 / 2 ≤ R.lower then
    constantSavingLower B.lower (1 - R.lower)
  else if R.upper < 1 / 2 then
    crossSavingLower terms B.lower (1 - R.upper)
  else 0

def NegativeSavingWellFormed (B R : SRI) : Prop :=
  if 1 / 2 ≤ R.lower then ConstantSavingWellFormed (1 - R.lower)
  else if R.upper < 1 / 2 then CrossSavingWellFormed B.lower (1 - R.upper)
  else True

theorem negativeSavingLower_le (terms : ℕ) {B R : SRI} {b r : ℝ}
    (hw : NegativeSavingWellFormed B R) (hB0 : 0 < B.lower)
    (hB : B.Contains b) (hb1 : b < 1) (hR : R.Contains r)
    (hR0 : 0 ≤ R.lower) (hR1 : R.upper ≤ 1) :
    (negativeSavingLower terms B R : ℝ) ≤ gammaMinus b r := by
  unfold gammaMinus
  have hR0R : (0 : ℝ) ≤ (R.lower : ℝ) := Rat.cast_nonneg.mpr hR0
  have hR1R : (R.upper : ℝ) ≤ 1 := by
    have h : (R.upper : ℝ) ≤ (((1 : ℚ) : ℝ)) := Rat.cast_le.mpr hR1
    norm_num at h ⊢
    exact h
  by_cases hhalf : 1 / 2 ≤ R.lower
  · rw [negativeSavingLower, if_pos hhalf]
    rw [NegativeSavingWellFormed, if_pos hhalf] at hw
    apply constantSavingLower_le_gammaPlus hw hB0.le hB.1
    · linarith [hR.2, hR1R]
    · norm_num only [Rat.cast_sub, Rat.cast_one]
      linarith [hR.1]
  · rw [negativeSavingLower, if_neg hhalf]
    rw [NegativeSavingWellFormed, if_neg hhalf] at hw
    by_cases hcross : R.upper < 1 / 2
    · rw [if_pos hcross]
      rw [if_pos hcross] at hw
      apply crossSavingLower_le_gammaPlus terms hw hB.1 hb1
      · norm_num only [Rat.cast_sub, Rat.cast_one]
        linarith [hR.2]
      · linarith [hR.1, hR0R]
    · rw [if_neg hcross]
      simpa only [Rat.cast_zero] using
        (gammaPlus_nonneg (r := 1 - r)
          ((Rat.cast_nonneg.mpr hB0.le).trans hB.1))

theorem mixture_le_upper {R MP MN : SRI} {r mp mn : ℝ}
    (hR : R.Contains r) (hR0 : 0 ≤ R.lower) (hR1 : R.upper ≤ 1)
    (hmp : mp ≤ (MP.upper : ℝ)) (hmn : mn ≤ (MN.upper : ℝ)) :
    r * mp + (1 - r) * mn ≤ (mixtureUpper R MP MN : ℝ) := by
  have hr0 : 0 ≤ r := (Rat.cast_nonneg.mpr hR0).trans hR.1
  have hr1 : r ≤ 1 := by
    have hu : (R.upper : ℝ) ≤ 1 := by
      have h : (R.upper : ℝ) ≤ (((1 : ℚ) : ℝ)) := Rat.cast_le.mpr hR1
      norm_num at h ⊢
      exact h
    exact hR.2.trans hu
  have hreplace : r * mp + (1 - r) * mn ≤
      r * (MP.upper : ℝ) + (1 - r) * (MN.upper : ℝ) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hmp hr0)
      (mul_le_mul_of_nonneg_left hmn (sub_nonneg.mpr hr1))
  apply hreplace.trans
  rw [mixtureUpper, Rat.cast_max]
  rcases le_total (MP.upper : ℝ) (MN.upper : ℝ) with huv | hvu
  · calc
      r * (MP.upper : ℝ) + (1 - r) * (MN.upper : ℝ) ≤
          (R.lower : ℝ) * (MP.upper : ℝ) +
            (1 - (R.lower : ℝ)) * (MN.upper : ℝ) := by
        have hrl : (R.lower : ℝ) ≤ r := hR.1
        nlinarith [mul_nonneg (sub_nonneg.mpr hrl) (sub_nonneg.mpr huv)]
      _ ≤ max
          ((R.lower * MP.upper + (1 - R.lower) * MN.upper : ℚ) : ℝ)
          ((R.upper * MP.upper + (1 - R.upper) * MN.upper : ℚ) : ℝ) := by
        norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
        exact le_max_left _ _
  · calc
      r * (MP.upper : ℝ) + (1 - r) * (MN.upper : ℝ) ≤
          (R.upper : ℝ) * (MP.upper : ℝ) +
            (1 - (R.upper : ℝ)) * (MN.upper : ℝ) := by
        have hru : r ≤ (R.upper : ℝ) := hR.2
        nlinarith [mul_nonneg (sub_nonneg.mpr hru) (sub_nonneg.mpr hvu)]
      _ ≤ max
          ((R.lower * MP.upper + (1 - R.lower) * MN.upper : ℚ) : ℝ)
          ((R.upper * MP.upper + (1 - R.upper) * MN.upper : ℚ) : ℝ) := by
        norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
        exact le_max_right _ _

/-- Soundness of one exact-rational box evaluation. -/
theorem envelopeUpperI_sound (terms : ℕ) (i : Fin 22) {D R : SRI}
    {lambda : ℚ} {delta r : ℝ}
    (hw : EnvelopeWellFormed terms i D R lambda)
    (hwPlus : PositiveSavingWellFormed (scheduleAI i D) R)
    (hwMinus : NegativeSavingWellFormed (scheduleBI i D) R)
    (hD : D.Contains delta) (hR : R.Contains r) :
    scalarEnvelope delta r (scheduleA i delta) (scheduleB i delta) lambda ≤
      (envelopeUpperI terms D (scheduleAI i D) (scheduleBI i D)
        (sPoint lambda) (sqrtPointI 44 R.upper)
        (sqrtPointI 44 (1 - R.lower)) R
        (positiveSavingLower terms (scheduleAI i D) R)
        (negativeSavingLower terms (scheduleBI i D) R)).upper := by
  let A := scheduleAI i D
  let B := scheduleBI i D
  let Lambda := sPoint lambda
  let Pmax := sqrtPointI 44 R.upper
  let Nmax := sqrtPointI 44 (1 - R.lower)
  let cp := positiveSavingLower terms A R
  let cm := negativeSavingLower terms B R
  rcases hw with ⟨hgap, hPsqrt, hNsqrt, hR0, hR1, hA0, hA1,
    hB0, hB1, _hcross, hl0, hl1, htPsq, htNsq, hqP, hqN, hPsq, hNsq, hNnegSq,
    hlogPP, hlogMP, hlogPN, hlogMN⟩
  have hA := scheduleAI_contains hD hgap
  have hB := scheduleBI_contains hD hgap
  have hLambda : Lambda.Contains (lambda : ℝ) := contains_point lambda
  have ha0 : 0 ≤ scheduleA i delta :=
    (Rat.cast_nonneg.mpr hA0.le).trans hA.1
  have hb0 : 0 ≤ scheduleB i delta :=
    (Rat.cast_nonneg.mpr hB0.le).trans hB.1
  have ha1 : scheduleA i delta < 1 := hA.2.trans_lt (by
    have h : (A.upper : ℝ) < (((1 : ℚ) : ℝ)) := Rat.cast_lt.mpr hA1
    norm_num at h ⊢
    exact h)
  have hb1 : scheduleB i delta < 1 := hB.2.trans_lt (by
    have h : (B.upper : ℝ) < (((1 : ℚ) : ℝ)) := Rat.cast_lt.mpr hB1
    norm_num at h ⊢
    exact h)
  have hl0R : (0 : ℝ) ≤ lambda := Rat.cast_nonneg.mpr hl0
  have hl1R : (lambda : ℝ) ≤ 1 := by
    have h : (lambda : ℝ) ≤ (((1 : ℚ) : ℝ)) := Rat.cast_le.mpr hl1
    norm_num at h ⊢
    exact h
  have hdenP : 0 < (sOne.add (D.add A).square).lower := by
    change 0 < 1 + (D.add A).square.lower
    linarith
  have hdenN : 0 < (sOne.add (B.sub D).square).lower := by
    change 0 < 1 + (B.sub D).square.lower
    linarith
  have hbase : (baseI terms D A B Lambda).Contains
      ((lambda : ℝ) * Real.log (1 + 1 / (delta + scheduleA i delta) ^ 2) +
        (1 - (lambda : ℝ)) *
          Real.log (1 + 1 / (scheduleB i delta - delta) ^ 2)) := by
    have htP := hD.add hA
    have htN := hB.sub hD
    have hargP := (contains_point 1).add
      ((contains_point 1).div htP.square htPsq)
    have hargN := (contains_point 1).add
      ((contains_point 1).div htN.square htNsq)
    have hlogP := hargP.logarithm terms hqP
    have hlogN := hargN.logarithm terms hqN
    simpa [baseI, Lambda] using
      (hLambda.mul hlogP).add (((contains_point 1).sub hLambda).mul hlogN)
  have hPmax := Contains.sqrt (contains_point R.upper) hPsqrt
  have hNmax := Contains.sqrt (contains_point (1 - R.lower)) hNsqrt
  have hr0 : 0 ≤ r := (Rat.cast_nonneg.mpr hR0).trans hR.1
  have hr1 : r ≤ 1 := by
    have hu : (R.upper : ℝ) ≤ 1 := by
      have h : (R.upper : ℝ) ≤ (((1 : ℚ) : ℝ)) := Rat.cast_le.mpr hR1
      norm_num at h ⊢
      exact h
    exact hR.2.trans hu
  have hPactual : Real.sqrt r ≤ Real.sqrt (R.upper : ℝ) :=
    Real.sqrt_le_sqrt hR.2
  have hNactual : Real.sqrt (1 - r) ≤ Real.sqrt (1 - (R.lower : ℝ)) :=
    Real.sqrt_le_sqrt (by linarith [hR.1])
  have hPmaxOne : Real.sqrt (R.upper : ℝ) ≤ 1 := by
    rw [Real.sqrt_le_one]
    have h : (R.upper : ℝ) ≤ (((1 : ℚ) : ℝ)) := Rat.cast_le.mpr hR1
    norm_num at h ⊢
    exact h
  have hNmaxOne : Real.sqrt (1 - (R.lower : ℝ)) ≤ 1 := by
    rw [Real.sqrt_le_one]
    have hl : (0 : ℝ) ≤ (R.lower : ℝ) := Rat.cast_nonneg.mpr hR0
    linarith
  have hconv := rho_convexOn_unitInterval (delta := delta)
    ha0 ha1 hb0 hb1 hl0R hl1R
  have hrho0 := rhoZeroI_contains (delta := delta) hA hB hLambda
  have hrhoP := rhoEndpointI_contains terms hD hA hB hLambda hPmax hPsq
    hdenP hdenN hlogPP hlogMP
  have hNneg : Nmax.neg.Contains (-Real.sqrt (1 - (R.lower : ℝ))) := by
    simpa only [Rat.cast_sub, Rat.cast_one] using hNmax.neg
  have hrhoN := rhoEndpointI_contains terms hD hA hB hLambda hNneg hNnegSq
    hdenP hdenN hlogPN hlogMN
  have hposConvex : rho delta (scheduleA i delta) (scheduleB i delta) lambda
      (Real.sqrt r) ≤
      max (rho delta (scheduleA i delta) (scheduleB i delta) lambda 0)
        (rho delta (scheduleA i delta) (scheduleB i delta) lambda
          (Real.sqrt (R.upper : ℝ))) := by
    apply hconv.le_max_of_mem_Icc
    · exact ⟨by norm_num, by norm_num⟩
    · exact ⟨by linarith [Real.sqrt_nonneg (R.upper : ℝ)], hPmaxOne⟩
    · exact ⟨Real.sqrt_nonneg _, hPactual⟩
  have hnegConvex : rho delta (scheduleA i delta) (scheduleB i delta) lambda
      (-Real.sqrt (1 - r)) ≤
      max (rho delta (scheduleA i delta) (scheduleB i delta) lambda
          (-Real.sqrt (1 - (R.lower : ℝ))))
        (rho delta (scheduleA i delta) (scheduleB i delta) lambda 0) := by
    apply hconv.le_max_of_mem_Icc
    · exact ⟨by linarith [hNmaxOne],
        by linarith [Real.sqrt_nonneg (1 - (R.lower : ℝ))]⟩
    · exact ⟨by norm_num, by norm_num⟩
    · exact ⟨neg_le_neg hNactual, neg_nonpos.mpr (Real.sqrt_nonneg _)⟩
  have hMPmem := hrho0.maximum hrhoP
  have hMNmem := hrho0.maximum hrhoN
  have hMP : positiveEndpointMax delta r (scheduleA i delta)
      (scheduleB i delta) lambda ≤
      ((positiveMaxI terms D A B Lambda Pmax).upper : ℝ) := by
    unfold positiveEndpointMax
    exact (max_le (le_max_left _ _) hposConvex).trans hMPmem.2
  have hMN : negativeEndpointMax delta r (scheduleA i delta)
      (scheduleB i delta) lambda ≤
      ((negativeMaxI terms D A B Lambda Nmax).upper : ℝ) := by
    unfold negativeEndpointMax
    have hactualN :
        rho delta (scheduleA i delta) (scheduleB i delta) lambda
          (-Real.sqrt (1 - r)) ≤
        max
          (rho delta (scheduleA i delta) (scheduleB i delta) lambda 0)
          (rho delta (scheduleA i delta) (scheduleB i delta) lambda
            (-Real.sqrt (1 - (R.lower : ℝ)))) := by
      simpa only [max_comm] using hnegConvex
    have hreorder : max
        (rho delta (scheduleA i delta) (scheduleB i delta) lambda 0)
        (rho delta (scheduleA i delta) (scheduleB i delta) lambda
          (-Real.sqrt (1 - r))) ≤
        max
          (rho delta (scheduleA i delta) (scheduleB i delta) lambda 0)
          (rho delta (scheduleA i delta) (scheduleB i delta) lambda
            (-Real.sqrt (1 - (R.lower : ℝ)))) := by
      exact max_le (le_max_left _ _) hactualN
    exact hreorder.trans hMNmem.2
  have hmix := mixture_le_upper hR hR0 hR1 hMP hMN
  have hcp := positiveSavingLower_le terms hwPlus hA0 hA ha1 hR hR0 hR1
  have hcm := negativeSavingLower_le terms hwMinus hB0 hB hb1 hR hR0 hR1
  have hcorr : (lambda : ℝ) * cp + (1 - (lambda : ℝ)) * cm ≤
      (lambda : ℝ) * gammaPlus (scheduleA i delta) r +
        (1 - (lambda : ℝ)) * gammaMinus (scheduleB i delta) r :=
    add_le_add (mul_le_mul_of_nonneg_left hcp hl0R)
      (mul_le_mul_of_nonneg_left hcm (sub_nonneg.mpr hl1R))
  let surrogate :=
    (lambda : ℝ) * Real.log (1 + 1 / (delta + scheduleA i delta) ^ 2) +
      (1 - (lambda : ℝ)) *
        Real.log (1 + 1 / (scheduleB i delta - delta) ^ 2) +
      (mixtureUpper R (positiveMaxI terms D A B Lambda Pmax)
        (negativeMaxI terms D A B Lambda Nmax) : ℝ) -
      ((lambda : ℝ) * cp + (1 - (lambda : ℝ)) * cm)
  have hscalar : scalarEnvelope delta r (scheduleA i delta)
      (scheduleB i delta) lambda ≤ surrogate := by
    unfold scalarEnvelope surrogate
    linarith
  have hcorrmem := (hLambda.mul (contains_point cp)).add
    (((contains_point 1).sub hLambda).mul (contains_point cm))
  have hsurrogate : (envelopeUpperI terms D A B Lambda Pmax Nmax R cp cm).Contains
      surrogate := by
    have hmixPoint := contains_point (mixtureUpper R
      (positiveMaxI terms D A B Lambda Pmax)
      (negativeMaxI terms D A B Lambda Nmax))
    have hsum := hbase.add hmixPoint
    have hcorrmem' :
        ((Lambda.mul (sPoint cp)).add
          ((sOne.sub Lambda).mul (sPoint cm))).Contains
            ((lambda : ℝ) * cp + (1 - (lambda : ℝ)) * cm) := by
      simpa only [Rat.cast_one] using hcorrmem
    exact hsum.sub hcorrmem'
  exact hscalar.trans hsurrogate.2

end StrengthenedCurvature
end SortingAdversary
