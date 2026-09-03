import SortingAdversary.StrengthenedCurvature.StrengthenedInterval
import Lean.Elab.Tactic.Decide

/-!
# Kernel-checked finite certificate for `K = 347/50`

The certificate data supply only rational subdivision boxes and rational
`lambda` witnesses.  This checker independently recomputes every interval
bound with exact rational arithmetic.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open RationalInterval

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def strengthenedK : ℚ := 347 / 50

def StrengthenedCellWellFormed (terms : ℕ) (i : Fin 22)
    (D R : SRI) (lambda : ℚ) : Prop :=
  EnvelopeWellFormed terms i D R lambda ∧
    PositiveSavingWellFormed (scheduleAI i D) R ∧
    NegativeSavingWellFormed (scheduleBI i D) R

local instance crossClosedWellFormedDecidable (Ell P N L : SRI) :
    Decidable (CrossClosedWellFormed Ell P N L) := by
  unfold CrossClosedWellFormed
  infer_instance

local instance crossSavingWellFormedDecidable (ell r₀ : ℚ) :
    Decidable (CrossSavingWellFormed ell r₀) := by
  unfold CrossSavingWellFormed SqrtCertificate
  infer_instance

local instance constantSavingWellFormedDecidable (r₁ : ℚ) :
    Decidable (ConstantSavingWellFormed r₁) := by
  unfold ConstantSavingWellFormed SqrtCertificate
  infer_instance

local instance positiveSavingWellFormedDecidable (A R : SRI) :
    Decidable (PositiveSavingWellFormed A R) := by
  unfold PositiveSavingWellFormed
  infer_instance

local instance negativeSavingWellFormedDecidable (B R : SRI) :
    Decidable (NegativeSavingWellFormed B R) := by
  unfold NegativeSavingWellFormed
  infer_instance

local instance envelopeWellFormedDecidable (terms : ℕ) (i : Fin 22)
    (D R : SRI) (lambda : ℚ) :
    Decidable (EnvelopeWellFormed terms i D R lambda) := by
  unfold EnvelopeWellFormed SqrtCertificate
  infer_instance

def strengthenedCellWellFormedDecidable (terms : ℕ) (i : Fin 22)
    (D R : SRI) (lambda : ℚ) :
    Decidable (StrengthenedCellWellFormed terms i D R lambda) := by
  unfold StrengthenedCellWellFormed
  infer_instance

def strengthenedCellUpper (terms : ℕ) (i : Fin 22)
    (D R : SRI) (lambda : ℚ) : ℚ :=
  let A := scheduleAI i D
  let B := scheduleBI i D
  let Pmax := sqrtPointI 44 R.upper
  let Nmax := sqrtPointI 44 (1 - R.lower)
  (envelopeUpperI terms D A B (sPoint lambda) Pmax Nmax R
    (positiveSavingLower terms A R)
    (negativeSavingLower terms B R)).upper

def strengthenedCellPass (terms : ℕ) (i : Fin 22)
    (D R : SRI) (lambda : ℚ) : Bool :=
  @decide (StrengthenedCellWellFormed terms i D R lambda)
      (strengthenedCellWellFormedDecidable terms i D R lambda) &&
    decide (strengthenedCellUpper terms i D R lambda <
      logRationalLower terms strengthenedK)

theorem strengthenedCellPass_sound {terms : ℕ} {i : Fin 22}
    {D R : SRI} {lambda : ℚ}
    (hpass : strengthenedCellPass terms i D R lambda = true)
    {delta r : ℝ} (hD : D.Contains delta) (hR : R.Contains r) :
    scalarEnvelope delta r (scheduleA i delta) (scheduleB i delta) lambda <
      Real.log (strengthenedK : ℝ) := by
  have hp : StrengthenedCellWellFormed terms i D R lambda ∧
      strengthenedCellUpper terms i D R lambda <
        logRationalLower terms strengthenedK := by
    simpa only [strengthenedCellPass, Bool.and_eq_true, decide_eq_true_eq] using hpass
  have hbound := envelopeUpperI_sound terms i hp.1.1 hp.1.2.1 hp.1.2.2 hD hR
  have hrat : (strengthenedCellUpper terms i D R lambda : ℝ) <
      (logRationalLower terms strengthenedK : ℝ) := by
    exact_mod_cast hp.2
  have hlog := log_rational_mem_pos terms strengthenedK (by
    norm_num [strengthenedK])
  exact hbound.trans_lt (hrat.trans_le hlog.1)

theorem strengthenedCellPass_wellFormed {terms : ℕ} {i : Fin 22}
    {D R : SRI} {lambda : ℚ}
    (hpass : strengthenedCellPass terms i D R lambda = true) :
    StrengthenedCellWellFormed terms i D R lambda := by
  have hp :
      @decide (StrengthenedCellWellFormed terms i D R lambda)
          (strengthenedCellWellFormedDecidable terms i D R lambda) = true ∧
        decide (strengthenedCellUpper terms i D R lambda <
          logRationalLower terms strengthenedK) = true := by
    simpa only [strengthenedCellPass, Bool.and_eq_true] using hpass
  letI := strengthenedCellWellFormedDecidable terms i D R lambda
  exact of_decide_eq_true hp.1

/-- A leaf stores the numerator of its exact `lambda / 10^12` witness. -/
inductive StrengthenedCertificateTree where
  | leaf (lambdaNumerator : ℕ)
  | split (lowerLower lowerUpper upperLower upperUpper : StrengthenedCertificateTree)
  deriving Repr

def boxMidpoint (I : SRI) : ℚ := (I.lower + I.upper) / 2
def boxLower (I : SRI) : SRI := ⟨I.lower, boxMidpoint I⟩
def boxUpper (I : SRI) : SRI := ⟨boxMidpoint I, I.upper⟩

def allFour (a b c d : Bool) : Bool := a && b && c && d

def checkStrengthenedTree (terms : ℕ) (i : Fin 22) :
    StrengthenedCertificateTree → SRI → SRI → Bool
  | .leaf numerator, D, R =>
      strengthenedCellPass terms i D R (numerator / 1000000000000)
  | .split t₀₀ t₀₁ t₁₀ t₁₁, D, R =>
      allFour
        (checkStrengthenedTree terms i t₀₀ (boxLower D) (boxLower R))
        (checkStrengthenedTree terms i t₀₁ (boxLower D) (boxUpper R))
        (checkStrengthenedTree terms i t₁₀ (boxUpper D) (boxLower R))
        (checkStrengthenedTree terms i t₁₁ (boxUpper D) (boxUpper R))

def StrengthenedCellConclusion (i : Fin 22) (delta r : ℝ) : Prop :=
  ∃ lambda : ℚ,
    0 < scheduleA i delta ∧ scheduleA i delta < 1 ∧
    0 < scheduleB i delta ∧ scheduleB i delta < 1 ∧
    delta < scheduleB i delta ∧
    0 ≤ lambda ∧ lambda ≤ 1 ∧
    scalarEnvelope delta r (scheduleA i delta) (scheduleB i delta) lambda <
      Real.log (strengthenedK : ℝ)

private theorem leafConclusion {terms : ℕ} {i : Fin 22}
    {D R : SRI} {lambda : ℚ}
    (hpass : strengthenedCellPass terms i D R lambda = true)
    {delta r : ℝ} (hD : D.Contains delta) (hR : R.Contains r) :
    StrengthenedCellConclusion i delta r := by
  have hw := strengthenedCellPass_wellFormed hpass
  have henv := hw.1
  rcases henv with ⟨hgap, _, _, _, _, hA0, hA1, hB0, hB1, hcross,
    hl0, hl1, _⟩
  have hA := scheduleAI_contains hD hgap
  have hB := scheduleBI_contains hD hgap
  have ha0 : 0 < scheduleA i delta :=
    (Rat.cast_pos.mpr hA0).trans_le hA.1
  have ha1 : scheduleA i delta < 1 := by
    have hu : ((scheduleAI i D).upper : ℝ) < 1 := by
      have h : ((scheduleAI i D).upper : ℝ) < (((1 : ℚ) : ℝ)) :=
        Rat.cast_lt.mpr hA1
      norm_num at h ⊢
      exact h
    exact hA.2.trans_lt hu
  have hb0 : 0 < scheduleB i delta :=
    (Rat.cast_pos.mpr hB0).trans_le hB.1
  have hb1 : scheduleB i delta < 1 := by
    have hu : ((scheduleBI i D).upper : ℝ) < 1 := by
      have h : ((scheduleBI i D).upper : ℝ) < (((1 : ℚ) : ℝ)) :=
        Rat.cast_lt.mpr hB1
      norm_num at h ⊢
      exact h
    exact hB.2.trans_lt hu
  have hdeltaB : delta < scheduleB i delta := by
    have hDB : (D.upper : ℝ) < ((scheduleBI i D).lower : ℝ) :=
      Rat.cast_lt.mpr hcross
    exact hD.2.trans_lt (hDB.trans_le hB.1)
  exact ⟨lambda, ha0, ha1, hb0, hb1, hdeltaB,
    hl0, hl1,
    strengthenedCellPass_sound hpass hD hR⟩

private theorem boxLower_contains {I : SRI} {x : ℝ}
    (hx : I.Contains x) (hxm : x ≤ (boxMidpoint I : ℚ)) :
    (boxLower I).Contains x := ⟨hx.1, hxm⟩

private theorem boxUpper_contains {I : SRI} {x : ℝ}
    (hx : I.Contains x) (hmx : (boxMidpoint I : ℚ) ≤ x) :
    (boxUpper I).Contains x := ⟨hmx, hx.2⟩

theorem checkStrengthenedTree_sound {terms : ℕ} {i : Fin 22}
    {tree : StrengthenedCertificateTree} {D R : SRI}
    (hcheck : checkStrengthenedTree terms i tree D R = true)
    {delta r : ℝ} (hD : D.Contains delta) (hR : R.Contains r) :
    StrengthenedCellConclusion i delta r := by
  induction tree generalizing D R with
  | leaf numerator =>
      exact leafConclusion hcheck hD hR
  | split t₀₀ t₀₁ t₁₀ t₁₁ ih₀₀ ih₀₁ ih₁₀ ih₁₁ =>
      have hc :
          ((checkStrengthenedTree terms i t₀₀ (boxLower D) (boxLower R) = true ∧
            checkStrengthenedTree terms i t₀₁ (boxLower D) (boxUpper R) = true) ∧
            checkStrengthenedTree terms i t₁₀ (boxUpper D) (boxLower R) = true) ∧
            checkStrengthenedTree terms i t₁₁ (boxUpper D) (boxUpper R) = true := by
        simpa only [checkStrengthenedTree, allFour, Bool.and_eq_true] using hcheck
      by_cases hd : delta ≤ (boxMidpoint D : ℚ)
      · have hDl := boxLower_contains hD hd
        by_cases hr : r ≤ (boxMidpoint R : ℚ)
        · exact ih₀₀ hc.1.1.1 hDl (boxLower_contains hR hr)
        · exact ih₀₁ hc.1.1.2 hDl
            (boxUpper_contains hR (le_of_not_ge hr))
      · have hDu := boxUpper_contains hD (le_of_not_ge hd)
        by_cases hr : r ≤ (boxMidpoint R : ℚ)
        · exact ih₁₀ hc.1.2 hDu (boxLower_contains hR hr)
        · exact ih₁₁ hc.2 hDu
            (boxUpper_contains hR (le_of_not_ge hr))

end StrengthenedCurvature
end SortingAdversary
