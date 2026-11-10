import SortingAdversary.Continuous.Weights
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Lex

/-!
# A finite common tree law from the geometric child weights

For counting a finite transcript we may sample from the complete tree over the
finite set of anchors used so far, truncated at the maximum occupied depth.
At every nonterminal node the draw stops with the unused child mass; at the
last level it stops with probability one. Extra unused nodes cause no problem.
The distribution is normalized by recursion and each occupied path gets at
least the prescribed stopping mass times its product of child weights.
-/

namespace SortingAdversary.Continuous.FiniteTreeLaw

open MeasureTheory
open scoped BigOperators

variable {C : Type}

/-- All paths of length at most `depth` over the finite anchor alphabet. -/
@[reducible] def Node (C : Type) : ℕ → Type
  | 0 => Unit
  | depth + 1 => Option (C × Node C depth)

instance [Fintype C] (depth : ℕ) : Fintype (Node C depth) := by
  induction depth with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ depth ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Option (C × Node C depth)))

instance (depth : ℕ) : MeasurableSpace (Node C depth) := ⊤

instance (depth : ℕ) : MeasurableSingletonClass (Node C depth) := ⟨fun _ => trivial⟩

def path : {depth : ℕ} → Node C depth → List C
  | 0, _ => []
  | _ + 1, none => []
  | _ + 1, some (c, p) => c :: path p

theorem path_injective (depth : ℕ) : Function.Injective (@path C depth) := by
  induction depth with
  | zero => intro x y _; exact Subsingleton.elim (α := Unit) x y
  | succ depth ih =>
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => simp [path] at h
    | some x =>
      cases y with
      | none => simp [path] at h
      | some y =>
        obtain ⟨hc, hp⟩ := List.cons.inj h
        exact congrArg some (Prod.ext hc (ih hp))

def ofList : (depth : ℕ) → (p : List C) → p.length ≤ depth → Node C depth
  | 0, [], _ => ()
  | 0, _ :: _, h => False.elim (Nat.not_succ_le_zero _ h)
  | depth + 1, [], _ => none
  | depth + 1, c :: p, h => some (c, ofList depth p (Nat.le_of_succ_le_succ h))

theorem path_ofList (depth : ℕ) (p : List C) (hp : p.length ≤ depth) :
    path (ofList depth p hp) = p := by
  induction depth generalizing p with
  | zero =>
    cases p with
    | nil => rfl
    | cons a p => simp only [List.length_cons] at hp; omega
  | succ depth ih => cases p <;> simp [ofList, path, ih]

def pathEmbedding (anchor : C ↪ ℝ) (depth : ℕ) : Node C depth ↪ List ℝ where
  toFun p := (path p).map anchor
  inj' := fun _ _ h => path_injective depth ((List.map_injective_iff.mpr anchor.injective) h)

variable [Fintype C]

noncomputable def mass (w : C → ℝ) : (depth : ℕ) → Node C depth → ℝ
  | 0, _ => 1
  | _ + 1, none => 1 - ∑ c, w c
  | depth + 1, some (c, p) => w c * mass w depth p

theorem mass_sum (w : C → ℝ) (depth : ℕ) : ∑ p, mass w depth p = 1 := by
  induction depth with
  | zero =>
    change (∑ _ : Unit, (1 : ℝ)) = 1
    simp
  | succ depth ih =>
    change (∑ p : Option (C × Node C depth), mass w (depth + 1) p) = 1
    rw [Fintype.sum_option]
    simp only [mass, Fintype.sum_prod_type, ← Finset.mul_sum, ih, mul_one]
    ring

theorem mass_nonneg (w : C → ℝ) (hw : ∀ c, 0 ≤ w c) (htotal : ∑ c, w c ≤ 1)
    (depth : ℕ) (p : Node C depth) : 0 ≤ mass w depth p := by
  induction depth with
  | zero => exact zero_le_one
  | succ depth ih =>
    cases p with
    | none => exact sub_nonneg.mpr htotal
    | some p => exact mul_nonneg (hw p.1) (ih p.2)

/-- The finite law pays at least one stopping factor and every path weight.
At the truncation level, forced stopping only increases this lower bound. -/
theorem mass_lower (w : C → ℝ) (hw : ∀ c, 0 ≤ w c)
    (stop : ℝ) (hstop : stop ≤ 1 - ∑ c, w c) (depth : ℕ) (p : Node C depth) :
    stop * ((path p).map w).prod ≤ mass w depth p := by
  have hstop_one : stop ≤ 1 := hstop.trans (sub_le_self _ (Finset.sum_nonneg (fun c _ => hw c)))
  induction depth with
  | zero => simpa [path, mass] using hstop_one
  | succ depth ih =>
    cases p with
    | none => simpa [path, mass] using hstop
    | some p =>
      have hm := mul_le_mul_of_nonneg_left (ih p.2) (hw p.1)
      simpa only [path, List.map_cons, List.prod_cons, mass, mul_left_comm] using hm

/-- An explicit finite sum of weighted point masses, not an assumed law. -/
noncomputable def nodeLaw (w : C → ℝ) (depth : ℕ) : Measure (Node C depth) :=
  ∑ p, ENNReal.ofReal (mass w depth p) • Measure.dirac p

theorem nodeLaw_probability (w : C → ℝ) (hw : ∀ c, 0 ≤ w c)
    (htotal : ∑ c, w c ≤ 1) (depth : ℕ) : IsProbabilityMeasure (nodeLaw w depth) := by
  constructor
  simp only [nodeLaw, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => mass_nonneg w hw htotal depth p),
    mass_sum]
  exact ENNReal.ofReal_one

theorem nodeLaw_singleton (w : C → ℝ) (hw : ∀ c, 0 ≤ w c)
    (htotal : ∑ c, w c ≤ 1) (depth : ℕ) (p : Node C depth) :
    (nodeLaw w depth).real {p} = mass w depth p := by
  classical
  simp [nodeLaw, measureReal_def, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply, Set.indicator_apply, mass_nonneg w hw htotal depth p]

end SortingAdversary.Continuous.FiniteTreeLaw
