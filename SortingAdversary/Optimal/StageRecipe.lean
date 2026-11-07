import SortingAdversary.Optimal.StageParameters
import SortingAdversary.Optimal.CappedStageScan

/-!
# The fixed arithmetic recipe for an actual adversary stage

The syntax below is independent of the input size and the stage index.
Every varying scalar is obtained by evaluating it with the capped arithmetic
interpreter. A successful whole-recipe test certifies every field and every
intermediate used to construct the actual normalization parameters.
-/

namespace SortingAdversary.Optimal.StageRecipe

open CappedArithmetic StageParameters

private def nat (n : ℕ) : Expr := .lit n
private def add (a b : Expr) : Expr := .add a b
private def mul (a b : Expr) : Expr := .mul a b
private def pow (a b : Expr) : Expr := .pow a b
private def maximum (a b : Expr) : Expr := .maximum a b

def degree : Expr := add .input (nat 4)
def pathLength : Expr := pow (nat 2) .input
def height : Expr := mul (nat 2) pathLength
def degreeCap : Expr := add degree (nat 1)
def comparables : Expr := pow (add degreeCap (nat 1)) (add height (nat 1))
def insertion : Expr := mul (nat 2) (pow (nat 4) comparables)
def accuracyDen : Expr := mul (nat 100) .input
def edgeRatio : Expr := mul (add (mul accuracyDen (add degreeCap (nat 1))) (nat 1)) insertion
def scaleLength : Expr := pow (nat 2) (mul .input (pow (add comparables (nat 2)) (nat 2)))
def scaleBase : Expr := mul (mul (nat 128) scaleLength)
  (pow (add edgeRatio (nat 1)) (add (mul (nat 2) height) (nat 3)))
def componentRatio : Expr := pow scaleBase (add scaleLength (nat 1))
def localInsertion : Expr := mul (nat 2) (pow (nat 4) (mul (nat 2) comparables))
def moment : Expr := mul (mul (nat 8) comparables)
  (pow (mul (nat 8) (pow comparables (nat 2))) height)
def sweeps (E : Expr) : Expr := add
  (mul moment (mul (mul (mul (nat 32) componentRatio) E) localInsertion)) (mul (nat 8) E)
def widthNeed (E : Expr) : Expr := add
  (maximum (mul (mul (mul (mul (nat 32) height) (sweeps E)) E) localInsertion)
    (mul (mul (nat 4) localInsertion) E)) (nat 1)
def comparisonSweeps : Expr := sweeps accuracyDen
def cdfSweeps : Expr := sweeps (nat 16)
def comparisonWidth : Expr := widthNeed accuracyDen
def cdfWidth : Expr := widthNeed (nat 16)
def minimumWidth : Expr := maximum (nat 32) (maximum comparisonWidth cdfWidth)
def cheap : Expr := mul minimumWidth (pow (nat 4) comparables)
def comparisonBall : Expr := mul (nat 2) (pow (add degreeCap (nat 1)) (mul height comparisonSweeps))
def cdfBall : Expr := pow (add degreeCap (nat 1)) (mul height cdfSweeps)

def field : Field → Expr
  | .degree => degree
  | .pathLength => pathLength
  | .height => height
  | .degreeCap => degreeCap
  | .comparables => comparables
  | .insertion => insertion
  | .accuracyDen => accuracyDen
  | .edgeRatio => edgeRatio
  | .scaleLength => scaleLength
  | .scaleBase => scaleBase
  | .componentRatio => componentRatio
  | .localInsertion => localInsertion
  | .moment => moment
  | .comparisonSweeps => comparisonSweeps
  | .cdfSweeps => cdfSweeps
  | .comparisonWidth => comparisonWidth
  | .cdfWidth => cdfWidth
  | .minimumWidth => minimumWidth
  | .cheap => cheap
  | .cheapSquare => pow cheap (nat 2)
  | .comparisonBall => comparisonBall
  | .cdfBall => cdfBall

theorem field_value (j : ℕ) (f : Field) : (field f).value j = StageParameters.value j f := by
  cases f <;> rfl

def collect : List Expr → Expr
  | [] => .lit 1
  | e :: es => .maximum e (collect es)

theorem collect_need (j : ℕ) {e : Expr} {es : List Expr} (he : e ∈ es) :
    e.need j ≤ (collect es).need j := by
  induction es with
  | nil => simp at he
  | cons a es ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact le_max_left _ _
    · exact (ih he).trans (le_max_right _ _)

theorem collect_nodes {e : Expr} {es : List Expr} (he : e ∈ es) : e.nodes ≤ (collect es).nodes := by
  induction es with
  | nil => simp at he
  | cons a es ih =>
    rcases List.mem_cons.mp he with rfl | he
    · change e.nodes ≤ e.nodes + (collect es).nodes + 1
      omega
    · have h := ih he
      change e.nodes ≤ a.nodes + (collect es).nodes + 1
      omega

def all : Expr := collect (fields.map field)

theorem field_need_le (j : ℕ) (f : Field) : (field f).need j ≤ all.need j :=
  collect_need j (List.mem_map.mpr ⟨f, mem_fields f, rfl⟩)

theorem field_nodes_le (f : Field) : (field f).nodes ≤ all.nodes :=
  collect_nodes (List.mem_map.mpr ⟨f, mem_fields f, rfl⟩)

theorem all_literalMax : all.literalMax ≤ 128 := by decide

def evaluated (cap j : ℕ) (f : Field) : ℕ := ((field f).eval cap j).value.getD 0

theorem evaluated_eq (cap j : ℕ) (hfit : all.need j ≤ cap) (f : Field) :
    evaluated cap j f = StageParameters.value j f := by
  have h := (field f).eval_complete cap j ((field_need_le j f).trans hfit)
  rw [evaluated, h, Option.getD_some, field_value]

theorem evaluated_le (cap j : ℕ) (hfit : all.need j ≤ cap) (f : Field) : evaluated cap j f ≤ cap := by
  rw [evaluated_eq cap j hfit f, ← field_value j f]
  exact ((field f).value_le_need j).trans ((field_need_le j f).trans hfit)

structure Table where
  values : List (Field × ℕ)
  work : ℕ
  peak : ℕ
  deriving Repr

/-- Evaluate the fixed field list once, sharing its materialized results
when building the dependent controller parameter structures. -/
def materialize (cap j : ℕ) : List Field → Table
  | [] => ⟨[], 0, 0⟩
  | f :: fs =>
    let first := (field f).eval cap j
    let rest := materialize cap j fs
    ⟨(f, first.value.getD 0) :: rest.values, first.work + rest.work + 1, max first.peak rest.peak⟩

theorem materialize_values (cap j : ℕ) (fs : List Field) :
    (materialize cap j fs).values = fs.map (fun f => (f, evaluated cap j f)) := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp only [materialize, List.map_cons, ih, evaluated]

private theorem lookup_map_function {α β : Type*} [DecidableEq α]
    (f : α → β) (xs : List α) {a : α} (ha : a ∈ xs) :
    (xs.map (fun x => (x, f x))).lookup a = some (f a) := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    by_cases hax : a = x
    · subst a
      simp
    · have ham : a ∈ xs := (List.mem_cons.mp ha).resolve_left hax
      have hbeq : (a == x) = false := beq_eq_false_iff_ne.mpr hax
      simpa only [List.map_cons, List.lookup_cons, hbeq] using ih ham

def Table.get (t : Table) (f : Field) : ℕ := (t.values.lookup f).getD 0

theorem materialize_get (cap j : ℕ) (f : Field) :
    (materialize cap j fields).get f = evaluated cap j f := by
  rw [Table.get, materialize_values, lookup_map_function _ _ (mem_fields f)]
  rfl

theorem materialize_correct (cap j : ℕ) (hfit : all.need j ≤ cap) (f : Field) :
    (materialize cap j fields).get f = StageParameters.value j f := by
  rw [materialize_get, evaluated_eq cap j hfit f]

theorem materialize_work (cap j : ℕ) (fs : List Field) (hcap : 1 ≤ cap) :
    (materialize cap j fs).work ≤ fs.length * (all.nodes * (5 * (cap + 1) + 2) + 1) := by
  induction fs with
  | nil => simp [materialize]
  | cons f fs ih =>
    have hf := ((field f).eval_work cap j hcap).trans
      (Nat.mul_le_mul_right _ (field_nodes_le f))
    simp only [materialize, List.length_cons]
    nlinarith

theorem field_literalMax (f : Field) : (field f).literalMax ≤ 128 := by cases f <;> decide

theorem materialize_peak (cap j : ℕ) (fs : List Field) (hcap : 1 ≤ cap) (hj : j ≤ cap) :
    (materialize cap j fs).peak ≤ (cap + 129) ^ 2 := by
  induction fs with
  | nil => simp [materialize]
  | cons f fs ih =>
    have hf := (field f).eval_peak cap j 128 hcap hj (field_literalMax f)
    exact max_le hf ih

end SortingAdversary.Optimal.StageRecipe
