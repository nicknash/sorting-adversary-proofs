import SortingAdversary.Continuous.ControllerInvariant
import SortingAdversary.Continuous.Sampling
import SortingAdversary.Optimal.PrimitiveWork

/-!
# Freezing a sparse order-restriction tree

A frozen comparison inspects the routing of its two labels. At a node a free
label is placed immediately to the right of its lower wall. Equal lower walls
are ordered by predecessor height and then label. The perturbations used to
realize this order exist only in the proof. The comparator does not compute
them, sort all labels, or read the transcript.
-/

namespace SortingAdversary.Continuous.PolylogFreeze

open FiniteAveraging TreeState OrderRegion Controller
open SortingAdversary.Optimal.PrimitiveWork (Result)

variable {n : ℕ}

/-- Compute a maximum over the *stored* incoming adjacency list. The empty
list has height zero; one arc adds one to its predecessor's height. -/
private def predecessorsMax (f : Fin n → Result ℕ) : List (Fin n) → Result ℕ
  | [] => ⟨0, 1⟩
  | u :: us =>
    let head := f u
    let tail := predecessorsMax f us
    ⟨max (head.value + 1) tail.value, head.work + tail.work + 4⟩

/-- Height in edges, searched only in the predecessor cone. The caller supplies
the stored incoming lists; a lookup of the list head is charged one access. -/
def height (parents : Fin n → List (Fin n)) : ℕ → Fin n → Result ℕ
  | 0, _ => ⟨0, 1⟩
  | h + 1, x =>
    let hs := predecessorsMax (height parents h) (parents x)
    ⟨hs.value, hs.work + 1⟩

private theorem predecessorsMax_le_work (f : Fin n → Result ℕ) (xs : List (Fin n)) (B : ℕ)
    (hb : ∀ u ∈ xs, (f u).work ≤ B) :
    (predecessorsMax f xs).work ≤ xs.length * (B + 4) + 1 := by
  induction xs with
  | nil => simp [predecessorsMax]
  | cons u us ih =>
    have hu := hb u (by simp)
    have ht := ih fun v hv => hb v (by simp [hv])
    simp only [predecessorsMax, List.length_cons, Nat.add_mul, one_mul]
    omega

/-- Finite cost independent of the ambient label count. -/
def heightBudget (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | h + 1 => d * (heightBudget d h + 4) + 2

theorem height_work_le (parents : Fin n → List (Fin n)) (d : ℕ)
    (hd : ∀ x, (parents x).length ≤ d) (h : ℕ) (x : Fin n) :
    (height parents h x).work ≤ heightBudget d h := by
  induction h generalizing x with
  | zero => rfl
  | succ h ih =>
    have hb := predecessorsMax_le_work (height parents h) (parents x) (heightBudget d h)
      (fun u _ => ih u)
    have hm := Nat.mul_le_mul_right (heightBudget d h + 4) (hd x)
    simp only [height, heightBudget]
    omega

private theorem predecessorsMax_congr (f g : Fin n → Result ℕ) (xs : List (Fin n))
    (h : ∀ u ∈ xs, (f u).value = (g u).value) :
    (predecessorsMax f xs).value = (predecessorsMax g xs).value := by
  induction xs with
  | nil => rfl
  | cons u us ih =>
    simp only [predecessorsMax, h u (by simp), ih (fun v hv => h v (by simp [hv]))]

private theorem predecessorsMax_ge (f : Fin n → Result ℕ) (xs : List (Fin n)) (x : Fin n)
    (hx : x ∈ xs) : (f x).value < (predecessorsMax f xs).value := by
  induction xs with
  | nil => simp at hx
  | cons u us ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)
    · exact (ih hx).trans_le (le_max_right _ _)

private theorem predecessorsMax_le (f : Fin n → Result ℕ) (xs : List (Fin n)) (B : ℕ)
    (hb : ∀ x ∈ xs, (f x).value < B) : (predecessorsMax f xs).value ≤ B := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    exact max_le (hb x (by simp)) (ih (fun y hy => hb y (by simp [hy])))

/-- Heights are independent of predecessor order and repetitions. In
particular, an adjacency list can replace a filter of the full label set. -/
theorem height_ext (a b : Fin n → List (Fin n))
    (mem : ∀ x y, y ∈ a x ↔ y ∈ b x) (h : ℕ) (x : Fin n) :
    (height a h x).value = (height b h x).value := by
  induction h generalizing x with
  | zero => rfl
  | succ h ih =>
    apply le_antisymm
    · apply predecessorsMax_le
      intro y hy
      rw [ih]
      exact predecessorsMax_ge _ _ _ ((mem x y).mp hy)
    · apply predecessorsMax_le
      intro y hy
      rw [← ih]
      exact predecessorsMax_ge _ _ _ ((mem x y).mpr hy)

private theorem height_stable (parents : Fin n → List (Fin n)) (r : Fin n → ℕ)
    (hr : ∀ x y, x ∈ parents y → r x < r y) (h : ℕ) (x : Fin n) (hx : r x ≤ h) :
    (height parents (h + 1) x).value = (height parents h x).value := by
  induction h generalizing x with
  | zero =>
    have he : parents x = [] := List.eq_nil_iff_forall_not_mem.mpr fun u hu => by
      have := hr u x hu
      omega
    simp [height, he, predecessorsMax]
  | succ h ih =>
    apply predecessorsMax_congr
    intro u hu
    exact ih u (by have := hr u x hu; omega)

/-- Once the search limit exceeds a strict topological rank, local height
strictly increases along every arc. No topological rank is computed by this
routine. -/
theorem height_strict (parents : Fin n → List (Fin n)) (r : Fin n → ℕ)
    (hr : ∀ x y, x ∈ parents y → r x < r y) (H : ℕ) (hH : ∀ x, r x < H)
    (x y : Fin n) (hxy : x ∈ parents y) :
    (height parents H x).value < (height parents H y).value := by
  cases H with
  | zero => exact (Nat.not_lt_zero _ (hH x)).elim
  | succ H =>
    rw [height_stable parents r hr H x (Nat.le_of_lt_succ (hH x))]
    exact predecessorsMax_ge _ _ _ hxy

/-- Unique integer tie-breaker, lexicographic in (height, label). -/
def tie (depth : Fin n → ℕ) (x : Fin n) : ℕ := depth x * n + x.val

private theorem tie_injective (depth : Fin n → ℕ) : Function.Injective (tie depth) := by
  intro x y h
  have hm := congrArg (· % n) h
  exact Fin.ext (by simpa [tie, Nat.add_mod, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] using hm)

private theorem tie_strict (depth : Fin n → ℕ) {x y : Fin n} (h : depth x < depth y) :
    tie depth x < tie depth y := by
  calc
    _ < depth x * n + n := Nat.add_lt_add_left x.isLt _
    _ = (depth x + 1) * n := by simp [Nat.add_mul]
    _ ≤ depth y * n := Nat.mul_le_mul_right _ h
    _ ≤ _ := Nat.le_add_right _ _

/-- The four cases after routing to the lowest common ancestor. Equality
between a child anchor and a lower wall puts the child first. -/
def answerAt (r : Routing ℚ) (tree : State n ℚ) (depth : Fin n → ℕ) (q : Query n) : Answer :=
  let l := tree.system.lower q.left
  let m := tree.system.lower q.right
  match r with
  | .coordinates =>
    if l < m ∨ l = m ∧ tie depth q.left < tie depth q.right then .less else .greater
  | .leftFree c => if l < c then .less else .greater
  | .rightFree c => if c ≤ m then .less else .greater
  | .anchors c d => if c < d then .less else .greater

def answer (tree : State n ℚ) (depth : Fin n → ℕ) (q : Query n) : Answer :=
  answerAt (route (tree.location q.left) (tree.location q.right)) tree depth q

/- The proof interprets the finitely many infinitesimal keys by ordinary
rationals. The cap is the first larger breakpoint, or one unit of space if
no nearer breakpoint occurs. -/
private def cap (b : ℚ) : List ℚ → ℚ
  | [] => b + 1
  | c :: cs => if b < c then min c (cap b cs) else cap b cs

private theorem lt_cap (b : ℚ) (cs : List ℚ) : b < cap b cs := by
  induction cs with
  | nil => simp [cap]
  | cons c cs ih => by_cases h : b < c <;> simp [cap, h, ih]

private theorem cap_le (b c : ℚ) (cs : List ℚ) (hc : c ∈ cs) (h : b < c) : cap b cs ≤ c := by
  induction cs with
  | nil => simp at hc
  | cons v vs ih =>
    rcases List.mem_cons.mp hc with rfl | hc
    · simp [cap, h]
    · by_cases hv : b < v
      · simpa only [cap, if_pos hv] using (min_le_right v (cap b vs)).trans (ih hc)
      · simpa [cap, hv] using ih hc

private def perturb (cs : List ℚ) (b : ℚ) : ℕ → ℚ
  | 0 => (b + cap b cs) / 2
  | i + 1 => (perturb cs b i + cap b cs) / 2

private theorem perturb_bounds (cs : List ℚ) (b : ℚ) (i : ℕ) :
    b < perturb cs b i ∧ perturb cs b i < cap b cs := by
  have hc := lt_cap b cs
  induction i with
  | zero => dsimp [perturb]; constructor <;> linarith
  | succ i ih => dsimp only [perturb]; constructor <;> linarith [ih.1, ih.2]

private theorem perturb_mono (cs : List ℚ) (b : ℚ) : StrictMono (perturb cs b) := by
  apply strictMono_nat_of_lt_succ
  intro i
  dsimp only [perturb]
  linarith [(perturb_bounds cs b i).2]

private def walls (s : State n ℚ) : List ℚ :=
  (List.finRange n).flatMap fun x => s.system.lower x :: s.system.upper x :: s.location x

private theorem lower_mem (s : State n ℚ) (x : Fin n) : s.system.lower x ∈ walls s :=
  List.mem_flatMap.mpr ⟨x, List.mem_finRange x, by simp⟩

private theorem upper_mem (s : State n ℚ) (x : Fin n) : s.system.upper x ∈ walls s :=
  List.mem_flatMap.mpr ⟨x, List.mem_finRange x, by simp⟩

private theorem anchor_mem (s : State n ℚ) (x : Fin n) {c : ℚ} (h : c ∈ s.location x) :
    c ∈ walls s := List.mem_flatMap.mpr ⟨x, List.mem_finRange x, by simp [h]⟩

private def realized (s : State n ℚ) (depth : Fin n → ℕ) (x : Fin n) : ℚ :=
  perturb (walls s) (s.system.lower x) (tie depth x)

private theorem above (s : State n ℚ) (depth : Fin n → ℕ) (x : Fin n) :
    s.system.lower x < realized s depth x := (perturb_bounds ..).1

private theorem below (s : State n ℚ) (depth : Fin n → ℕ) (x : Fin n) {c : ℚ}
    (hc : c ∈ walls s) (hlt : s.system.lower x < c) : realized s depth x < c :=
  (perturb_bounds ..).2.trans_le (cap_le _ _ _ hc hlt)

private theorem values_lt (s : State n ℚ) (depth : Fin n → ℕ) (x y : Fin n) :
    realized s depth x < realized s depth y ↔
      s.system.lower x < s.system.lower y ∨
        s.system.lower x = s.system.lower y ∧ tie depth x < tie depth y := by
  rcases lt_trichotomy (s.system.lower x) (s.system.lower y) with h | h | h
  · exact iff_of_true ((below s depth x (lower_mem s y) h).trans (above s depth y)) (Or.inl h)
  · simp [realized, h, (perturb_mono (walls s) (s.system.lower y)).lt_iff_lt]
  · have hrev := (below s depth y (lower_mem s x) h).trans (above s depth x)
    simp [not_lt.mpr hrev.le, not_lt.mpr h.le, h.ne.symm]

private theorem values_injective (s : State n ℚ) (depth : Fin n → ℕ) :
    Function.Injective (realized s depth) := by
  intro x y he
  by_contra hne
  have ht := (tie_injective depth).ne hne
  rcases lt_trichotomy (s.system.lower x) (s.system.lower y) with hl | hl | hl
  · exact ((values_lt ..).mpr (Or.inl hl)).ne he
  · rcases lt_or_gt_of_ne ht with h | h
    · exact ((values_lt ..).mpr (Or.inr ⟨hl,h⟩)).ne he
    · exact ((values_lt ..).mpr (Or.inr ⟨hl.symm,h⟩)).ne he.symm
  · exact ((values_lt ..).mpr (Or.inl hl)).ne he.symm

private def routeWalls (cs : List ℚ) : Routing ℚ → Prop
  | .leftFree c | .rightFree c => c ∈ cs
  | _ => True

private theorem route_walls (cs p q : List ℚ) (hp : ∀ c ∈ p, c ∈ cs)
    (hq : ∀ c ∈ q, c ∈ cs) : routeWalls cs (route p q) := by
  induction p generalizing q with
  | nil => cases q with
    | nil => trivial
    | cons c qs => exact hq c (by simp)
  | cons c ps ih => cases q with
    | nil => exact hp c (by simp)
    | cons d qs =>
      by_cases h : c = d
      · subst d
        simpa [route] using ih qs (fun v hv => hp v (by simp [hv])) (fun v hv => hq v (by simp [hv]))
      · simp [route, h, routeWalls]

private theorem answer_holds (s : State n ℚ) (depth : Fin n → ℕ) (q : Query n) :
    s.toReal.Holds (fun x => (realized s depth x : ℝ)) ⟨q, answer s depth q⟩ := by
  let x := q.left
  let y := q.right
  let a := realized s depth x
  let b := realized s depth y
  let r := route (s.location x) (s.location y)
  have hw : routeWalls (walls s) r :=
    route_walls _ _ _ (fun _ => anchor_mem s x) (fun _ => anchor_mem s y)
  have hr : r.toReal.Holds (a : ℝ) (b : ℝ) (answerAt r s depth q) := by
    cases e : r with
    | coordinates =>
      change (Routing.coordinates : Routing ℝ).Holds _ _ (if _ then _ else _)
      split
      · rename_i ht
        exact (Rat.cast_lt (K := ℝ)).mpr ((values_lt s depth x y).mpr ht)
      · rename_i ht
        have hn := mt (values_lt s depth x y).mp ht
        have ne := (values_injective s depth).ne q.distinct
        exact (Rat.cast_lt (K := ℝ)).mpr (lt_of_le_of_ne (le_of_not_gt hn) ne.symm)
    | leftFree c =>
      rw [e] at hw
      change (Routing.leftFree (c : ℝ)).Holds _ _ (if _ then _ else _)
      split
      · rename_i h
        exact (Rat.cast_lt (K := ℝ)).mpr (below s depth x hw h)
      · rename_i h
        exact (Rat.cast_lt (K := ℝ)).mpr ((le_of_not_gt h).trans_lt (above s depth x))
    | rightFree c =>
      rw [e] at hw
      change (Routing.rightFree (c : ℝ)).Holds _ _ (if _ then _ else _)
      split
      · rename_i h
        exact (Rat.cast_lt (K := ℝ)).mpr (h.trans_lt (above s depth y))
      · rename_i h
        exact (Rat.cast_lt (K := ℝ)).mpr (below s depth y hw (lt_of_not_ge h))
    | anchors c d =>
      change (Routing.anchors (c : ℝ) (d : ℝ)).Holds _ _ (if _ then _ else _)
      split
      · exact (Rat.cast_lt (K := ℝ)).mpr ‹c < d›
      · have hn := route_anchors_distinct _ _ e
        exact (Rat.cast_lt (K := ℝ)).mpr (lt_of_le_of_ne (le_of_not_gt ‹¬ c < d›) hn.symm)
  have er : route (s.toReal.location x) (s.toReal.location y) = r.toReal :=
    route_toReal _ _
  rw [← er] at hr
  change s.toReal.Holds _ ⟨q, answerAt r s depth q⟩
  cases e : answerAt r s depth q with
  | less => rw [e] at hr; exact route_less_sound _ _ _ _ hr
  | greater => rw [e] at hr; exact route_greater_sound _ _ _ _ hr

/-- The same ranking witnesses the old transcript and *all* future frozen
queries. Only the two queried labels' heights are needed at equal lower walls. -/
theorem frozen_ranking (M : Memory n) (geo : Geometric M) (depth : Fin n → ℕ)
    (hd : ∀ x y, M.tree.system.edge x y = true → depth x < depth y) :
    ∃ π : Ranking n, Compatible π M.history ∧ ∀ q, answer M.tree depth q = q.outcome π := by
  let X (x : Fin n) : ℝ := (realized M.tree depth x : ℝ)
  have hf : M.tree.toReal.system.StrictlyFeasible X := by
    constructor
    · intro x
      exact ⟨(Rat.cast_lt (K := ℝ)).mpr (above _ _ _),
        (Rat.cast_lt (K := ℝ)).mpr (below _ _ _ (upper_mem _ _) (geo.widths x))⟩
    · intro x y he
      have hm : M.tree.system.lower x ≤ M.tree.system.lower y :=
        (Rat.cast_le (K := ℝ)).mp (geo.normalized x y he).1
      apply (Rat.cast_lt (K := ℝ)).mpr
      apply (values_lt _ _ _ _).mpr
      exact hm.lt_or_eq.imp_right fun h => ⟨h, tie_strict _ (hd x y he)⟩
  have inj : Function.Injective (M.tree.toReal.position X) := by
    intro x y h
    have he := (List.concat_inj.mp (by simpa only [State.position, List.concat_eq_append] using h)).2
    exact values_injective _ _ ((Rat.cast_inj (α := ℝ)).mp he)
  obtain ⟨π, hp⟩ := exists_orderCell _ inj
  have obs (o : Observation n) (h : M.tree.toReal.Holds X o) : o.Holds π := by
    cases e : o.answer with
    | less =>
      simp only [Observation.Holds, e]
      exact (hp _ _).mpr (by simpa [State.Holds, e] using h)
    | greater =>
      simp only [Observation.Holds, e]
      exact (hp _ _).mpr (by simpa [State.Holds, e] using h)
  refine ⟨π, List.forall_iff_forall_mem.mpr (fun o ho => obs o (geo.consistent X hf o ho)), ?_⟩
  intro q
  have ho := obs _ (answer_holds M.tree depth q)
  cases e : answer M.tree depth q with
  | less =>
    have h : π q.left < π q.right := by simpa [Observation.Holds, e] using ho
    simp [Query.outcome, h]
  | greater =>
    have h : π q.right < π q.left := by simpa [Observation.Holds, e] using ho
    simp [Query.outcome, not_lt.mpr h.le]

/-- Instantiate the comparator with bounded predecessor searches on an actual
ready controller state. The rank supplied by positivity and height is used
only in the proof of stabilization. -/
theorem ready_frozen_ranking (M : Memory n) (k : ℕ) (ready : Ready k M)
    (parents : Fin n → List (Fin n))
    (hp : ∀ x y, x ∈ parents y ↔ M.tree.system.edge x y = true) :
    ∃ π : Ranking n, Compatible π M.history ∧
      ∀ q, answer M.tree (fun x => (height parents (2^k) x).value) q = q.outcome π := by
  obtain ⟨r, hr, hH⟩ := short_rank_of_height M.tree.system.toReal ready.positive (2^k) ready.height
  apply frozen_ranking M ready.toGeometric
  intro x y hxy
  exact height_strict parents r (fun a b hab => hr a b ((hp a b).mp hab)) _
    (fun a => (Nat.lt_succ_self _).trans (hH a)) x y ((hp x y).mpr hxy)

end SortingAdversary.Continuous.PolylogFreeze
