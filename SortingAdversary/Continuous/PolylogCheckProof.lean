import SortingAdversary.Continuous.PolylogPrepared
import SortingAdversary.Continuous.PolylogCompare
import SortingAdversary.Continuous.PolylogLocalBudget

/-! Refinement of an active query and a repair candidate from their stored addresses. -/

namespace SortingAdversary.Continuous.PolylogCompare

open PolylogBits PolylogAddressOrder PolylogPrepared PolylogSchedule TreeState
open Optimal.CappedArithmetic (Expr)
variable {n t b D : ℕ} {m : Memory n t b} {M : Controller.Memory n} {nodes : List (List ℕ)}

private theorem value_bound (a : blockStore.Ref b) (ha : PolylogPrefix.coordinate blockStore D a ≤ 1) :
    value blockStore b a ≤ 2^D := by
  have h := (div_le_one (by positivity : (0:ℚ) < 2^D)).1 ha
  exact_mod_cast h

private noncomputable def wallSpec (hm : m.Represents D nodes M) (geom : Controller.Geometric M) :
    WallSpec blockStore m.heap b D m.spatial.walls M.tree.system := by
  let l (x : Fin n) := (m.spatial.walls.lower.get x.val).value
  let u (x : Fin n) := (m.spatial.walls.upper.get x.val).value
  have low (x) : ∃ a : blockStore.Ref b, PolylogBits.Represents blockStore m.heap (l x) a :=
    (nonneg_iff _ _ _ _ _).1 ((geom.rationalBounds x).1.trans_eq (hm.spatial.walls.1 x).symm)
  have upp (x) : ∃ a : blockStore.Ref b, PolylogBits.Represents blockStore m.heap (u x) a :=
    (nonneg_iff _ _ _ _ _).1 (((geom.rationalBounds x).1.trans (geom.widths x).le).trans_eq
      (hm.spatial.walls.2 x).symm)
  have el (x) : PolylogPrefix.coordinate blockStore D (low x).choose = M.tree.system.lower x :=
    (decode_of_rep m.valid (low x).choose_spec).symm.trans (hm.spatial.walls.1 x)
  have eu (x) : PolylogPrefix.coordinate blockStore D (upp x).choose = M.tree.system.upper x :=
    (decode_of_rep m.valid (upp x).choose_spec).symm.trans (hm.spatial.walls.2 x)
  exact ⟨fun x => (low x).choose,fun x => (upp x).choose,fun x => (low x).choose_spec,
    fun x => (upp x).choose_spec,el,eu,fun x => ⟨value_bound _ ((el x).le.trans
      ((geom.widths x).le.trans (geom.rationalBounds x).2)), value_bound _ ((eu x).le.trans
      (geom.rationalBounds x).2)⟩⟩

private def anchorsHave (P : ℚ → Prop) : Routing ℚ → Prop
  | .coordinates => True
  | .leftFree c | .rightFree c => P c
  | .anchors c d => P c ∧ P d

private theorem anchorsHave_route (P : ℚ → Prop) (xs ys : List ℚ)
    (hx : ∀ c ∈ xs, P c) (hy : ∀ c ∈ ys, P c) : anchorsHave P (TreeState.route xs ys) := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => trivial
    | cons a as => exact hy a (by simp)
  | cons a as ih => cases ys with
    | nil => exact hx a (by simp)
    | cons b bs =>
      by_cases hab : a=b
      · simpa [route,hab] using ih bs (fun c hc => hx c (by simp [hc])) (fun c hc => hy c (by simp [hc]))
      · simpa only [route,hab,if_false,anchorsHave] using And.intro (hx a (by simp)) (hy b (by simp))

variable (extra : Expr) (hm : m.Represents D nodes M) (hk : 64 ≤ parameter extra n)
    (hM : Controller.Admissible (parameter extra n) M) (hD : D < 2^b) (hcap : Optimal.Parameters.logCap n ≤ D)

include hk hM hcap

private theorem fraction_cap (x : Fin n) :
    let k := parameter extra n
    PolylogOracle.grid k + (Neighborhood.schedule M.tree.system k (ArbitraryLabels.pathHeight k) (by omega)
      (halfWidth k) (width_pos k) {x}).length * EnclosureParameters.alphabetExponent k (ArbitraryLabels.pathHeight k) ≤ D :=
  (PolylogLocalBudget.endpoint_precision extra M.tree.system hk {x} (by simp) hM.degree).trans hcap

include hm hD in
theorem candidate_value (x : Fin n) : (candidate D (parameter extra n) m x).value =
    (PolylogOracle.centralTest M (parameter extra n) x).map Certificates.roundUp := by
  have cap := fraction_cap (b := b) extra hk hM hcap x
  exact central_value m.valid m.cache (le_refl b) hD (wallSpec hm hM.toGeometric) (by omega)
    hm.spatial.graph hM.noLoop ((Nat.le_add_right ..).trans cap) x

include hm hD in
theorem check_value (q : Query n) : (check D (parameter extra n) m q).value.realize M =
    PolylogOracle.attempt M (parameter extra n) q := by
  let k := parameter extra n
  have pos : 0 < k := by dsimp [k]; omega
  let route := (PolylogStorage.route m.spatial q).value
  let dec := m.decode D
  have hr : PolylogRouting.decodeRoute dec route = TreeState.route (M.tree.location q.left) (M.tree.location q.right) :=
    PolylogStorage.route_value hm.spatial (m.decode_injective D) q
  let P (c : ℚ) := 0 ≤ c ∧ c ≤ 1
  have path (x : Fin n) : ∀ c ∈ M.tree.location x, P c :=
    fun c hc => ⟨hm.paths_nonneg x c hc, hm.paths_bounded x c hc⟩
  have anchors : anchorsHave P (PolylogRouting.decodeRoute dec route) :=
    hr ▸ anchorsHave_route P _ _ (path q.left) (path q.right)
  have cut (c : ℕ) (hc : P (dec c)) : ∃ a : blockStore.Ref b,
      PolylogBits.Represents blockStore m.heap c a ∧ PolylogPrefix.coordinate blockStore D a = dec c ∧
      value blockStore b a ≤ 2^D := by
    obtain ⟨a,rep⟩ := (nonneg_iff blockStore m.heap D b c).mp hc.1
    have eq : PolylogPrefix.coordinate blockStore D a = dec c := (decode_of_rep m.valid rep).symm
    exact ⟨a,rep,eq,value_bound a (eq.le.trans hc.2)⟩
  let W := wallSpec hm hM.toGeometric
  have thresholdOK (x : Fin n) (c : ℕ) (hc : P (dec c)) :
      (threshold m.spatial.graph m.spatial.walls m.heap (fun h => m.cache.lookup h false) b D k x c).value =
      PolylogOracle.thresholdTest M k x (dec c) := by
    obtain ⟨a,rep,eq,bound⟩ := cut c hc
    rw [← eq]
    exact threshold_value m.valid m.cache (le_refl b) hD W pos hm.spatial.graph hM.noLoop x c a rep bound
      (fraction_cap (b := b) extra hk hM hcap x)
  apply PolylogActive.attempt_value M k _ _ _ _ _ q dec _ route hr _ _ _ rfl
  · exact pair_value m.valid m.cache (le_refl b) hD W pos hm.spatial.graph hM.noLoop
      ((Nat.le_add_right ..).trans (fraction_cap (b := b) extra hk hM hcap q.left)) _ _
  · intro c hc
    apply thresholdOK q.left c
    simpa only [hc,PolylogRouting.decodeRoute,anchorsHave] using anchors
  · intro c hc
    apply thresholdOK q.right c
    simpa only [hc,PolylogRouting.decodeRoute,anchorsHave] using anchors
  · intro a b' hab
    have hpair : P (dec a) ∧ P (dec b') := by simpa only [hab,PolylogRouting.decodeRoute,anchorsHave] using anchors
    obtain ⟨_,ra,_,_⟩ := cut a hpair.1
    obtain ⟨_,rb,_,_⟩ := cut b' hpair.2
    have := m.less_correct D a b'
    simpa only [Memory.less, PolylogAddressOrder.less, isRoot_of_rep ra, isRoot_of_rep rb, if_true] using this

end SortingAdversary.Continuous.PolylogCompare
