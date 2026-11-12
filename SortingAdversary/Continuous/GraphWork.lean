import SortingAdversary.Continuous.Controller
import SortingAdversary.Optimal.ClosureWork
import SortingAdversary.Optimal.RankWork

/-!
# Counted materialized graph ordering and freezing

The closure and ranking computations are the actual cached-table algorithms.
Input row evaluation carries its own cost; a functional graph is never treated
as an unexplained constant-time oracle. For freezing, the row callback is the
concrete bounded history scan, so the complete charge has no callback premise.
The counters use the repository's primitive word-operation model.
-/

namespace SortingAdversary.Continuous.GraphWork

open SortingAdversary.Optimal
open PrimitiveWork SparseClosure

variable {n : ℕ}

def closureRanks (rows : ClosureWork.Rows n) : PrimitiveWork.Result (Vector (Fin n) n) :=
  let closed := ClosureWork.closure rows
  let ranked := RankWork.storedRanks closed.value
  ⟨ranked.value, closed.work + ranked.work⟩

theorem closureRanks_value (rows : ClosureWork.Rows n) :
    (closureRanks rows).value =
      Vector.ofFn (PublicOrder.extensionRank (closure (ClosureWork.values rows))) := by
  simp only [closureRanks, RankWork.storedRanks_value, ClosureWork.closure_value,
    lookup_tableClosure]

def closureRanksBound (n rowWork : ℕ) : ℕ :=
  ClosureWork.workBound n rowWork + 11 * n ^ 2 + 17 * n + 2

theorem closureRanks_work (rows : ClosureWork.Rows n) (rowWork : ℕ)
    (hrows : ∀ x y, (rows x y).work ≤ rowWork) :
    (closureRanks rows).work ≤ closureRanksBound n rowWork := by
  have hc := ClosureWork.closure_work_le rows rowWork hrows
  have hr := RankWork.storedRanks_work_le (ClosureWork.closure rows).value
  unfold closureRanks closureRanksBound
  dsimp only
  omega

theorem closureRanks_graphRank (D : FiniteAveraging.System (Fin n) ℚ)
    (rows : ClosureWork.Rows n) (he : ClosureWork.values rows = D.edge) (x : Fin n) :
    ((closureRanks rows).value[x]).val = GraphOrder.graphRank D x := by
  rw [closureRanks_value, GraphOrder.graphRank_eq, he]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]

/-- The predicate inspects one observation's orientation, two labels, and
the two equality tests. Eight word operations include these field reads and
Boolean combination; list traversal is charged by `PrimitiveWork.any`. -/
def historyRows (h : History n) (x y : Fin n) : PrimitiveWork.Result Bool :=
  PrimitiveWork.any (fun o =>
    ⟨decide (x = PublicLegality.earlier o ∧ y = PublicLegality.later o), 8⟩) h

theorem historyRows_value (h : History n) :
    ClosureWork.values (historyRows h) = PublicLegality.historyRows h := by
  funext x y
  simp only [ClosureWork.values, historyRows, PrimitiveWork.any_value, PublicLegality.historyRows]

theorem historyRows_work (h : History n) (x y : Fin n) :
    (historyRows h x y).work ≤ 10 * h.length + 2 := by
  have hh := PrimitiveWork.any_work_le
    (fun o => (⟨decide (x = PublicLegality.earlier o ∧ y = PublicLegality.later o), 8⟩ :
      PrimitiveWork.Result Bool)) h 8 (fun _ _ => le_rfl)
  simpa only [historyRows, Nat.reduceAdd, Nat.mul_comm] using hh

/-- This computes the same cached vector installed by `Controller.freeze`. -/
def freeze (h : History n) : PrimitiveWork.Result (Vector (Fin n) n) :=
  closureRanks (historyRows h)

theorem freeze_value (h : History n) :
    (freeze h).value = Vector.ofFn (Controller.freeze h) := by
  rw [freeze, closureRanks_value, historyRows_value]
  apply congrArg Vector.ofFn
  funext x
  rw [Controller.freeze_apply, PublicLegality.publicRows_eq]

theorem freeze_work (h : History n) :
    (freeze h).work ≤ closureRanksBound n (10 * h.length + 2) :=
  closureRanks_work _ _ (historyRows_work h)

theorem freeze_work_bounded_history (h : History n) (hh : h.length ≤ n ^ 2) :
    (freeze h).work ≤ 100 * (n + 1) ^ 4 := by
  apply (freeze_work h).trans
  have hm : n * n * h.length ≤ n * n * n ^ 2 := Nat.mul_le_mul_left _ hh
  unfold closureRanksBound ClosureWork.workBound
  nlinarith [Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]

theorem horizon_le_square (n : ℕ) : Controller.horizon n ≤ n ^ 2 := by
  unfold Controller.horizon
  have hc : Nat.clog 2 n ≤ n := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  simpa only [pow_two] using Nat.mul_le_mul_left n hc

theorem freeze_work_at_horizon (h : History n) (hh : h.length ≤ Controller.horizon n) :
    (freeze h).work ≤ 100 * (n + 1) ^ 4 :=
  freeze_work_bounded_history h (hh.trans (horizon_le_square n))

/-- After the horizon, a query only reads two cached ranks and compares them;
the returned frozen table is shared unchanged. -/
def frozenAnswer (r : Vector (Fin n) n) (q : Query n) : PrimitiveWork.Result Answer :=
  ⟨if r[q.left] < r[q.right] then .less else .greater, 3⟩

theorem frozenAnswer_value (r : Vector (Fin n) n) (q : Query n) :
    (frozenAnswer r q).value = Controller.rankAnswer (fun x => r[x]) q := rfl

theorem frozenAnswer_work (r : Vector (Fin n) n) (q : Query n) :
    (frozenAnswer r q).work = 3 := rfl

end SortingAdversary.Continuous.GraphWork
