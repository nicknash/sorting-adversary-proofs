import SortingAdversary.Continuous.ArbitraryLabels
import SortingAdversary.Continuous.RationalState
import SortingAdversary.Continuous.GraphPaths
import SortingAdversary.Continuous.TraceAccounting
import SortingAdversary.Optimal.PublicLegality
import SortingAdversary.Optimal.RankWork

/-!
# The executable continuous adversary

The controller stores exact rational bounds and reduced dyadic anchor paths.
It routes a comparison, runs at most three selection attempts, records the
answer, and performs the paper's single path-or-degree repair. The returned
action trace records precisely those mutations for the semantic and counting
proofs; it contains no probabilities, volumes, or proof-oracle inputs.

After the finite horizon, all answers use fixed ranks computed from the
bounded transcript. The `none` result of `compare` detects exhaustion of the
three selection attempts; the legality theorem proves that this case is
unreachable for valid states with the paper's parameter range.
-/

namespace SortingAdversary.Continuous.Controller

open FiniteAveraging TreeState OrderRegion
open TraceAccounting (Move Action)
open SortingAdversary.Optimal.GraphBalls

variable {n : ℕ}

structure Memory (n : ℕ) where
  tree : State n ℚ
  paths : Fin n → List DyadicAnchor
  history : History n

def initial (n : ℕ) : Memory n := ⟨TreeState.initial n, fun _ => [], []⟩

def applyMove (M : Memory n) (m : Move n) : Memory n where
  tree := TreeState.normalize (refineAt M.tree m.item m.anchor.coordinate) m.order
  paths := Function.update M.paths m.item (M.paths m.item ++ [m.anchor])
  history := M.history

def applyMoves : Memory n → List (Move n) → Memory n
  | M, [] => M
  | M, m :: ms => applyMoves (applyMove M m) ms

def applyAction (M : Memory n) : Action n → Memory n
  | .selection m | .degree m => applyMove M m
  | .path ms => applyMoves M ms
  | .answer q a order =>
    ⟨TreeState.normalize (record M.tree q a) order, M.paths, ⟨q, a⟩ :: M.history⟩

def runActions (M : Memory n) (actions : List (Action n)) : Memory n :=
  actions.foldl applyAction M

/-- Encoding is arithmetic on the reduced numerator and denominator. -/
def makeMove (M : Memory n) (x : Fin n) (c : ℚ) : Move n :=
  let anchor := DyadicAnchor.ofRat c
  let D := resetCoordinate M.tree.system x anchor.coordinate
  ⟨x, anchor, rankOrder (GraphOrder.graphRank D)⟩

def reverseAnswer : Answer → Answer
  | .less => .greater
  | .greater => .less

def reverseResult : LocalSelection.Result n → LocalSelection.Result n
  | .answer a => .answer (reverseAnswer a)
  | .refine x c => .refine x c

/-- The free coordinate is the first argument of every threshold test. -/
def attempt (M : Memory n) (k : ℕ) (q : Query n) : LocalSelection.Result n :=
  match route (M.tree.location q.left) (M.tree.location q.right) with
  | .coordinates => ArbitraryLabels.select M.tree.system k q.left q.right
  | .leftFree c => ArbitraryLabels.selectThreshold M.tree.system k q.left c
  | .rightFree c => reverseResult (ArbitraryLabels.selectThreshold M.tree.system k q.right c)
  | .anchors c d => .answer (if c < d then .less else .greater)

structure Result (n : ℕ) where
  memory : Memory n
  answer : Answer
  actions : List (Action n)

/-- Fuel counts selection attempts, including the successful final test. -/
def selectLoop (k : ℕ) (q : Query n) : ℕ → Memory n → Option (Result n)
  | 0, _ => none
  | fuel + 1, M =>
    match attempt M k q with
    | .answer a => some ⟨M, a, []⟩
    | .refine x c =>
      let m := makeMove M x c
      (selectLoop k q fuel (applyMove M m)).map fun r =>
        ⟨r.memory, r.answer, .selection m :: r.actions⟩

/-- A reserved path is completed in path order, even after its earlier
vertices have been removed from the parent graph. -/
def pathBatch (k : ℕ) : Memory n → List (Fin n) → Memory n × List (Move n)
  | M, [] => (M, [])
  | M, x :: xs =>
    let m := makeMove M x (ArbitraryLabels.chooseAnchor M.tree.system k x)
    let r := pathBatch k (applyMove M m) xs
    (r.1, m :: r.2)

def degreeChoice (M : Memory n) (k : ℕ) : Option (Fin n) :=
  (List.finRange n).find? fun x => decide ((neighbors M.tree.system.edge x).card = k)

/-- All unaffected node graphs already satisfy the strict bounds, so the
global scan finds exactly a violation at the node where an answer was added. -/
def repair (k : ℕ) (M : Memory n) : Memory n × List (Action n) :=
  match GraphPaths.firstPath M.tree.system.edge (2 ^ k) with
  | some xs =>
    let r := pathBatch k M xs
    (r.1, [.path r.2])
  | none =>
    match degreeChoice M k with
    | none => (M, [])
    | some x =>
      let m := makeMove M x (ArbitraryLabels.chooseAnchor M.tree.system k x)
      (applyMove M m, [.degree m])

def compare (k : ℕ) (M : Memory n) (q : Query n) : Option (Result n) :=
  (selectLoop k q 3 M).map fun r =>
    let D := (record r.memory.tree q r.answer).system
    let order := rankOrder (GraphOrder.graphRank D)
    let answered := applyAction r.memory (.answer q r.answer order)
    let repaired := repair k answered
    ⟨repaired.1, r.answer, r.actions ++ [.answer q r.answer order] ++ repaired.2⟩

def horizon (n : ℕ) : ℕ := n * Nat.clog 2 n

/-- The stored frozen ranks are computed once from the bounded transcript. -/
def freeze (h : History n) : Fin n → Fin n :=
  let table := SortingAdversary.Optimal.SparseClosure.tableClosure
    (SortingAdversary.Optimal.PublicLegality.historyRows h)
  let ranks := (SortingAdversary.Optimal.RankWork.storedRanks table).value
  fun x => ranks[x]

@[simp] theorem freeze_apply (h : History n) (x : Fin n) :
    freeze h x = SortingAdversary.Optimal.PublicOrder.extensionRank
      (SortingAdversary.Optimal.PublicLegality.publicRows h) x := by
  simp only [freeze, SortingAdversary.Optimal.RankWork.storedRanks_value,
    Fin.getElem_fin, Vector.getElem_ofFn]
  rfl

def rankAnswer (r : Fin n → Fin n) (q : Query n) : Answer :=
  if r q.left < r q.right then .less else .greater

inductive MachineState (n : ℕ) where
  | active (memory : Memory n)
  | frozen (ranks : Fin n → Fin n)

def start (n k : ℕ) : MachineState n :=
  if 64 ≤ k then .active (initial n) else .frozen id

/-- The total machine transition. Exhaustion has a defined fallback, but is
excluded by the theorem for every reachable active state. -/
def step (k : ℕ) (s : MachineState n) (q : Query n) : Answer × MachineState n :=
  match s with
  | .frozen r => (rankAnswer r q, .frozen r)
  | .active M =>
    if M.history.length < horizon n then
      match compare k M q with
      | some r => (r.answer, .active r.memory)
      | none =>
        let ranks := freeze M.history
        (rankAnswer ranks q, .frozen ranks)
    else
      let ranks := freeze M.history
      (rankAnswer ranks q, .frozen ranks)

def replay (k : ℕ) (past : History n) : MachineState n :=
  past.reverse.foldl (fun s o => (step k s o.query).2) (start n k)

def strategy (k : ℕ) : Strategy n := fun past q => (step k (replay k past) q).1

@[simp] theorem replay_cons (k : ℕ) (o : Observation n) (past : History n) :
    replay k (o :: past) = (step k (replay k past) o.query).2 := by
  simp [replay, List.foldl_append]

theorem pathBatch_labels (k : ℕ) (M : Memory n) (xs : List (Fin n)) :
    ((pathBatch k M xs).2.map Move.item) = xs := by
  induction xs generalizing M with
  | nil => rfl
  | cons x xs ih => simp only [pathBatch, List.map_cons, makeMove, ih]

theorem pathBatch_apply (k : ℕ) (M : Memory n) (xs : List (Fin n)) :
    (pathBatch k M xs).1 = applyMoves M (pathBatch k M xs).2 := by
  induction xs generalizing M with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem degreeChoice_some (M : Memory n) (k : ℕ) (x : Fin n)
    (h : degreeChoice M k = some x) : (neighbors M.tree.system.edge x).card = k :=
  of_decide_eq_true (List.find?_some
    (p := fun y => decide ((neighbors M.tree.system.edge y).card = k)) h)

theorem degreeChoice_none (M : Memory n) (k : ℕ) :
    degreeChoice M k = none ↔ ∀ x, (neighbors M.tree.system.edge x).card ≠ k := by
  simp [degreeChoice, List.find?_eq_none]

end SortingAdversary.Continuous.Controller
