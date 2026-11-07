import SortingAdversary.Optimal.RepresentationTree
import SortingAdversary.Optimal.RecursiveController

/-!
# Runtime observations of the measured recursive controller

Only the comparison sign, next stored tree, and identity counter are kept by
the online machine. Accounting payloads and products can be erased from the
implementation while equality of these three observations preserves the
complete strategy. Reference executors appear only in proof indices.
-/

namespace SortingAdversary.Optimal.MeasuredController

open RepresentationWork StoredRouting

variable {n : ℕ}

structure Core (n : ℕ) where
  forward : Bool
  next : StoredTree n
  counter : ℕ

def Core.ofAnswered {P : LocalProperty n} {Payload : Type*} {t : StoredTree n} {a b : Fin n}
    (r : Answered P Payload t a b) : Core n := ⟨r.forward, r.next, r.counter⟩

structure Output (expected : Core n) where
  core : Core n
  access : TreeAccess core.next
  actual : core = expected
  cached : access.Bound 2

abbrev StopExecutor {P : LocalProperty n} {Payload : Type*} (stop : Stopper P Payload) :=
  (t : StoredTree n) → (access : TreeAccess t) → access.Bound 2 →
    (hw : t.erase.WellFormed) → (ho : t.erase.Coherent) → (ready : AllNodes P t) →
    (a b : Fin n) → (ha : a ∈ t.pool.members) → (hb : b ∈ t.pool.members) →
    (hab : t.pool.system.edge a b ≠ true) → (hba : t.pool.system.edge b a ≠ true) →
    (hstop : ¬ ∃ c, t.pool.pins a = some c ∧ t.pool.pins b = some c) → (counter : ℕ) →
    PrimitiveWork.Result (Output (Core.ofAnswered (stop t hw ho ready a b ha hb hab hba hstop counter)))

abbrev RouteExecutor {P : LocalProperty n} {Payload : Type*} (stop : Stopper P Payload)
    (stable : DelegationStable P) (delegatePayload : ℕ → Fin n → Fin n → Payload → Payload) :=
  (t : StoredTree n) → (access : TreeAccess t) → access.Bound 2 →
    (hw : t.erase.WellFormed) → (ho : t.erase.Coherent) → (ready : AllNodes P t) →
    (a b : Fin n) → (ha : a ∈ t.pool.members) → (hb : b ∈ t.pool.members) →
    (hab : t.pool.system.edge a b ≠ true) → (hba : t.pool.system.edge b a ≠ true) → (counter : ℕ) →
    PrimitiveWork.Result (Output (Core.ofAnswered
      (routeUnknown stop stable delegatePayload t hw ho ready a b ha hb hab hba counter)))

end SortingAdversary.Optimal.MeasuredController
