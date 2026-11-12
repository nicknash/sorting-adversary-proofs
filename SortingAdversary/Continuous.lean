import SortingAdversary.Continuous.UniformAdversary
import SortingAdversary.Continuous.ControllerResources
import SortingAdversary.Continuous.UniformEfficient
import SortingAdversary.Continuous.LayerAdversary
import SortingAdversary.Continuous.ApproximateCounting
import SortingAdversary.Continuous.Examples
import SortingAdversary.Continuous.Audit

/-!
# The current paper's continuous sorting adversary

`UniformAdversary.strategy` is the executable exact-rational construction.
`UniformAdversary.asymptoticallyOptimal` proves its unconditional leading-one
comparison bound; `worst_case` transfers the interaction to a genuine input
of every correct finite comparison tree. `production` uses the same family
for every target partial order. The supplied-information reduction states
the external weak-order entropy theorem as an explicit input.

`UniformMachineWork.build` constructs the measured stored program;
`UniformEfficient.asymptoticallyOptimal_and_polynomial` combines its exact
strategy agreement, reachable operand certificates, and fixed polynomial
initialization and query charges in the explicit schoolbook arithmetic model.

The old integer-colour development remains available under `Optimal`.
The continuous audit permits only the standard logical axioms.
-/
