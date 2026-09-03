import SortingAdversary.Strategy
import SortingAdversary.Potential

/-!
# From a potential calculation to a sorting lower bound

This file is the final reusable bridge needed by an adversary-specific proof.
It packages three logically separate obligations:

1. the adversarial transcript is compatible with at least one genuine ranking;
2. the potential increments are indexed by the comparisons in that transcript;
3. exact rational potential arithmetic forces at least `k` increments.

No asymptotics and no floating-point computation occur here.
-/

namespace SortingAdversary

/-- A strategy together with exact potential certificates for all correct trees.

An implementation of a concrete adversary should normally build this structure.
The generic theorem below then converts it into an ordinary worst-case input.
-/
structure PotentialAdversaryCertificate (n k : ℕ) where
  strategy : Strategy n
  consistent : ∀ t : DecisionTree n,
    ∃ π : Ranking n, Compatible π (t.run strategy []).observations
  trace : ∀ (t : DecisionTree n), t.Correct → PotentialCertificate
  increment_count : ∀ (t : DecisionTree n) (ht : t.Correct),
    (trace t ht).increments.length = (t.run strategy []).comparisons
  maxIncrease_positive : ∀ (t : DecisionTree n) (ht : t.Correct),
    0 < (trace t ht).maxIncrease
  target_ratio : ∀ (t : DecisionTree n) (ht : t.Correct),
    (k : ℚ) ≤ (trace t ht).target / (trace t ht).maxIncrease

namespace PotentialAdversaryCertificate

/-- Forget the potential internals after using them to prove that every
interaction with a correct tree has length at least `k`. -/
def toAdversaryCertificate (cert : PotentialAdversaryCertificate n k) :
    AdversaryCertificate n k where
  strategy := cert.strategy
  consistent := cert.consistent
  long := by
    intro t ht
    have hratio :=
      (cert.trace t ht).ratio_le_length (cert.maxIncrease_positive t ht)
    have hrat : (k : ℚ) ≤ ((cert.trace t ht).increments.length : ℚ) :=
      (cert.target_ratio t ht).trans hratio
    have hnat : k ≤ (cert.trace t ht).increments.length := by
      exact_mod_cast hrat
    rw [cert.increment_count t ht] at hnat
    exact hnat

/-- A potential adversary certificate yields a genuine worst-case lower bound
for every correct deterministic comparison tree. -/
theorem lower_bound (cert : PotentialAdversaryCertificate n k)
    (t : DecisionTree n) (ht : t.Correct) : t.WorstCaseAtLeast k :=
  lower_bound_of_adversary_certificate cert.toAdversaryCertificate t ht

end PotentialAdversaryCertificate
end SortingAdversary
