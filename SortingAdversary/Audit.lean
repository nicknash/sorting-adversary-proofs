import SortingAdversary.Strategy
import SortingAdversary.Knowledge
import SortingAdversary.Potential
import SortingAdversary.PotentialAdversary
import SortingAdversary.AsymptoticStatement

/-!
# Audit surface

The declarations printed here are the small semantic interface a reviewer
should inspect before relying on the kernel-checked proof beneath it.
-/

#print SortingAdversary.Query
#print SortingAdversary.Ranking
#print SortingAdversary.DecisionTree
#print SortingAdversary.DecisionTree.Correct
#print SortingAdversary.AdversaryCertificate
#print SortingAdversary.lower_bound_of_adversary_certificate
#print SortingAdversary.PotentialCertificate
#print SortingAdversary.PotentialAdversaryCertificate
#print SortingAdversary.PotentialCertificate.target_le_length_mul
#print SortingAdversary.HasLeadingConstant
#print SortingAdversary.Target072

#print axioms SortingAdversary.lower_bound_of_adversary_certificate
#print axioms SortingAdversary.PotentialCertificate.target_le_length_mul
#print axioms SortingAdversary.PotentialAdversaryCertificate.lower_bound
