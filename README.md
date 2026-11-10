# Sorting adversaries in Lean

**[Read the human-friendly paper (PDF)](for-humans/output/pdf/paper.pdf)**

The paper's continuous adversary is formalized in Lean 4 under
[SortingAdversary/Continuous](https://github.com/nicknash/sorting-adversary-proofs/tree/68ba6a2073abb8ea661d5347a3fee06c120c5a64/SortingAdversary/Continuous)
([PR #10](https://github.com/nicknash/sorting-adversary-proofs/pull/10)).
Lean proves consistency of its answers, the $(1-o(1))n\log_2 n$ comparison
lower bound against every correct sorter, and polynomial initialization and
per-query cost in an explicit arithmetic cost model. The combined theorem is in
[Continuous/UniformEfficient.lean](https://github.com/nicknash/sorting-adversary-proofs/blob/68ba6a2073abb8ea661d5347a3fee06c120c5a64/SortingAdversary/Continuous/UniformEfficient.lean).

The earlier recursive colour and curvature adversary formalizations are also
retained.

See the [continuous formalization notes](https://github.com/nicknash/sorting-adversary-proofs/blob/68ba6a2073abb8ea661d5347a3fee06c120c5a64/docs/continuous-adversary-formalization.md)
for the theorem map, build instructions, and verification assumptions.
