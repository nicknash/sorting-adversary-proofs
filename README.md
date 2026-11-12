# Sorting adversaries in Lean

**[Read the human-friendly paper (PDF)](for-humans/output/pdf/paper.pdf)** · [Hexagon Math](https://hexagonmath.org/2611.00196v2)

The paper's continuous adversary is formalized in Lean 4 under
[SortingAdversary/Continuous](SortingAdversary/Continuous).
Lean proves consistency of its answers, the $(1-o(1))n\log_2 n$ comparison
lower bound against every correct sorter, and polynomial initialization and
per-query cost in an explicit arithmetic cost model. The combined theorem is in
[Continuous/UniformEfficient.lean](SortingAdversary/Continuous/UniformEfficient.lean).

The earlier recursive colour and curvature adversary formalizations are also
retained.

See the [continuous formalization notes](docs/continuous-adversary-formalization.md)
for the theorem map, build instructions, and verification assumptions.
