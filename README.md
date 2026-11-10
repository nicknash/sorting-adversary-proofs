# Sorting adversaries in Lean

**[Read the human-friendly paper (PDF)](for-humans/output/pdf/paper.pdf)**

This repository formalizes a deterministic sorting adversary in Lean 4 that
forces every correct comparison sorter to make $(1-o(1))n\log_2 n$
comparisons. The proofs establish consistency of its answers, the comparison
lower bound, and polynomial initialization and per-query cost in an explicit
arithmetic cost model. The combined theorem is in
[UniformEfficient.lean](SortingAdversary/Optimal/UniformEfficient.lean).

The Lean proofs use the earlier recursive colour construction. The paper
presents a simplified continuous version that is not yet fully aligned with
the Lean development.

The repository also formalizes an earlier curvature adversary with comparison
bound $c n\log_2 n-O(n)$, where $c=2/\log_2(347/50)\approx0.71558$.

For detailed coverage and verification assumptions, see the
[optimal-adversary formalization notes](docs/optimal-adversary-formalization.md)
and [verification model](docs/verification.md).

To build with the pinned Lean toolchain and mathlib revision:

```sh
lake exe cache get
lake build SortingAdversary
```
