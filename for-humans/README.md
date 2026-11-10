# An Optimal Deterministic Adversary for Sorting

Nicholas Nash · 10 November 2026 · ORCID [0009-0003-0475-7852](https://orcid.org/0009-0003-0475-7852)

Section 1 states the main theorem and explains the derandomization
problem. Section 2 reviews earlier adversaries. Section 3 defines
order-restriction DAGs, their canonical intervals, and coordinate
restriction. It then assembles them into a tree and gives the comparison,
repair, and refinement procedures. A failed comparison test supplies an
interior anchor with large volume gain. A repair chooses its anchor
separately and passes it to the same move operation.

Section 4 proves that refinements are rare by counting the binary
denominators in a path repair. It then counts the total orders consistent
with the answers. Unqueried labels can be inserted freely into each
compatible order on queried labels, giving the prefix guarantee
`log T_q >= log(n!) - (1 + O(log k/k))q`.

Section 5 chooses the parameters within a polynomial-time budget. Section 6
applies the prefix bound to partial-order production with vanishing
relative error. A weak-order extension gives a supplied-poset guarantee
of `(1-o(1))log e(P) - O(n log log n)` further comparisons.
The appendices prove the independent DAG lemmas, construct the finite
local calculations, and supply the quantitative estimates and corollary
proofs. The tree-dependent child-admission argument remains in Section 3.

The revision follows the mathematical and expository recommendations in
[Simplify Paper Arguments](https://chatgpt.com/g/g-p-6a045ae0f48c8191895c83cae6fb3a8b-adversaries/c/6af20322-5238-83eb-8c1a-60fbea8e1d71).
The retained KZZ lattice figure illustrates the intermediate child ranges.

- [Current paper](output/pdf/paper.pdf)
- `paper.tex`: title, approved abstract, methodological disclosure, and section inputs
- `sections/`: exposition, complete proofs, figures, and references
- `anc/`: exact finite diagnostics and recorded results
- `REVIEW_NOTES.txt`: provenance and the scope of verification
- `revision.json`: current revision metadata

Build with TeX Live and `latexmk`:

```sh
cd for-humans
make
make checks
make submission
```

`make submission` builds `output/submission/hexagon-source.zip` from the TeX
source and ancillary checks. It excludes build intermediates, review notes,
Lean files, and the precompiled PDF.

The exact-rational diagnostics check the charging inequalities, continuous
moments of the finite digit update, binary-grid rounding, middle-half
precision, and interval certificates against small-instance probabilities.
The accounting checks cover rarity, the stopping charge for queried labels,
and free insertion of untouched labels. Exact endpoint calculations check
locality with frozen boundaries and different topological tie orders.
A separate exhaustive diagnostic checks repair after one inserted arc on
DAGs with at most five vertices, including every eligible repair choice.
Small examples retain every digit sequence with its multiplicity. Independent volume
calculations remain as references for the effective-interval and refinement
section checks; volume integration is no longer part of the adversary.
These are finite diagnostics. The general density, locality, and comparison
arguments are proved in the manuscript. Earlier finite-mesh diagnostics
remain in `anc/` as historical material, outside the current check target
and submission archive.
The related Lean
development in this repository concerns the earlier integer-colour
construction; it does not formally verify this unit-interval proof.

The version submitted to Hexagon as **hexagon:2611.00196**, under CC BY 4.0
on 7 November 2026, is preserved in
[commit 3075b7e](https://github.com/nicknash/sorting-adversary-proofs/tree/3075b7e81eb86b16a3de09c4e03edb00d4434d48/for-humans).
`submission.json` records that deposit. The current revision has not been
submitted as a replacement.
