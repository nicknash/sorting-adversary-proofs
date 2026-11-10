# An Optimal Deterministic Adversary for Sorting

Nicholas Nash · 10 November 2026 · ORCID [0009-0003-0475-7852](https://orcid.org/0009-0003-0475-7852)

The current manuscript presents the unit-interval adversary with finite
coordinate updates on bounded neighborhoods. Section 1 introduces the
derandomization problem, and Section 2 reviews the earlier adversaries.
Section 3 gives the tree of item records and in-node DAGs, the comparison
procedure, and the operations that refine items and propagate bounds.

The adversary selects and records an answer, then performs at most one
structural repair. A newly inserted arc can create a long path or raise
an endpoint's degree; removing that arc as part of the repair restores
both graph bounds. Before the answer, only the queried items can be
refined, at most once each. A full call makes at most `n+2` refinements.

Section 4 explains the volume gained by refinement, counts the orders
represented by a state, and proves that refinements are rare: there are
only `O(q/k)` moves after `q` completed calls. This gives the optimal
comparison bound without separate charging coefficients. Section 5 chooses
anchors by rounding to a binary grid, proves the one-arc repair property,
and explains why answer selection stops after at most two moves.

Section 6 explains the finite updates, their preservation of the uniform
distribution, and the enclosing intervals that certify comparisons.
Section 7 combines a finite horizon, a clocked parameter search, and the
budget `E_k <= n` to obtain uniform polynomial time. The appendices give
the normalization and density proofs, local contraction, certificate
calibration, refinement and consistency details, and arithmetic bounds.

This revision follows the newest proposal in
[Simplify Paper Arguments](https://chatgpt.com/g/g-p-6a045ae0f48c8191895c83cae6fb3a8b-adversaries/c/6af20322-5238-83eb-8c1a-60fbea8e1d71),
based on commit `d0da5c2`. It removes the implicit anchor tree, shortest-anchor
search, mixed comparison-failure/central-success branch, and the lambda/sigma
accounting. Stored intervals now give each coordinate's full feasible range;
normalization preserves the region exactly. Failed comparison certificates
use the middle half directly, while structural refinements first try a
central-interval certificate. The same rarity lemma also improves the stored
precision bound to `O(n log² n)`.

The abstract, disclosure, Section 2, and all figures except the obsolete
anchor-tree diagram are unchanged. Sections 1 and 3 receive the changes
needed for the revised algorithm, representation, and roadmap.

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
