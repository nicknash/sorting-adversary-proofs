# An Optimal Deterministic Adversary for Sorting

Nicholas Nash · 9 November 2026 · ORCID [0009-0003-0475-7852](https://orcid.org/0009-0003-0475-7852)

The current manuscript presents the unit-interval adversary using finite
averaging to estimate comparison probabilities and a potential function to
account for comparisons and refinements. It introduces the derandomization problem, reviews
the classical binary-tree adversaries and the interval lattice of Kaplan,
Zamir, and Zwick. Section 3 describes the state and algorithm once, with
diagrams and one comparison procedure. It introduces the parameters alongside
the operations that need them and states a probability-estimation lemma.
An implicit binary anchor tree specifies positions by root-to-node paths;
both branches of anchor selection are walks in this auxiliary tree.
Section 4 states the comparison bound in terms of the degree threshold k
and states each refinement, consistency, and geometric guarantee before
using it in the proof. Section 5 gives the anchor rules and the deferred
proofs of these guarantees; the preparation and repair bounds support its
proof of consistency and termination.
Section 6 supplies the finite probability estimator, and Section 7 proves
uniform polynomial running time with exact dyadic arithmetic.
Parameter values are chosen alongside the bounds they ensure; Appendix D
collects their values, roles, and introduction points. The comparison
pseudocode explicitly updates the global transcript and global comparison
DAG on every answer path.

The source for this simplification is the
[finite-averaging audit](https://chatgpt.com/g/g-p-6a045ae0f48c8191895c83cae6fb3a8b-adversaries/c/6af1b5f8-a1d0-83ed-b93d-fe7efd94df67).
The abstract, disclosure, and related work are unchanged; the introduction's
roadmap reflects the new order. The top-down presentation preserves the
adversary, parameter values, numerical guarantees, and comparison bound.

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

The exact-rational diagnostics cover 1,353 accounting checks, 320 comparisons
of full and truncated update sequences, and 45,756 update/rounding checks.
The earlier geometric checks cover 51 volume systems, 393 midpoint searches,
and 131 narrow-coordinate choices. These are finite diagnostics; the proofs
of convergence, locality, and the asymptotic bound are in the manuscript.
The related Lean
development in this repository concerns the earlier integer-colour
construction; it does not formally verify this unit-interval proof.

The version submitted to Hexagon as **hexagon:2611.00196**, under CC BY 4.0
on 7 November 2026, is preserved in
[commit 3075b7e](https://github.com/nicknash/sorting-adversary-proofs/tree/3075b7e81eb86b16a3de09c4e03edb00d4434d48/for-humans).
`submission.json` records that deposit. The current revision has not been
submitted as a replacement.
