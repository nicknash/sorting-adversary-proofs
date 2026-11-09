# An Optimal Deterministic Adversary for Sorting

Nicholas Nash · 9 November 2026 · ORCID [0009-0003-0475-7852](https://orcid.org/0009-0003-0475-7852)

The current manuscript presents the unit-interval adversary using finite
averaging to estimate comparison probabilities and one coefficient to
account for refinements. It introduces the derandomization problem, reviews
the classical binary-tree adversaries and the interval lattice of Kaplan,
Zamir, and Zwick, then gives an illustrated data-structure overview with high-level query
pseudocode, followed by the complete mechanical algorithm. Section 6 defines
the finite calculation explicitly: initialize temporary positions at their
lower endpoints, update them in topological order, and average over every
sequence of choices from a finite mesh. The proof bounds the error and shows
why only a neighborhood of the queried items is needed. Subsequent sections
derive the comparison bound and give a uniform polynomial-time implementation
with exact dyadic arithmetic. The tree structure, anchor rules, and geometric
packing argument are retained from the preceding version.

The source for this simplification is the
[finite-averaging audit](https://chatgpt.com/g/g-p-6a045ae0f48c8191895c83cae6fb3a8b-adversaries/c/6af1b5f8-a1d0-83ed-b93d-fe7efd94df67).
Sections 1 and 2 are unchanged. Section 3 has only the necessary corrections
to answer selection: directly determined answers and the use of one strict
event estimate together with its complement.

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
