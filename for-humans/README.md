# An Optimal Deterministic Adversary for Sorting

Nicholas Nash · 9 November 2026 · ORCID [0009-0003-0475-7852](https://orcid.org/0009-0003-0475-7852)

The current manuscript presents the unit-interval adversary with exact
probability calculations on bounded neighborhoods. Section 1 introduces the
derandomization problem, and Section 2 reviews the earlier adversaries.
Section 3 gives the data structure and comparison procedure, including the
implicit binary anchor tree and a single preparation loop. Local anchor,
interval, and directed-path tests recognize every determined answer.

Section 4 proves the comparison bound by counting refinements and summing
their anchor depths. A probability argument relates the final state to the
unique order determined by the sorter. Section 5 proves the refinement and
anchor guarantees. Section 6 establishes the accuracy of the neighborhood
calculation and explains its exact evaluation. Section 7 chooses parameters
to obtain one uniform polynomial-time adversary. Appendix A gives the density
bounds, using Prékopa's theorem for log-concavity; Appendix B collects the
parameters.

This revision follows the mathematical simplifications in
[Simplify Paper Arguments](https://chatgpt.com/g/g-p-6a045ae0f48c8191895c83cae6fb3a8b-adversaries/c/6af20322-5238-83eb-8c1a-60fbea8e1d71).
This iteration removes the global comparison DAG, the separate repair
procedure, and persistent propagation of bounds. The abstract, disclosure,
and Sections 1–2 are unchanged; Section 3 receives the necessary changes
to the comparison and refinement rules. The density proof uses contractions
of convex sections, and the locality proof counts contracting steps along
possible sequences of updates.
The exact comparison bound is now
`(n log₂ n − 3n) / (1 + (2 log₂ k + 17)/k)` for powers of two `k ≥ 64`.

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

The current exact-rational diagnostics check the two accounting inequalities
and their comparison coefficient, and compare two independent volume
calculations on 54 systems. The geometric checks also cover 423 anchor
searches and 141 narrow-coordinate choices. New exact checks cover 370
ordered-pair certainty tests, 423 section calculations with raw and effective
bounds, and 1,110 effective intervals after coordinate removal. These are
finite diagnostics;
the general density, locality, and comparison arguments are proved in the
manuscript. The earlier finite-averaging script and its recorded results
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
