# An Optimal Deterministic Adversary for Sorting

Nicholas Nash · 9 November 2026 · ORCID [0009-0003-0475-7852](https://orcid.org/0009-0003-0475-7852)

The current manuscript presents the unit-interval adversary with finite
coordinate updates on bounded neighborhoods. Section 1 introduces the
derandomization problem, and Section 2 reviews the earlier adversaries.
Section 3 gives the recursive data structure and comparison procedure.

Section 4 proves the comparison bound from guarantees about volume changes,
the cost of choosing children, and consistency. Section 5 proves those
refinement guarantees. Its anchor rule chooses the shortest binary fraction
in a central interval, obtained from empirical quartiles or effective
interval bounds. A general fact about log-concave densities explains why
approximate quartiles work: their density is comparable to the peak.
Section 6 gives the finite digit update and a theorem approximating queried
positions without a width assumption. Density bounds then yield comparison
probabilities. Section 7 obtains uniform polynomial time from the explicit
enumeration budget `E_k = S_k^(b_k t_k) <= n`.
Appendix A proves the density bounds using convexity, Prékopa's theorem,
and Bobkov's characterization of one-dimensional log-concavity.
Appendix B proves the local approximation theorem, and Appendix C collects
the parameters.

The construction follows the mathematical simplifications in
[Simplify Paper Arguments](https://chatgpt.com/g/g-p-6a045ae0f48c8191895c83cae6fb3a8b-adversaries/c/6af20322-5238-83eb-8c1a-60fbea8e1d71).
This revision separates the guarantees needed by the comparison proof
from their implementations, replaces two specialized geometric lemmas
with the central-quantile bound, and separates approximation of positions
from approximation of probabilities. One affine inequality covers all
three refinement costs. The abstract, disclosure, Sections 2 and 3, and
existing figures are unchanged from the preceding revision. Section 1
receives only necessary roadmap changes.
The explicit comparison bound remains
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

The exact-rational diagnostics check the direct charging inequalities,
continuous moments of the finite digit update, shortest anchors, narrow
anchor precision, and empirical quartiles with ties. Small chain examples
retain every digit sequence with its multiplicity. Independent volume
calculations remain as references for the local certainty and refinement
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
