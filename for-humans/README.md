# An Optimal Deterministic Adversary for Sorting

Nicholas Nash · 10 November 2026 · ORCID [0009-0003-0475-7852](https://orcid.org/0009-0003-0475-7852)

The current manuscript presents the unit-interval adversary with finite
coordinate updates on bounded neighborhoods. Section 1 introduces the
derandomization problem, and Section 2 reviews the earlier adversaries.
Section 3 gives the recursive data structure and comparison procedure.

Section 4 counts the orders represented by any state and proves the
comparison bound from one inequality relating refinement cost to volume
gain. AM–GM handles the distinct children used by a path batch. Section 5
proves consistency and the anchor guarantee. The adversary tries to certify
an answer and refines a queried item if that calculation fails. Anchor
selection similarly tries to certify a central interval, falling back to
the middle half of the item's effective interval on failure.

Section 6 implements the probability routines by finite calculations of
enclosing intervals. Disjoint intervals certify a comparison; sorting and
counting endpoints certifies a central interval. Monotonicity makes these
certificates valid. A density bound for every pair of coordinates explains
why failure yields enough volume gain to pay for refinement. Section 7
obtains uniform polynomial time from the enumeration budget
`E_k = S_k^(b_k t_k) <= n` and a horizon of `n ceil(log₂ n)` answers,
after which fixed ranks consistent with the recorded answers suffice.
Appendix A proves the density bounds using convexity and Prékopa's theorem.
Appendix B proves contraction using one averaging lemma, and Appendix C
collects the parameters.

The construction follows the mathematical simplifications in
[Simplify Paper Arguments](https://chatgpt.com/g/g-p-6a045ae0f48c8191895c83cae6fb3a8b-adversaries/c/6af20322-5238-83eb-8c1a-60fbea8e1d71).
This revision removes operational width classification, complete recognition
of forced comparisons, and the argument that repeated queries leave the
state unchanged. Precision is bounded by the refinement count times
`log₂ E_k`. The locality proof uses conditional averages of powers in place
of route enumeration. The ancillary `+17` coefficient and its appendix
are removed; the paper proves the intended `(1-o(1)) n log₂ n` bound.
The abstract, disclosure, Section 2, and existing figures are unchanged.
Sections 1 and 3 receive only the necessary roadmap and algorithm changes.

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
moments of the finite digit update, shortest anchors, fallback-anchor
precision, and interval certificates against small-instance probabilities.
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
