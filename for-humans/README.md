# An Optimal Deterministic Adversary for Sorting

Nicholas Nash · 8 November 2026 · ORCID [0009-0003-0475-7852](https://orcid.org/0009-0003-0475-7852)

The current manuscript presents the unit-interval adversary with a single
potential for repairs. It introduces the derandomization problem, reviews
the classical binary-tree adversaries and the interval lattice of Kaplan,
Zamir, and Zwick, then gives an illustrated overview and the complete
mechanical algorithm. The later sections develop legality, local
probabilities, geometric packing, the comparison bound, and a uniform
polynomial-time implementation. Worked examples distinguish fixed parent
positions from fresh child coordinates. TikZ figures illustrate the
construction, the volume identity, and the geometric proof. The potential
coefficients are derived from the changes caused by a refinement.

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

The numerical checks cover selected finite volume calculations, anchor rules,
and potential identities. They are not a verification of all adversary
trajectories or a formal proof of the locality theorem. The related Lean
development in this repository concerns the earlier integer-colour
construction; it does not formally verify this unit-interval proof.

The version submitted to Hexagon as **hexagon:2611.00196**, under CC BY 4.0
on 7 November 2026, is preserved in
[commit 3075b7e](https://github.com/nicknash/sorting-adversary-proofs/tree/3075b7e81eb86b16a3de09c4e03edb00d4434d48/for-humans).
`submission.json` records that deposit. The current revision has not been
submitted as a replacement.
