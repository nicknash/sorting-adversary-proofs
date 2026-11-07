# An optimal deterministic sorting adversary

Initial human-readable paper draft, 7 November 2026.

- `paper.tex` is the entry point; the exposition is split across `sections/`.
- `references.bib` contains the bibliography.
- `REVIEW_NOTES.txt` records provenance, editorial questions, and the boundary
  between the manuscript and the current Lean development.

Build with a TeX Live installation providing `latexmk`, BibTeX, TikZ, and
`algpseudocode`:

```sh
cd for-humans
make
```

The [compiled paper](output/pdf/paper.pdf) is versioned alongside the sources.
Build intermediates and local rendering checks are ignored.
The algorithm is specified before the detailed proofs. The opening connects
Atallah--Kosaraju, Borodin--Guibas--Lynch--Yao, Richards--Vaidya, and
Brodal--Chaudhuri--Radhakrishnan; it distinguishes the new ordered multiway
recursion from the classical binary token tree.

This draft presents the mathematical construction in the supplied manuscript.
It does not claim that the complete leading-one, polynomial-time adversary has
already been formalized in Lean. See `../docs/optimal-adversary-formalization.md`.
