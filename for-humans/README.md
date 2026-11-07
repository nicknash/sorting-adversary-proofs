# An Optimal Deterministic Adversary for Sorting

Nicholas Nash · 7 November 2026 · ORCID [0009-0003-0475-7852](https://orcid.org/0009-0003-0475-7852)

The paper now follows *Deferred separation: positions, refinement, and prefix
codes*. It uses continuous positions, dyadic anchors, a prefix-code bound for
refinement costs, and an exact largest-coordinate volume recurrence.

- [Compiled paper](output/pdf/paper.pdf)
- `paper.tex`: entry point, abstract, and methodological disclosure
- `sections/deferred-separation.tex`: mathematical exposition and references
- `anc/check_local_volume.py`: exact numerical diagnostics
- `anc/check_local_volume.json`: recorded results
- `REVIEW_NOTES.txt`: provenance and verification scope

Build with TeX Live and `latexmk`:

```sh
cd for-humans
make
make checks
make submission
```

The submission command creates `output/submission/hexagon-source.zip`, containing
only the TeX source and permitted ancillary checks. Figures and references are
embedded in the TeX. Build intermediates and rendering checks are ignored;
the compiled PDF is versioned.

The related Lean development elsewhere in this repository follows the earlier
recursive integer-colour construction. The paper distinguishes that formalization
from the continuous presentation used here.

Submitted to Hexagon as **hexagon:2611.00196** under CC BY 4.0 on 7 November
2026. The source and compiled PDF were received successfully; moderator review
is pending. Submission metadata and hashes are in `submission.json`.
