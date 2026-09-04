Strengthened-curvature sorting adversary checkpoint
===================================================

Main result
-----------
A deterministic polynomial-time adversary forces

  (0.715579977964088...)*n*log_2(n) - O(n)

comparisons.  The universal determinant-ratio constant is K = 347/50 = 6.94.

Files
-----
- strengthened_curvature_sorting_adversary.pdf
  The 19-page audited research note.
- strengthened_curvature_sorting_adversary.tex
  LaTeX source.
- verify_0715579_strengthened_curvature_revised.py
  The theorem-critical interval certificate (120 decimal places).
- certificate_0715579_revised.txt
  Recorded certificate output.
- audit_diagnostics.py
  Independent non-rigorous consistency checks.
- audit_diagnostics_output.txt
  Recorded diagnostic output.
- schedule_plot.pdf
- diagnostic_envelope_plot.pdf
  Figure assets used by the LaTeX source.

Reproduction
------------
Run the certificate:

  python verify_0715579_strengthened_curvature_revised.py

Compile the note from this directory:

  latexmk -pdf strengthened_curvature_sorting_adversary.tex

The finite proof is conditional on the correctness of mpmath.iv's outward
interval arithmetic, as stated explicitly in the note.
