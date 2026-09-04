# Sorting adversaries in Lean

This repository is an audit-oriented, `sorry`-free Lean 4 formalization of a
deterministic curvature/volumetric adversary for comparison sorting.

## Headline theorem, stated exactly

Put

```text
K = 347 / 50
B = (1/2) log₂(K) = 1.397467831401768...
c = 1/B = 2/log₂(K) = 0.715579977964088...
```

The closing theorem is
[`SortingAdversary.StrengthenedCurvature.efficient_curvature_adversary`](SortingAdversary/StrengthenedCurvature/EfficientRule.lean).
It proves `StrengthenedCurvatureTarget`. Unfolded, this says that there is one
history-dependent strategy for every input size and a uniform constant
`C ≥ 0` such that, for every `n ≥ 2` and every correct finite deterministic
comparison tree on `n` labelled items, running the tree against the strategy:

1. produces a transcript compatible with an actual total ranking `π`; and
2. makes at least

   ```text
   c · n log₂(n) - C · n
   ```

   comparisons.

The construction in the proof takes `C = (3/2)/B`. The compatibility bridge
then proves that the same tree has a genuine input `π` whose ordinary
root-to-leaf cost is that large. Thus the result is an online adversary lower
bound, not merely a statement about an abstract potential or an inconsistent
answer sequence.

Lean also proves, without decimal evaluation,

```text
0.7155 < c < 18/25 = 0.72.
```

In particular, the repository does **not** prove leading coefficient `0.72`;
`Target072` is only a named specification.

## What Lean formalizes

The trusted root is [`SortingAdversary.lean`](SortingAdversary.lean). Its proof
path contains all of the following.

- **Sorting semantics.** A ranking is a permutation of `Fin n`; a comparison
  tree is a finite binary tree; correctness means that every hidden ranking is
  returned exactly; and cost counts comparison nodes. The theorem
  `run_matches_compatible_ranking` connects an adaptive adversarial run to the
  ordinary run on a concrete compatible ranking.
- **The retained history.** Repeated comparisons and comparisons already
  implied by transitive closure are answered consistently without adding a
  geometric row. Every genuinely informative comparison is retained, and the
  retained history has exactly the same compatible rankings as the full
  transcript.
- **The history polytope and potential.** Item positions lie in `(0,1)`, and
  each retained answer adds a strict order inequality. For rows with normals
  `aᵢ` and positive slacks `sᵢ(x)`, Lean defines

  ```text
  H_G(x) = Σᵢ aᵢ aᵢᵀ / sᵢ(x)²
  Φ(G)   = inf_{x ∈ K_G} (1/2) log₂ det H_G(x).
  ```

  It proves positive definiteness, boundary coercivity, continuity, existence
  of a volumetric center, and the stationarity equations at a center.
- **The local matrix analysis.** Lean formalizes whitening, effective
  resistance and the unit-energy electrical motion, determinant and inverse
  differentiation, the row-space projection formula for the second derivative,
  the sign-imbalance curvature saving, and the integrated bounds for both
  possible answer branches.
- **The finite scalar certificate.** The matrix problem is reduced to normalized
  query offset `δ` and positive electrical-energy fraction `r`. A proved
  exact-rational interval checker covers
  `[0, 411/1000] × [0,1]` over 22 schedule segments. Lean natively replays
  the supplied 7,315-terminal-box certificate and proves the scalar envelope
  giving determinant ratio at most `347/50`. Larger offsets are handled at
  the old center by the rank-one determinant formula.
- **The one-comparison and global bounds.** For every informative query, one
  feasible answer raises the potential by at most `B`. Initially the
  potential is at most `(3/2)n`; a compatible terminal history has potential
  at least `n log₂ n`. Telescoping gives the theorem above, while entailed
  queries only add to the algorithm's actual comparison count.
- **Approximate child selection.** Given certified rational estimates of both
  child potentials with absolute error `ε`, Lean proves that choosing the
  smaller estimate loses at most `2ε` relative to the true smaller child.

The compact declaration-level audit is in
[`SortingAdversary/Audit.lean`](SortingAdversary/Audit.lean), and the intended
meaning of the definitions is documented in
[`docs/semantic-boundary.md`](docs/semantic-boundary.md).

## How the result is achieved

The closest mathematical source is the strengthened-curvature note in the
research bundle:
[`strengthened_curvature_sorting_adversary.pdf`](strengthened_curvature_checkpoint_bundle/strengthened_curvature_sorting_adversary.pdf)
([TeX source](strengthened_curvature_checkpoint_bundle/strengthened_curvature_sorting_adversary.tex)).
At a high level, the proof works as follows.

1. Encode all informative answers as an open order polytope and measure its
   state by the minimum log determinant of the logarithmic-barrier Hessian.
2. Show that this potential starts at order `n` but must reach
   `n log₂ n` once the complete order is known.
3. At the current volumetric center, whiten the Hessian and express a proposed
   comparison as a unit-energy electrical direction. This turns the
   high-dimensional derivative calculation into projection identities.
4. Use the imbalance between positive and negative row motions to subtract a
   definite amount from the generic curvature bound. Integrate the resulting
   inequalities along two trial branches and average them to eliminate the
   first-derivative/cubic obstruction.
5. Reduce what remains to a two-variable scalar envelope. A rational
   piecewise-linear schedule and the exact certificate prove the bound for
   small offsets; for large offsets, keep the side containing the old center.
6. Choose a certified child, charge at most `B` potential per informative
   comparison, and telescope the initial-to-terminal gap.

For a more elementary conceptual route, see
[`elementary_ln2_sorting_adversary_memo.pdf`](elementary_ln2_sorting_adversary_memo.pdf)
([TeX source](elementary_ln2_sorting_adversary_memo.tex)). That memo interprets
the same determinant as a weighted spanning-tree score, uses cubic cancellation
and three simple offset regimes, and obtains the weaker but cleaner coefficient
`ln 2 = 0.693147...`. It is useful intuition, but its matrix-tree
reinterpretation and its separate `ln 2` proof are not the theorem formalized
here; Lean follows the strengthened `347/50` argument.

## Research bundle and the trust boundary

[`strengthened_curvature_checkpoint_bundle/`](strengthened_curvature_checkpoint_bundle/)
contains the strengthened memo, its TeX source and figures, the revised Python
interval verifier, its recorded certificate output, and independent diagnostic
scripts. See the bundle's
[`README.txt`](strengthened_curvature_checkpoint_bundle/README.txt) for
reproduction commands.

The bundle explains the discovery and external audit of the scalar certificate.
The Lean theorem does not invoke the Python verifier, trust its output file, or
use the diagnostic plots. Instead, the repository proves the soundness of its
own rational interval checker and replays certificate data stored in
`StrengthenedCertificateData.lean`. The finite replay uses `native_decide`, so
the generated native evaluator axiom is explicitly visible in the axiom audit.

Lean also does not formalize a bit-cost model or a convex-optimization
implementation. The exact strategy is a semantic, noncomputable function
using exact real volumetric centers. The research memos explain why
polynomial-accuracy centers and child potentials can be obtained in polynomial
time, and Lean proves the `2ε` robustness lemma needed by that argument, but it
does not construct or verify the optimizer. Likewise, Lean uses the simpler
terminal estimate `n log₂ n`, not the memo's sharper finite
`(n+1/2) log₂(n+1)` estimate. There is no compatible-ranking counting
adversary in the theorem path.

## Build and audit

The Lean toolchain and mathlib revision are pinned.

```bash
lake update
lake exe cache get
./scripts/check-trusted-no-sorry.sh
lake build SortingAdversary
```

GitHub Actions repeats the source audit, full trusted build, `leanchecker`, and
axiom audit. See [`docs/verification.md`](docs/verification.md) for the complete
verification model.
