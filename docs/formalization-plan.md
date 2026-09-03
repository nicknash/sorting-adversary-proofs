# Formalization plan for the 0.72 target

## Completed reusable foundation

The trusted library currently contains:

1. an explicit deterministic comparison-tree model;
2. a concrete permutation/ranking semantics;
3. adaptive strategy execution with full transcript recording;
4. the consistency-to-worst-case transfer theorem;
5. relation-valued knowledge states and semantically sound transitive closure;
6. exact rational telescoping-potential accounting; and
7. an explicit asymptotic predicate for a leading constant.

This layer is intended to remain reusable for the 37/64 adversary, the
tracked-point variants, and later adversaries.

## Required frozen mathematical source

The material available to this repository does not yet contain a complete,
audited specification of the claimed 0.72... construction.  A decimal value or
an optimized experiment is not enough to instantiate the generic Lean theorem.
The source-of-truth document must state all of the following without relying on
unstated case conventions:

1. **State.** Every field of the adversary state, including any packets,
   components, tracked points, credits, matrices, or retained history.
2. **Reachability invariant.** Structural conditions true initially and
   preserved by every response.
3. **Total response function.** A deterministic answer and successor state for
   every query in every reachable state, including repeated/entailed queries
   and all degeneracies.
4. **Realization semantics.** A proof that each reachable state represents at
   least one actual ranking and that every returned answer is consistent with
   the successor state.
5. **Potential.** Its exact definition and exact one-comparison upper bound.
6. **Terminal bound.** Why correctness of the sorting tree forces the final
   potential or structural quantity to be large.
7. **Parameter certificate.** Rational or algebraic values proving a leading
   coefficient strictly above or equal to `18/25`, without trusting floating
   point.
8. **Efficiency proof.** A separate cost-model argument, only if polynomial
   adversary running time is part of the theorem being claimed.

## Intended module tree

```text
SortingAdversary/Adversary072/
  SourceSpecification.lean
  State.lean
  Interpretation.lean
  Reachable.lean
  Response.lean
  Invariant.lean
  LocalPotential.lean
  Terminal.lean
  ExactCertificate.lean
  Main.lean
```

`Main.lean` must prove:

```lean
theorem SortingAdversary.adversary_072 : SortingAdversary.Target072
```

without `sorry`, `admit`, project-specific axioms, unchecked floating point,
`native_decide` in the trusted theorem, or an external solver treated as an
oracle.

## Recommended proof order

1. Freeze the source specification and map every paper lemma to a Lean name.
2. Formalize the response function as executable data before proving its cost.
3. Prove realizability and invariant preservation for each transition family.
4. Prove one local potential theorem per transition family.
5. Aggregate local bounds through the generic potential theorem.
6. Prove the terminal lower bound and the all-`n` rounding/padding step.
7. Replace the challenge `sorry` with `Adversary072.Main` and run Comparator.


See also `docs/source-freeze-checklist.md` for the exact handoff contract between the paper proof and the Lean development.
