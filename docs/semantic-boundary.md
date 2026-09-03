# Semantic boundary

Lean checks consequences of formal definitions.  A human reviewer must still
check that those definitions describe deterministic comparison sorting.  This
project keeps that review surface deliberately small.

## Standard substrate

* `Item n = Fin n`: the `n` labelled objects being sorted.
* `Ranking n = Equiv.Perm (Fin n)`: a bijection from each item to its rank.
  Thus `π i` means the rank of item `i`.
* `<` on `Fin n`: mathlib's standard strict order on ranks.
* natural numbers: exact comparison counts.
* rational numbers: exact potential certificates.

## Small project-specific interface

* `Query n`: two distinct labelled items.
* `Answer`: either the left item is smaller or the right item is smaller.
* `DecisionTree n`: a finite binary tree whose internal nodes are queries and
  whose leaves output complete rankings.
* `DecisionTree.Correct`: every hidden ranking reaches a leaf outputting that
  exact ranking.
* `DecisionTree.cost`: the root-to-leaf number of comparisons.
* `Strategy n`: a deterministic answer depending on the prior transcript and
  current query.
* `Compatible`: a concrete ranking makes every adversarial answer true.

The theorem `run_matches_compatible_ranking` is the semantic bridge: any
ranking compatible with an adversarial transcript takes the same path through
the ordinary decision tree, reaches the same leaf, and pays the same cost.

The theorem `lower_bound_of_adversary_certificate` then says that a strategy
which (i) always leaves at least one compatible ranking and (ii) forces a long
run against every correct tree yields a genuine worst-case sorting input.

## Rule for adversary-specific machinery

Packets, intervals, tracked points, credits, Hessians, determinants, and stored
history are internal proof devices.  They may not replace the decision-tree
semantics above.  They must be interpreted back into compatible rankings and
must ultimately construct an `AdversaryCertificate`.

## Reviewer checklist

A semantic review need only answer:

1. Does `Ranking` represent all strict total orders of the labelled items?
2. Does `Query.outcome` return the ordinary comparison result?
3. Does `DecisionTree.evaluate` follow the corresponding branch?
4. Does `Correct` express successful sorting on every ranking?
5. Does `cost` count precisely one per internal comparison?
6. Does `run_matches_compatible_ranking` correctly connect adaptive answers to
   a concrete input?

Everything below this boundary is proof checking rather than interpretation.
