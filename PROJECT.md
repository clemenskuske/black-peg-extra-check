# Black-Peg Permutation Mastermind with an Extra Check

This repository studies the adaptive game in
[`source/black_peg_mastermind_extra_check.pdf`](source/black_peg_mastermind_extra_check.pdf):
each round asks a permutation query, receives its number of exact matches, and
then asks one truthful coordinate-equality question.

The general verified result is the information-theoretic lower bound. Any
deterministic strategy that solves every permutation secret in at most `T`
rounds must satisfy

```text
n! <= (2 * (n + 1))^T.
```

Equivalently, over the reals,

```text
T >= ceil(log(n!) / log(2 * (n + 1))).
```

The full argument, scope, and literature check are in
[`research/proof-notes.md`](research/proof-notes.md). The Lean theorem is
`BlackPegExtraCheck.decisionTreeLowerBound` in
[`BlackPegExtraCheck/DecisionTree.lean`](BlackPegExtraCheck/DecisionTree.lean).

The fixed AB-Mastermind case with ten fields and eleven non-repeating colors is
developed in
[`research/ten-fields-eleven-colors/proof.md`](research/ten-fields-eleven-colors/proof.md).
The lower bound `T+(10, 11) >= 8` is a closed Lean theorem. The file also
derives the source-backed classical upper bound `T+(10,11) <= 44` by ignoring
the extra answer; Lean records that external construction as an explicit
premise.

The claimed fifteen-round cyclic/X-ray proof is not complete. Lean now checks
the ten legal cyclic setup rounds, reconstruction of the missing cyclic count,
identification of one field from the ten equality bits, the legal mixed
queries, the equality-accelerated recurrence `9 -> 4 -> 1`, and their exact
composition into a fifteen-round strategy *conditional only on* the universal
three-round eight-rook separator proposition
`EightRookCylindricalSepThree`. No witness for that proposition is supplied.
The older fourteen-round allocation is now formalized as a conditional
composition from the proposition `NineRookCylindricalSepFour`. A reconstructed
standalone verifier at
[`research/ten-fields-eleven-colors/verify_nine_rook_sep4.cpp`](research/ten-fields-eleven-colors/verify_nine_rook_sep4.cpp)
checks every normalized nine-rook fiber with the legal black-answer-then-
adaptive-equality quantifier order, but its certificates have not yet been
imported into Lean. Therefore the repository still does not claim an
unconditional `T+(10,11) <= 14` theorem.

For the lower-bound direction, the audit also gives a kernel-checked reduction
of a possible ninth-round lower bound to either of two concrete intersection
inequalities: more than 89,036 survivors after four zero/false rounds, or more
than 6,370 after five. The sharper four-round threshold now follows from a
kernel-checked derangement decomposition giving every exact black fiber its
true cap `choose(10,b) * (D(10-b) + D(11-b))`; the older factorial cap gave
92,206. The explicit obstruction below has prefix counts 199,926
and 10,404, respectively, but those computations are not universal proofs.
Both routes now have kernel-checked injections from completed-path perfect
matchings into the real survivor states, reducing them to clean permanent
inequalities.
For the five-round route the project formalizes the safe perfect-matching
bridge, the necessary five-factor cut inequality, the six-regular small-defect
reduction, and an explicit degree-one obstruction showing that a five-factor
cannot simply be assumed. For the denser four-round route it now also proves
the analogous seven-regular/six-factor defect arithmetic: after at most four
deletions, a violated six-factor cut has excess only `1`, `2`, or `3`. A
kernel-checked nonempty four-query/four-check example has one color of degree
three, proving that a universal six-factor shortcut is false and that the
exceptional cuts must be counted directly. A second kernel-checked reduction
shows that the four-path permanent follows if the query-only graph has at
least 276,640 perfect matchings and each checked edge occurs in at most one
sixth of them; the resulting arithmetic clears 89,036. The one-sixth marginal
is now known to be false for the full completed-query class with overlaps: an
exact block-structured four-query example has 1,968,535 query-only matchings,
458,761 of which use one allowed edge. The corresponding seven-regular,
edge-disjoint marginal inequality remains open. A second exact obstruction
shows that the overlap support cannot always be enlarged to a simple
four-regular forbidden graph on the same vertices: four legal query factors
can have support `K_3,3` disjoint from an already saturated four-regular
eight-vertex block. Thus the remaining route must prove a direct aggregate
four-edge inequality, or handle precisely these deficient overlap components
rather than invoking a blanket regular completion. The exact aggregate target
is now kernel-checked: query matchings partition into path survivors and the
union of the four checked-edge events. Hence the weakest remaining condition
is `89036 + |loss union| < |query matchings|`. With the proposed query lower
bound 276,640, the convenient still-sufficient relaxation is
`3|loss union| <= 2|query matchings| + 9529`, allowing 3,176 more losses at the
minimum than the old two-thirds bound. The corresponding Lean
lemmas are in
[`BlackPegExtraCheck/TenFieldsElevenColors.lean`](BlackPegExtraCheck/TenFieldsElevenColors.lean)
and
[`BlackPegExtraCheck/FiveZeroBridge.lean`](BlackPegExtraCheck/FiveZeroBridge.lean);
the exact capacity theorem is in
[`BlackPegExtraCheck/ExactFiberCapacity.lean`](BlackPegExtraCheck/ExactFiberCapacity.lean);
the exact aggregate reduction is in
[`BlackPegExtraCheck/AggregateFourPathBridge.lean`](BlackPegExtraCheck/AggregateFourPathBridge.lean);
the all-four-cycle injection with reverse multiplicity one is in
[`BlackPegExtraCheck/RegularMarginalStructure.lean`](BlackPegExtraCheck/RegularMarginalStructure.lean);
the Hall factorization proving that the edge-disjoint query class is exactly
the full class of simple seven-regular bipartite graphs is in
[`BlackPegExtraCheck/RegularQueryClass.lean`](BlackPegExtraCheck/RegularQueryClass.lean);
the regular-completion obstruction is in
[`BlackPegExtraCheck/RegularCompletionObstruction.lean`](BlackPegExtraCheck/RegularCompletionObstruction.lean);
the cyclic composition is in
[`BlackPegExtraCheck/CyclicStrategy.lean`](BlackPegExtraCheck/CyclicStrategy.lean).

The exact recursive legal separator predicate and a sound executable finite
certificate checker are in
[`BlackPegExtraCheck/Separator.lean`](BlackPegExtraCheck/Separator.lean).
They are infrastructure for the missing eight- and nine-rook endgames. The
86-member sharp eight-rook state has an explicit three-round certificate
kernel-checked in
[`BlackPegExtraCheck/SharpEightRookCertificate.lean`](BlackPegExtraCheck/SharpEightRookCertificate.lean),
but that is one state rather than a universal proof. No all-fiber certificate
is currently supplied, so this does not close a new numerical upper bound.

## Verification

The project is pinned by `lean-toolchain` and `lake-manifest.json`.

```sh
bash scripts/verify.sh
```

The included dev-container performs the same check when a GitHub Codespace is
created. Its setup is idempotent; downloaded dependencies and build artifacts
remain untracked.

## Status

The extra-check variant does not appear in the primary sources surveyed. No
proof closing the current `Omega(n)` versus `O(n log n)` gap was found. For the
fixed `(10,11)` game the currently justified mathematical bounds are therefore
`8 <= T+(10,11) <= 44`; the upper endpoint relies on the cited published
classical construction rather than a Lean strategy term. This repository
separates kernel-checked results, conditional reductions, and open research
directions rather than presenting a conjectural improvement as a theorem.
