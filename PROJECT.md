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
inequalities: more than 92,206 survivors after four zero/false rounds, or more
than 6,370 after five. The explicit obstruction below has prefix counts 199,926
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
exceptional cuts must be counted directly. The corresponding Lean lemmas are in
[`BlackPegExtraCheck/TenFieldsElevenColors.lean`](BlackPegExtraCheck/TenFieldsElevenColors.lean)
and
[`BlackPegExtraCheck/FiveZeroBridge.lean`](BlackPegExtraCheck/FiveZeroBridge.lean);
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
