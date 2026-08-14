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
premise. A proposed 14-round cyclic/X-ray allocation is also recorded, but its
Lean theorem is conditional on a missing endgame strategy and is not an
executable or closed upper-bound proof. The current audit isolates both that
gap and a kernel-checked reduction of a possible ninth-round lower bound to a
five-fiber intersection inequality. It now also formalizes the safe
perfect-matching bridge, the necessary five-factor cut inequality, the
six-regular small-defect reduction, and an explicit degree-one obstruction
showing that a five-factor cannot simply be assumed. The corresponding Lean
lemmas are in
[`BlackPegExtraCheck/TenFieldsElevenColors.lean`](BlackPegExtraCheck/TenFieldsElevenColors.lean)
and
[`BlackPegExtraCheck/FiveZeroBridge.lean`](BlackPegExtraCheck/FiveZeroBridge.lean).

The exact recursive legal separator predicate and a sound executable finite
certificate checker are in
[`BlackPegExtraCheck/Separator.lean`](BlackPegExtraCheck/Separator.lean).
They are infrastructure for the missing eight- and nine-rook endgames; no
universal separator certificate is currently supplied, so they do not close a
new numerical upper bound by themselves.

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
proof closing the current `Omega(n)` versus `O(n log n)` gap was found. This
repository deliberately separates kernel-checked results, conditional
reductions, and open research directions rather than presenting a conjectural
improvement as a theorem.
