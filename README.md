# Black-Peg Permutation Mastermind with an Extra Check

This repository studies the adaptive game in
[`source/black_peg_mastermind_extra_check.pdf`](source/black_peg_mastermind_extra_check.pdf):
each round asks a permutation query, receives its number of exact matches, and
then asks one truthful coordinate-equality question.

The verified result is the information-theoretic lower bound. Any deterministic
strategy that solves every secret in at most `T` rounds must satisfy

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
repository deliberately separates the kernel-checked lower bound from open
research directions rather than presenting a conjectural improvement as a
theorem.
