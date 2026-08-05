# Proof notes

## Model and source

The source problem is the one-page brief
[`source/black_peg_mastermind_extra_check.pdf`](../source/black_peg_mastermind_extra_check.pdf).
For `n` positions, the secret and every black-peg query are permutations of
`[n]`. A round returns a black-peg count `b` in `{0, ..., n}`. After seeing
`b`, the strategy may select one pair `(i, j)` and learn whether `pi(i) = j`.

The timing convention matters for strategy design but not for the lower bound
below: after fixing the history, there are at most `n + 1` first-stage answers,
and below each first-stage answer there are at most two second-stage answers.

## Proved lower bound

Fix a deterministic strategy whose worst-case number of rounds is at most `T`.
Pad any shorter successful play to length `T` with arbitrary dummy questions.
Each secret permutation now determines a length-`T` answer transcript.

1. A round has at most `2(n + 1)` possible answer pairs `(b, c)`.
2. Therefore there are at most `[2(n + 1)]^T` padded transcripts.
3. If two different secrets had the same transcript, determinism would make
   the strategy ask the same questions along both plays and return the same
   final identification. It would be wrong for at least one secret.
4. Hence the map from the `n!` secrets to transcripts is injective, so

   ```text
   n! <= [2(n + 1)]^T.
   ```

Because `2(n + 1) > 1`, taking logarithms yields

```text
T >= ceil(log(n!) / log(2(n + 1))).
```

Stirling's formula makes the right-hand side `Omega(n)` (indeed
`n - O(n / log n)`). The Lean development formalizes the finite cardinality
inequality, which is the exact combinatorial content; the real-logarithm
restatement is not needed by the proof kernel.

## Upper bounds

Two valid constructions are currently available.

- Coordinate-check-only fallback: process positions in order and test all but
  one of the still-unused values. A `true` answer fixes the value; if every
  tested value is false, the sole untested value is forced. The last position
  is forced by bijectivity. This takes at most
  `(n - 1) + (n - 2) + ... + 1 = n(n - 1)/2` rounds and ignores black counts.
- Classical inheritance: ignore the extra check and run a deterministic
  black-peg AB-Mastermind strategy. El Ouali, Glazik, Sauerland, and Srivastav
  prove an `O(n log n)` upper bound for the permutation case, which is the
  stronger asymptotic upper bound here.

Thus the justified general bounds are

```text
ceil(log(n!) / log(2(n + 1))) <= T_plus(n) <= O(n log n).
```

## Literature check and open point

The cited paper proves a lower bound of `n` queries and an explicit
`O(n log n)` strategy for the classical black-peg AB/permutation game:

- M. El Ouali, C. Glazik, V. Sauerland, and A. Srivastav,
  [On the Query Complexity of Black-Peg AB-Mastermind](https://arxiv.org/abs/1611.05907),
  arXiv:1611.05907.
- The published version states the same gap and constants:
  [Games 9(1), 2 (2018)](https://doi.org/10.3390/g9010002).

Related primary-source searches found work on static permutation Mastermind and
on the weaker yes/no response model, but no treatment of a black-count round
augmented by one adaptively selected coordinate equality. The one-bit check
does not by itself turn the known classical construction into a linear-round
strategy, and no rigorous `O(n)` construction or stronger adversary bound was
found. Closing the gap should therefore be treated as open work.

Promising directions include quantifying how much an equality bit can improve
the classical binary-search subroutine, and proving a weighted adversary bound
for candidate permutation sets after a count answer. Neither direction is
claimed as a theorem here.

## Lean correspondence

`BlackPegExtraCheck/DecisionTree.lean` uses:

- `Secret n = Equiv.Perm (Fin n)`, whose finite cardinality is `n!`;
- `RoundAnswer n = Fin (n + 1) x Bool`, whose cardinality is `2(n + 1)`;
- `Transcript n T = Fin T -> RoundAnswer n`, whose cardinality is
  `[2(n + 1)]^T`; and
- `Fintype.card_le_of_injective` to conclude the bound from a solving
  transcript encoder.

There are no axioms or placeholders in the proof source.
