# Ten fields and eleven colors

## Statement

Let `T+(10, 11)` be the worst-case number of rounds needed to identify an
injective length-ten secret over eleven colors. A round first returns the
number of exact matches and then permits one adaptive coordinate-equality
check. The requested bounds are

```text
5 <= T+(10, 11) <= 45.
```

The proofs below actually give the stronger bounds

```text
6 <= T+(10, 11) <= 44.
```

## Lower bound

There are

```text
11 * 10 * ... * 2 = 11! = 39,916,800
```

injective secrets. Every round has eleven possible black counts, from zero to
ten, followed by a Boolean answer, so it has at most 22 outcomes. This remains
true when the equality check is chosen after the black count is revealed: each
of the eleven first-stage branches has at most two second-stage branches.

Pad shorter plays after they solve the secret. A deterministic solver then
maps every secret to a fixed-length transcript. This map must be injective, or
two different secrets would follow the same deterministic path and receive
the same final identification. Consequently a solver using `r` rounds must
satisfy

```text
39,916,800 <= 22^r.
```

Now

```text
22^4 =   234,256 < 39,916,800,
22^5 = 5,153,632 < 39,916,800.
```

Four rounds are therefore impossible, proving the requested lower bound of
five. Five rounds are impossible as well, proving the stronger lower bound of
six.

## Upper bound

El Ouali, Glazik, Sauerland, and Srivastav give a constructive strategy for
classical black-peg AB-Mastermind with `k > n`. Its query count is

```text
(n - 2) * ceil(log2 n) + k + 1.
```

The construction has two phases. First it queries cyclic shifts. Because each
color occurs once in every position over the full shift family, the sum of the
black counts is `n`; this makes one shift response redundant, and because
`k > n` at least one shift has response zero. Second, the zero-response query
supports binary searches for the secret colors in all but two positions. The
last two entries are finished with at most two queries. The cited paper proves
the correctness and the displayed total.

For ten fields and eleven colors, `ceil(log2 10) = 4`, hence

```text
(10 - 2) * 4 + 11 + 1 = 44.
```

The extra-check game may ignore its additional Boolean answer and run exactly
this classical strategy. Therefore `T+(10, 11) <= 44`, which immediately gives
the requested `T+(10, 11) <= 45`.

## Lean scope

[`BlackPegExtraCheck/TenFieldsElevenColors.lean`](../../BlackPegExtraCheck/TenFieldsElevenColors.lean)
kernel-checks the 39,916,800-secret cardinality, the 22-outcome transcript
bound, the lower bounds of five and six, and the arithmetic implication from
the cited constructive strategy's 44-round theorem to the requested 45-round
upper bound. The paper's full multi-phase decision-tree construction is not
reformalized; it appears as the explicitly named premise
`publishedClassicalStrategy`, rather than as an axiom or an unmarked
placeholder.

## Primary source

- M. El Ouali, C. Glazik, V. Sauerland, and A. Srivastav,
  [On the Query Complexity of Black-Peg AB-Mastermind](https://arxiv.org/abs/1611.05907),
  especially Theorem 3 and the `k > n` construction.
