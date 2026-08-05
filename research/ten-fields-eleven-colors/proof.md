# Ten fields and eleven colors

## Statement

Let `T+(10, 11)` be the worst-case number of rounds needed to identify an
injective length-ten secret over eleven colors. A round first returns the
number of exact matches and then permits one adaptive coordinate-equality
check. The requested bounds are

```text
5 <= T+(10, 11) <= 45.
```

The strengthened proofs below give

```text
7 <= T+(10, 11) <= 28.
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
five. Five rounds are impossible as well, proving the stronger information
lower bound of six.

### Structural improvement to seven

The information count alone stops at six because `22^6 > 11!`. A first-round
adversary argument gives one more round without enumerating strategies.

Fix any legal first guess `q`. Relabeling the eleven colors makes its ten
entries the canonical inclusion of ten colors into eleven. Every derangement
of all eleven colors restricts to a secret with no match against `q`. The
restriction is injective: the omitted image recovers the derangement's
eleventh value. The standard derangement recurrence

```text
D(0) = 1,
D(1) = 0,
D(n + 2) = (n + 1) * (D(n) + D(n + 1))
```

gives

```text
D(11) = 14,684,570.
```

After receiving zero black pegs, the strategy selects one equality check
`y(i) = c`. Among all injective ten-field secrets, at most

```text
10 * 9 * ... * 2 = 10! = 3,628,800
```

have that fixed coordinate value. Therefore the adversary can answer `false`
while retaining at least

```text
14,684,570 - 3,628,800 = 11,055,770
```

secrets. But five more rounds have only

```text
22^5 = 5,153,632
```

transcripts. Thus no six-round strategy can solve that branch, proving
`T+(10, 11) >= 7`.

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
the originally requested `T+(10, 11) <= 45`.

### Hybrid improvement to twenty-eight

The extra checks can be integrated into the classical construction much more
effectively.

#### Phase 1: ten rounds

Write positions as `0, ..., 9` and colors modulo eleven. Query the ten cyclic
codes

```text
q_s(i) = i + s mod 11,    s = 0, ..., 9.
```

If `b_s` is the black count, then the eleven cyclic codes satisfy
`sum_s b_s = 10`; hence the unqueried count `b_10` is known. Moreover,

```text
sum_s s * b_s
  = sum_i (y(i) - i)
  = -omittedColor - 1             (mod 11).
```

Thus the omitted color is known after the tenth black answer. During the first
nine rounds, use the equality checks to test `y(0)` against colors `0, ..., 8`.
If all are false, then after learning the omitted color the tenth check either
distinguishes colors `9` and `10`, or is unnecessary because one of them is
omitted. Hence one coordinate and the omitted color are known after ten
rounds. The remaining nine positions form a permutation of nine known colors.

#### Phase 2: four pipelined binary searches

The `k > n` routine `findNext` from the cited paper identifies one new open
coordinate in at most `ceil(log2 10) = 4` black queries. Pad shorter calls to
four rounds so that every call supplies four equality checks. An *active
index* `j` is known before each call, and the routine returns a coordinate
where the cyclic code `q_j` is correct.

An equality check `y(p) = q_j(p)` is therefore a guard:

- if it is true, coordinate `p` is already identified;
- if it is false, the coming `findNext` call cannot return `p`.

Run three padded calls as follows. The first call identifies a coordinate. In
its last extra check, guard a remaining coordinate `p` against the active
index for the second call. If the guard is false, use three checks in the
second call to test three more possible colors of `p`, then use its last check
as the guard for the third call. Initially `p` has at most eight candidate
colors, because the omitted color and the first identified color are already
excluded. Two further checks in the third call therefore determine `p`.
Any true answer only determines `p` earlier. In all cases, the three black
searches and the equality checks identify at least four distinct coordinates
in twelve rounds.

At most five positions remain. In the last check of the third call, guard a
new position against the active index for a fourth call. The guard plus three
checks in that fourth call determine the guarded position among at most five
colors, while `findNext` determines another distinct position. The fourth
extra check starts resolving the at most three remaining positions.

At most two additional equality-check rounds finish those three positions:
one more check fixes the partially tested position, and one check distinguishes
the final two colors if necessary. The total is

```text
10 + 3 * 4 + 4 + 2 = 28.
```

This proves `T+(10, 11) <= 28` without searching a game tree.

## Lean scope

[`BlackPegExtraCheck/TenFieldsElevenColors.lean`](../../BlackPegExtraCheck/TenFieldsElevenColors.lean)
kernel-checks the 39,916,800-secret cardinality, the 22-outcome transcript
bound, the information bounds of five and six, and the structural
derangement/fiber proof ruling out six-round strategies. The number of
derangements is derived by its recurrence rather than by enumerating secrets.

For the upper bound, Lean checks both the published 44-round arithmetic and
the `10 + 3*4 + 4 + 2 = 28` hybrid allocation. The phase-1 modular identity,
the pipelined use of `findNext`, and the full query construction are proved
mathematically above but are not yet represented as an executable Lean game
strategy. Accordingly, the Lean upper theorem takes the explicitly named
premise `hybridStrategy`; there is no axiom or hidden placeholder.

## Primary source

- M. El Ouali, C. Glazik, V. Sauerland, and A. Srivastav,
  [On the Query Complexity of Black-Peg AB-Mastermind](https://arxiv.org/abs/1611.05907),
  especially Theorem 3 and the `k > n` construction.
