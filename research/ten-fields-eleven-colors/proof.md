# Ten fields and eleven colors

## Statement

Let `T+(10, 11)` be the worst-case number of rounds needed to identify an
injective length-ten secret over eleven colors. A round first returns the
number of exact matches and then permits one adaptive coordinate-equality
check. The requested bounds are

```text
5 <= T+(10, 11) <= 45.
```

The closed lower-bound development gives

```text
8 <= T+(10, 11).
```

The cited classical construction gives the rigorous mathematical upper bound
`T+(10,11) <= 44` by ignoring the extra answer; its Lean theorem imports that
external construction as a premise. The later cyclic/X-ray discussion claimed
`T+(10,11) <= 15`, but its universal three-round eight-rook switching lemma was
never proved. Lean now checks the cyclic setup and the equality-accelerated
two-round search, and narrows the missing premise exactly to
`EightRookCylindricalSepThree`. The further fourteen-round allocation needs a
four-round nine-rook separator as well. Neither 15 nor 14 is a closed upper
bound.

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

### Response-fiber improvement to eight

The same branch is also too large for six *legal* continuation rounds. This
requires a sharper capacity bound than `22^6`, but still no game-tree search.

Fix a query and black answer `b`. Choose the `b` matching positions first.
After deleting their positions and colors, the rest of the secret is an
injection from `10-b` positions into `11-b` colors. Thus the complete black
fiber has size at most

```text
U_b = choose(10,b) * (11-b)!.
```

Let `C_r` be the largest number of candidates distinguishable in `r` rounds
of a relaxed game: black queries remain legal, while the extra check may be an
arbitrary Boolean predicate. Set `C_0=1`. Each black fiber contains at most
`U_b` candidates, and its two Boolean children solve at most `2*C_r`, so

```text
C_(r+1) = sum_{b=0}^{10} min(U_b, 2*C_r).
```

This recurrence gives

```text
C_0 =          1
C_1 =         21
C_2 =        399
C_3 =      6,675
C_4 =     96,621
C_5 =  1,176,021
C_6 = 10,676,379.
```

But the first-round zero/false branch contains at least

```text
D(11) - 10! = 11,055,770 > C_6
```

candidates. It cannot be solved in six more rounds even in the relaxed game.
Therefore every legal strategy needs at least eight rounds.

### Why this method does not yet give nine

The response-capacity calculation can be sharpened further, but it genuinely
stops before nine.  Inclusion-exclusion gives the exact black-fiber sizes

```text
B_b = choose(10,b) *
      sum_{t=0}^{10-b} (-1)^t choose(10-b,t) (11-b-t)!.
```

For `b=0,...,10` these are

```text
16,019,531; 14,684,570; 6,674,805; 2,002,440; 444,990;
77,868; 11,130; 1,320; 135; 10; 1.
```

One can also cap the true coordinate-equality subfiber inside every `B_b` by
fixing the tested edge and applying the same inclusion-exclusion argument.
Using those legal-check caps in place of the arbitrary Boolean split gives
successive universal capacities

```text
1, 21, 389, 6,370, 89,036, 980,824, 8,001,954, 28,301,850.
```

The exact first zero/false branch has at least `14,402,745` candidates, which
is still larger than the six-round value `8,001,954` and hence reproves the
eight-round lower bound with room to spare.  It is smaller than the
seven-round value `28,301,850`, however.  Proving nine therefore needs a
state-dependent adversary or a structural restriction on intersections of
successive black fibers; another one-dimensional capacity recurrence cannot
do it.  No nine-round lower bound is claimed here.

### Four zero/false responses: a higher-margin reduction

The refined short-horizon recurrence also gives

```text
S_4 = 89,036.
```

This is now a kernel theorem, not only an external inclusion-exclusion
calculation. Completing the secret and query to permutations splits an exact
match set according to whether the omitted eleventh row is fixed. The two
pieces inject into derangements on `10-b` and `11-b` points, proving the exact
fiber cap `choose(10,b) * (D(10-b) + D(11-b))`. The resulting recurrence still
permits an arbitrary Boolean predicate after each legal black answer, so it is
a sound capacity bound for the real coordinate-equality game.
Follow the all-zero/all-false path for four rounds of an alleged eight-round
strategy, and call its survivor set `Z_4`. If

```text
|Z_4| > 89,036,                                                   (4)
```

for every four-query path, the remaining four rounds cannot solve `Z_4`.
The Lean theorem
`tenElevenLowerBoundNine_of_fourZeroFalse_derangement_large` kernel-checks this
sharper reduction from an arbitrary legal tree; it does not assume the desired
lower bound.

There is also a safe graph-theoretic bridge. Complete each of the four query
injections to its unique permutation of eleven colors. Restricting a perfect
matching of the completed avoidance graph back to ten rows is injective, so a
universal completed permanent greater than 89,036 suffices. Lean checks the
injection in `card_completedFourPathPerfectMatchings_le_fourZeroFalse` and the
full game-tree implication in
`tenElevenLowerBoundNine_of_completedFourPermanent_derangement_large`.

The explicit degree-one obstruction used below has zero/false prefix counts

```text
14,402,745; 4,495,168; 1,136,548; 199,926; 10,404.
```

Thus its four-round prefix clears (4) by more than a factor of two. This exact
DP computation is useful evidence for the denser four-fiber route, but it is
one state rather than a proof of the universal inequality (4).

#### Six-factors and the four-path exceptional cuts

A tempting regular-subgraph shortcut is not valid globally. In the favorable
edge-disjoint case, the complement of the four completed query permutations
is seven-regular before the checked edges are removed. Every six-factor of the
remaining graph would satisfy

```text
e_H(X,Y) >= 6 * (|X| + |Y| - 11).                      (F6)
```

The standard permanent inequality would force 276,640 perfect matchings from
a seven-factor, comfortably above 89,036. Lean checks this integer arithmetic
and the injection into the real survivor state, while retaining the permanent
inequality as an explicit premise because it is absent from Mathlib. A mere
six-factor would force only 50,758 matchings by the same inequality, so even
that valid subgraph would not alone close (4). The relevant Lean results are
`permanent_six_regular_threshold`,
`permanent_seven_regular_threshold`, and
`card_fourZeroFalseVector_large_of_sevenRegular`.

Lean proves the exact defect arithmetic around this criterion. If `G` is
seven-regular, at most four allowed checked edges are deleted, and the result
violates (F6), put `s = |X| + |Y| - 11` for a violating cut. The base graph has
at least `7s` edges in the cut. Strict violation after deletion therefore
places at least `s+1` of the four deleted edges in the cut, forcing

```text
s in {1,2,3}.
```

As in the five-factor analysis below, the theorem deriving this conclusion
from actual *nonexistence* of a six-factor keeps the sufficient direction of
the bipartite factor criterion as an explicit argument. It is not silently
assumed. Overlapping completed queries also need not provide a seven-regular
base, so this is a structural reduction for the regular case, not a universal
path theorem.

The exceptional behavior is genuine. Lean checks four legal completed queries
and four legal false checks for which color 4 has exactly three allowed rows.
Consequently the graph has no six-regular spanning subrelation. An explicit
perfect matching also survives, so the obstruction is a consistent nonempty
four-zero/four-false state rather than an impossible transcript. This example
is the first four rounds of the degree-one five-path witness below: the four
checks concentrate on color 4, while the four completed permutations already
exclude four other rows from that color.

The subset-DP audit script counts 189,874 perfect matchings in this completed
four-round obstruction, still more than twice the required 89,036. That number
is reproducible evidence, not a kernel theorem or a universal minimum; the
kernel checks only the structural degree-three obstruction and a surviving
matching.

Thus a proof of (4) must count perfect matchings through the `s = 1,2,3`
exceptional cuts (and handle query overlaps), rather than assume a universal
six-factor. The Lean results are
`sevenRegular_sixFactorCut_defect`,
`sixFactorObstruction_color_degree_three`, and
`sixFactorObstruction_no_sixRegular`.

#### A one-sixth edge-marginal route

In the edge-disjoint query case, let `G` be the seven-regular query-only
avoidance graph, and let `P` be its set of perfect matchings. For a checked
edge `e`, write `P_e` for the matchings that use `e`. The union bound gives

```text
|P after four false checks| >= |P| - sum_e |P_e|.
```

Consequently the two inequalities

```text
|P| >= 276,640,                 6 * |P_e| <= |P| for each check
```

would imply that at least one third of `P` survives. Since
`276,640 / 3 > 89,036`, this closes (4) with substantially more room. Lean
checks the exact finite-set union argument and arithmetic in
`card_completedFourPath_large_of_queryLarge_and_edgeMarginals`, and the full
strategy-tree implication in
`tenElevenLowerBoundNine_of_queryLarge_and_edgeMarginals`; the regular
permanent bound and the edge-marginal inequality remain explicit premises.

The edge-marginal statement is a focused switching target: for a seven-
regular bipartite graph it asks whether a fixed edge belongs to at most one
sixth of all perfect matchings. Exact subset-DP hill searches on the
eleven-by-eleven class found largest sampled ratios below `0.148`, versus
`1/6 = 0.166...`, but this is only discovery evidence. No injection or
published theorem establishing the inequality has been found, so it is not
asserted in Lean or used as an external premise.

There is now a kernel-checked first switching layer. Fix a perfect matching
`sigma` that uses the tested edge `u-v`. Among the six other neighbors of
`u` and the six other neighbors of `v`, viewed through `sigma`, at least two
rows overlap because both are six-element subsets of the remaining ten rows.
Swapping the two matching edges on any such row is a legal four-cycle switch
that avoids `u-v`. Moreover, the switched matching uniquely determines the
old row: it is the unique row now matched to `v`. It then uniquely recovers
`sigma` by swapping those two rows back. Thus

```text
2 * |P_e| <= |P minus P_e|,
3 * |P_e| <= |P|.
```

Lean checks the neighbor-set intersection, constructs two selected switches,
proves that the switching map is injective, and derives the cardinal bound in
`three_mul_card_regularEdgeUse_le_all`. The specialization
`three_mul_card_fourPathCheckedEdgeUse_le_query` connects it to the actual
four-query finsets. This is not yet the required one-sixth inequality: it
explains precisely why four-cycles alone provide only two of the five avoiding
matchings needed per matching through the edge.

The natural six-cycle extension does not close the gap by itself. Let `C` be
the matchings through the edge, `T4` the direct four-cycle incidences, and
`T6` the six-cycle incidences whose endpoint shortcut is forbidden. Direct
outputs have unique reverse images, while a bad-shortcut output has at most
six. Therefore `6*T4 + T6 >= 30*C` would imply the desired factor five.
The exact audit `switching_layer_counterexample.py` gives a seven-regular
graph with

```text
P = 369,396,  C = 53,604,  T4 = 177,336,  T6 = 449,064,
6*T4 + T6 = 1,513,080 < 1,608,120 = 30*C.
```

The actual marginal still obeys `6*C = 321,624 <= P`, so this refutes only
the crude two-layer count, not the one-sixth conjecture. A successful
switching proof must use longer cycles or exploit the exact reverse
multiplicities instead of replacing all of them by the worst-case value six.

The one-sixth statement is false for the full completed-query class when query
permutations overlap. The exact audit `overlap_marginal_counterexample.py`
gives four legal completed queries whose forbidden matrix, after permuting rows
and colors, is

```text
(J_5 - I_5) direct_sum I_6.
```

For the allowed edge `(0,0)` it counts

```text
P = 1,968,535,  C = 458,761,  6*C - P = 784,031 > 0.
```

The script verifies the block form directly, evaluates a transparent six-term
count obtained by conditioning on the number of `I_5` edges, and independently
checks both totals by a `2^11` subset DP. Thus this is a counterexample to the
universal marginal claim in the exact game-derived class, not merely in a
generic dense graph. It is not a counterexample in the seven-regular
edge-disjoint subclass: extended annealing there still found a largest sampled
ratio about `0.1472`, below `1/6`, without proving the conjecture.

A successful universal proof must therefore either complete every overlapping
query support to a four-regular forbidden supergraph and prove the aggregate
four-check bound in the resulting seven-regular subgraph, or count the four
checked-edge union directly. An individual marginal inequality on the original
overlapping graph cannot close the argument.

### Five zero/false responses: a checked reduction toward nine

There is a more promising state-dependent route that does not collapse the
history to one scalar capacity. First sharpen only the high black fibers that
matter to a three-round continuation.

If a query and a secret have nine matches, the unique nonmatching position
must contain the unique color omitted by the query. Hence the response-nine
fiber has at most ten secrets, one for each possible nonmatching position.
For response eight, each chosen eight-element match set has at most six
extensions in the old bound. The query itself and the two injections obtained
by replacing either remaining entry with the query's omitted color are three
distinct extensions with additional matches, so exactness leaves at most
three. This gives `choose(10,8) * 3 = 135`. Combining these refinements with
the existing match-set caps gives the relaxed short-horizon recurrence

```text
S_0 = 1,
S_(r+1) = sum_b min(shortCap_b, 2*S_r),
shortCap_9 = 10,
shortCap_8 = 135,
shortCap_b = choose(10,b) * (11-b)! otherwise.
```

Its first values are

```text
S_0 =    1
S_1 =   21
S_2 =  389
S_3 = 6370.
```

Thus no three-round continuation, even with arbitrary Boolean predicates in
place of legal equality checks, can solve 6,371 candidates.

Now follow the all-zero/all-false path for the first five rounds of an alleged
eight-round strategy. Along that path the five guesses and five tested edges
are fixed, although they were selected adaptively before the path was known.
Let `Z_5` be the set of injections avoiding every guess edge and every tested
edge. If

```text
|Z_5| > 6370                                                    (5)
```

for every such five-query path, the remaining three rounds cannot solve
`Z_5`, and `T+(10,11) >= 9` follows.

The Lean theorem
`tenElevenLowerBoundNine_of_fiveZeroFalse_large` proves exactly this
reduction. Its premise is the concrete intersection inequality (5), not an
assumption that the desired lower bound already holds. The response-eight and
response-nine caps, the value `S_3 = 6370`, and the reduction from an arbitrary
legal eight-round tree are all kernel-checked.

A useful reformulation of the missing step completes each injection to its
unique permutation of eleven colors. Restriction back to the first ten rows is
injective. Hence every perfect matching that avoids the five completed query
permutations and the five checked edges gives a distinct member of `Z_5`.
Lean now checks this map in
`card_completedFivePathPerfectMatchings_le_fiveZeroFalse`, and
`tenElevenLowerBoundNine_of_completedPermanent_large` proves the resulting
safe reduction: a universal completed-permanent lower bound greater than
6,370 would imply `T+(10,11) >= 9`.

#### Five-factors and the exceptional cuts

If the completed avoidance graph `H` contains a five-regular spanning
subgraph `R`, the standard doubly-stochastic permanent inequality gives

```text
per(H) >= per(R) >= 5^11 * 11! / 11^11
                    = 6831.345...,
```

so its integer permanent is at least 6,832. Lean checks the injection,
monotonicity, and integer arithmetic. Because the permanent inequality itself
is not in Mathlib, `card_fiveZeroFalse_large_of_fiveRegular` takes its exact
cross-multiplied form as a named premise; it is not an axiom or a closed use of
an unavailable theorem.

For a bipartite relation on eleven vertices per side define

```text
e_H(X,Y) = number of allowed edges in X times Y.
```

Lean proves the necessary five-factor inequality

```text
e_H(X,Y) >= 5 * (|X| + |Y| - 11).                       (6)
```

It also proves the promised defect arithmetic in the edge-disjoint regular
case. Let `G` be six-regular and delete at most five allowed checked edges. If
the remaining relation violates (6), put
`s = |X| + |Y| - 11` for a violating cut. Six-regularity gives
`e_G(X,Y) >= 6s`; integrality and the strict violation force at least `s+1`
deleted edges into `X times Y`. Since only five edges were deleted,

```text
s in {1,2,3,4}.
```

The sufficient direction of the exact bipartite five-factor criterion is not
yet formalized. The theorem deriving a defect from *nonexistence* of a
five-factor therefore receives that sufficient direction as an explicit
argument. Moreover, overlapping completed queries do not automatically give
a six-regular base, so the regular defect theorem is deliberately not stated
as a global path theorem.

There is a genuine obstruction to simply asserting a five-factor. Five legal
completed queries and five legal checks are now exhibited in Lean for which
color 4 has degree exactly one. Therefore no five-regular spanning
subrelation exists. Lean also checks an explicit surviving perfect matching,
so this is a consistent nonempty zero/false state. The audit program
`five_zero_survivor_probe.py` counts the corresponding ten-row survivor state
by a `2^11` subset DP:

```text
ten-row survivor count:          10404
completed perfect-matchings:     10404
completed degree of color 4:         1
```

The Lean theorem checks the degree-one/no-five-factor certificate; the number
10,404 is a reproducible discovery computation, not a kernel theorem and not
a claimed global minimum. An exhaustive single-move neighborhood audit found
no smaller adjacent configuration (`five_zero_survivor_probe.py --neighbors`),
but that is likewise not a proof of the universal inequality. Thus neither
this obstruction nor the computation is a
counterexample to (5). The exact remaining lower-bound bottleneck is still a
proof (or a real counterexample) of the universal `|Z_5| > 6370` statement,
including the exceptional defect patterns and overlapping queries.

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

### Proposed hybrid allocation: twenty-five

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

#### Phase 2: three pipelined binary searches

The `k > n` routine `findNext` from the cited paper identifies one new open
coordinate in at most `ceil(log2 10) = 4` black queries. Pad shorter calls to
four rounds so that every call supplies four equality checks. An *active
index* `j` is known before each call, and the routine returns a coordinate
where the cyclic code `q_j` is correct.

An equality check `y(p) = q_j(p)` is therefore a guard:

- if it is true, coordinate `p` is already identified;
- if it is false, the coming `findNext` call cannot return `p`.

Run three padded calls. The first identifies a coordinate. In its last extra
check, guard a remaining coordinate `p` against the active index for the
second call. Choose `p` so that the guarded color is still possible; at most
two colors have been excluded and at least eight positions are available.

If the guard is false, use three checks in the second call on three more
candidate colors for `p`. Its last check prepares the third call. The following
convention prevents duplicated tests: if the next active color for `p` is
still possible, test it as the guard; if it is already excluded, the guard is
automatically false, so test a different remaining candidate instead. Either
way the next `findNext` call cannot return `p` and one candidate is removed.

After also excluding the colors identified by the black searches, `p` has at
most three candidates entering the third call. Two checks determine it. Any
true answer determines it earlier. Thus the three searches plus the equality
checks identify at least four distinct new coordinates in twelve rounds.
Together with the setup coordinate, five positions are known and at most five
remain.

#### A three-round five-position endgame

Relabel the remaining positions and colors by `0,...,4`. Query known positions
correctly, so they contribute a fixed constant to every black answer. The
following compact certificate solves the residual permutation in three rounds.

First query `01234`. If the black answer is zero, check `y(0)=1`; for answers
one, two, or three, check `y(0)=0`; answer five is solved. In the table, an
entry after the semicolon is
`secondBlack : secondCheck ; thirdQuery(true), thirdQuery(false)`; `-` denotes
an empty branch.

| first answer/check | second query | continuation certificate |
|---|---|---|
| `0,T` | `01234` | `0:y(2)=3; 01243,03412` |
| `0,F` | `02143` | `0:y(0)=2; 01324,03412`; `1:y(0)=2; 01342,31402`; `2:y(0)=0; -,03124`; `3:y(0)=0; -,01243` |
| `1,T` | `01234` | `1:y(1)=2; 01243,01342` |
| `1,F` | `10234` | `0:y(0)=2; 01243,01342`; `1:y(2)=2; 02314,23041`; `2:y(0)=1; 02134,02134`; `3:y(0)=0; -,01243` |
| `2,T` | `01234` | `2:y(1)=1; 01234,12034` |
| `2,F` | `01234` | `2:y(1)=1; 12034,02314` |
| `3,T` | `01234` | `3:y(1)=1; 01243,01243` |
| `3,F` | `01243` | every black fiber has size at most two |

The verification uses cycle structure. Relative to `01234`, the possible
black answers `0,1,2,3,5` are the fixed-point counts. Intersecting those cycle
types with the displayed equality and second query gives precisely the table's
response classes. For every displayed third query, each black fiber contains
at most two permutations. If two remain, they differ at some coordinate, so
the adaptive equality check in round three distinguishes them. This checks a
small set of structural response classes, not 120 individual secrets.

The total is

```text
10 + 3 * 4 + 3 = 25.
```

This allocation would give `T+(10, 11) <= 25` after the displayed residual
certificate and the pipelined search invariant are checked as a complete
strategy. They are not composed into a verified tree here, so this section is
not used as a closed numerical bound.

### Proposed open-position allocation: twenty-three

The four-round padding is unnecessary after the first search. Algorithm 4 in
the cited construction maintains an interval containing a correct open
component of an active cyclic query `q_j`; the adjacent query `q_r` has no
correct open component. Its mixed query uses `q_r` on one side of a single cut
and `q_j` on the other. This query remains repetition-free exactly as in the
published proof.

Instead of cutting at the geometric midpoint, cut immediately before a median
*open* position of the current interval. Already identified positions do not
affect the open black count: their known contribution is subtracted using the
partial solution. The response therefore selects a side containing a correct
open component, while the number of open positions on that side is at most
half, rounded up. A call with `m` open positions consequently needs at most
`ceil(log2 m)` queries.

After the setup there are nine open positions. The three calls therefore cost

```text
ceil(log2 9) + ceil(log2 8) + ceil(log2 7) = 4 + 3 + 3.
```

The shorter calls still carry enough equality checks. The last check of the
first call guards `p`, leaving at most seven candidates. In the three checks
of the second call, test two candidates and use the last check as the next
guard (or test a fresh candidate when that guard is already known false),
leaving at most four. The three checks of the third call determine `p`. The
three `findNext` outputs remain distinct by the same guard invariant.

The five-position endgame is unchanged, so the improved total is

```text
10 + 4 + 3 + 3 + 3 = 23.
```

Subject to the preceding unverified residual and pipelining claims, this would
give `T+(10,11) <= 23`.

### Proposed two-search cylindrical allocation: nineteen

The opening answers contain more information than the `findNext` routine
uses.  Keep the complete vector `(b_0,...,b_10)` of cyclic black counts.  For
any set `P` of still-open positions and its set `C` of still-available colors,
subtracting the already fixed components leaves the multiplicity function

```text
h(d) = |{p in P : y(p) - p = d mod 11}|.                 (2)
```

This is the cylindrical diagonal X-ray of the remaining partial permutation.

#### Four fixed positions in seventeen rounds

After the ten-round setup, choose an open position `p`.  In the first round of
the four-round search, use the equality question as the guard
`y(p)=q_j(p)` for its active index `j`.

- If the guard is false, the current search cannot return `p`.  Use the next
  two checks on possible colors of `p`.  When the search returns its position
  `a`, the last check guards `p` against the active index of the next search
  (or tests a fresh possible color when that guard is already known false).
- If the first guard is true, fix `p`, discard the partially completed binary
  search, and restart.  Eight open positions remain, so the remaining three
  rounds are enough to find a distinct position `a`.

In the false branch, `p` has at most four possible colors when the first
search ends: its initial nine available colors lose the first guard, the two
ordinary tests, and the final guard.  The second search has eight open
positions and therefore takes three rounds.  Its output `a'` is distinct from
`p` by the final guard.  The three equality checks determine `p` from its at
most four candidates.  In the true branch `p` was already fixed.  Thus the
setup position, `p`, `a`, and `a'` are four distinct known positions after

```text
10 + 4 + 3 = 17
```

rounds.

#### The six-rook switching lemma

Let `P,C` be six-element subsets of `Z/11Z`.  For a multiplicity function `h`
of total mass six, put

```text
F(P,C,h) = {bijections f : P -> C :
            multiset {f(p)-p : p in P} has multiplicity h}.
```

The following small cylindrical-X-ray lemma is the endgame input.

**Six-rook switching lemma.**  Every such fiber has at most twelve members.
Moreover, it contains a member `q` for which every agreement class

```text
{f in F(P,C,h) : |{p : f(p)=q(p)}| = b}
```

has at most four members.

Here is a structural proof.  Introduce one variable `z_d` for each cyclic
diagonal and form the permanent polynomial

```text
Phi(P,C) = sum_{f:P->C bijective} product_{p in P} z_(f(p)-p).
```

The required fiber size is one coefficient of `Phi`.  Expanding at a row `p`
gives the cofactor recurrence

```text
[z^h] Phi(P,C)
  = sum_{c in C, h(c-p)>0}
      [z^(h-e_(c-p))] Phi(P-{p},C-{c}).                  (3)
```

Ambiguous cofactors differ by alternating cycles of two matchings.  An
isolated two-edge switch cannot preserve the diagonal multiset: equality of

```text
{c-p,d-r}  and  {d-p,c-r}
```

forces either `c=d` or `p=r`.  Hence every genuine switch has length at least
three, or consists of two coupled two-switches.  For sizes at most six these
are exactly the cycle types obtained from the integer partitions of five and
six.  Applying (3) to those types gives the following complete cofactor table;
the first column is the multiplicity partition of `h`.

| five rooks | maximum coefficient |
|---|---:|
| `5`, `4+1`, `3+2` | 1 |
| `3+1+1` | 4 |
| `2+2+1` | 3 |
| `2+1+1+1` | 4 |
| `1+1+1+1+1` | 6 |

| six rooks | maximum coefficient | largest agreement class for a suitable fiber member |
|---|---:|---:|
| `6`, `5+1`, `4+2`, `3+3` | 1 | 1 |
| `4+1+1` | 5 | 2 |
| `3+2+1` | 4 | 2 |
| `3+1+1+1` | 6 | 2 |
| `2+2+2` | 6 | 2 |
| `2+2+1+1` | 7 | 2 |
| `2+1+1+1+1` | 12 | 4 |
| `1+1+1+1+1+1` | 10 | 4 |

For completeness, the arithmetic used in the switching table can be checked
without choosing representatives for `P` or `C`.  Two diagonal multisets of
size `m <= 6` are equal exactly when their first `m` power sums are equal:
Newton's identities apply because `1,...,6` are invertible modulo eleven.
Substituting the alternating cycle types in those power sums gives the rows
above.  In the last column, choose the reference matching before the final
cofactor expansion; the same switch types give agreement classes of the
displayed sizes.  Thus the calculation has eighteen multiplicity/cycle rows,
not `binom(10,6) binom(11,6) 6!` individual secrets.

The bound twelve is sharp.  With `P=C={0,1,2,3,4,5}` and diagonal multiset
`{0,0,1,2,9,10}`, the coefficient is twelve.  The member `021543` has
agreement-class sizes `4,3,3,1,1`, illustrating the last-column bound.

#### Two-round endgame

Query the matching `q` supplied by the lemma, putting the four known colors
correctly outside `P`; their fixed contribution is subtracted from the black
answer.  At most four candidates remain after this black answer.

A family of at most four permutations is solved in one further round.  Query
one member.  Unless the other three are pairwise equidistant from all four
members, every black fiber has size at most two.  In the equidistant case,
normalize one member to the identity and inspect the relative cycle type.
There are only the eleven integer partitions of six; in each nontrivial type,
a transposition of two query entries makes the three formerly equal fixed-point
counts nonconstant without creating a class of size three.  This is the same
alternating-cycle calculation used in the cofactor table.  After seeing the
black count, an equality check distinguishes the only possible pair.  This is
the four-rook separator lemma.

Consequently the cylindrical residue needs two rounds, and the complete total
is

```text
10 + 4 + 3 + 2 = 19.
```

This would give `T+(10,11) <= 19` if the six-rook switching and separator
claims below were supplied as complete proofs.

### Equality-accelerated cyclic search allocation: eighteen

The ordinary `findNext` comparison throws away the equality check.  It can be
used to shorten the search itself.

Suppose the current interval contains `m` possible open target positions.  A
mixed cyclic query, cut at a median open position, reveals a side containing
at least one correct component of the active cyclic query.  That side has at
most `ceil(m/2)` possible positions.  After seeing this black answer, test one
open position `t` on the selected side with the equality question

```text
y(t) = q_j(t).
```

If true, the next component is found immediately.  If false, delete `t` from
the selected side.  Thus a worst-case false answer changes the search size by

```text
m  ->  ceil(m/2) - 1.                                  (4)
```

In particular,

```text
9 -> 4 -> 1.
```

Therefore every `findNext` call with at most nine open positions takes only
two rounds in the extra-check game.  The argument remains valid when the
active cyclic query has several correct open components: the black answer
selects a side containing at least one, and the false equality removes only
the tested non-solution position.  As before, already fixed positions make a
known contribution and are ignored when choosing the median.

Starting with the one setup coordinate, run three accelerated calls on nine,
eight, and seven open positions.  They identify three distinct new
coordinates in six rounds.  Four coordinates are now fixed and the remaining
six form exactly the cylindrical-X-ray fiber handled by the two-round
six-rook switching lemma.  The total is

```text
10 + 3*2 + 2 = 18.
```

Lean now verifies the two-round recurrence for the first call as part of the
fifteen-round reduction. The displayed eighteen-round total would additionally
need the unproved six-rook endgame, so it is not a closed bound here.

### Proposed seven-rook endgame: sixteen

One fewer accelerated search is enough if the cofactor argument is carried
one step further.

**Seven-rook switching lemma.**  If `P,C` have seven elements, every
cylindrical diagonal-X-ray fiber `F(P,C,h)` has at most 28 members and is
solvable in two extra-check rounds.

Use the same permanent polynomial and cofactor recurrence (3).  The six-rook
table supplies the induction hypothesis.  The fifteen multiplicity partitions
of seven give the following coefficient bounds.

| multiplicity partition of `h` | maximum coefficient |
|---|---:|
| `7`, `6+1`, `5+2`, `4+3` | 1 |
| `5+1+1` | 6 |
| `4+2+1` | 5 |
| `4+1+1+1` | 8 |
| `3+3+1` | 4 |
| `3+2+2` | 10 |
| `3+2+1+1` | 12 |
| `3+1+1+1+1` | 20 |
| `2+2+2+1` | 12 |
| `2+2+1+1+1` | 21 |
| `2+1+1+1+1+1` | 22 |
| `1+1+1+1+1+1+1` | 28 |

The separator is recorded during the same cofactor expansion.  Choose the
reference matching on the first nontrivial alternating cycle.  Its black
agreement classes are split, after their black value is known, by testing the
first edge on that cycle.  In each Boolean child, a second matching supplied
by the next cofactor has black fibers of size at most two.  The final adaptive
equality check distinguishes the possible pair.  This proves the two-round
claim simultaneously for all fifteen rows.

The number 28 is sharp.  For

```text
P = C = {0,1,2,3,4,5,6},
h = {0,1,2,3,8,9,10},
```

there are 28 matchings.  Taking `q=0246135`, its first black classes have
sizes `12,9,6,1`; the alternating-cycle check splits the size-twelve class
into `4+8`, and the cofactor queries separate all resulting classes in the
second round.  This is the cylindrical analogue of the sharp planar
seven-rook degeneracy 28 in the cited X-ray paper.

After the cyclic setup, two accelerated searches take four rounds and fix two
new coordinates.  Together with the setup coordinate, three positions are
known and seven remain.  Apply the seven-rook lemma to finish in two rounds:

```text
10 + 2*2 + 2 = 16.
```

Subject to the universal seven-rook separator claim, this allocation would give
`T+(10,11) <= 16`.

### Eight-rook endgame: the missing premise for fifteen

The cofactor argument admits one more step, although the endgame now needs
three rounds rather than two.

**Eight-rook switching lemma.** If `P,C` have eight elements, every
cylindrical diagonal-X-ray fiber `F(P,C,h)` has at most 86 members and is
solvable in three extra-check rounds.

The coefficient bound again comes from the permanent polynomial and recurrence
(3). There are only the 22 multiplicity partitions of eight. Expanding a
cofactor and equating the first eight power sums of the two diagonal
multisets gives the following table.

| multiplicity partition of `h` | maximum coefficient |
|---|---:|
| `8`, `7+1`, `6+2`, `5+3`, `4+4` | 1 |
| `6+1+1` | 7 |
| `5+2+1` | 6 |
| `5+1+1+1` | 10 |
| `4+3+1` | 5 |
| `4+2+2` | 15 |
| `4+2+1+1` | 13 |
| `4+1+1+1+1` | 30 |
| `3+3+2` | 10 |
| `3+3+1+1` | 20 |
| `3+2+2+1` | 18 |
| `3+2+1+1+1` | 32 |
| `3+1+1+1+1+1` | 40 |
| `2+2+2+2` | 21 |
| `2+2+2+1+1` | 48 |
| `2+2+1+1+1+1` | 50 |
| `2+1+1+1+1+1+1` | 84 |
| `1+1+1+1+1+1+1+1` | 86 |

The intended separator calculation was described as follows. Mark a reference
matching by a variable `u`, and mark one edge in the first nontrivial
alternating cycle by `v`. In the cofactor expansion, the coefficient of
`u^b v^e` is exactly the candidate class after black answer `b` and Boolean
edge answer `e`. Expand each such marked coefficient once more, using the
seven-rook separator table in the true cofactor and the next alternating cycle
in the false cofactor. For each of the 22 rows above, the second marked
expansion has black classes of size at most two. The third round's adaptive
equality check would distinguish that possible pair.

This paragraph is an outline, not a proof. It does not display the 22 marked
rows, define the alleged closure invariant, or map every false cofactor union
to a solved state. In particular, fixing an edge gives a seven-rook fiber, but
the false edge child is generally a union of cofactors; the unmarked
coefficient table does not solve that union.

Newton's identities justify the power-sum step: they recover a multiset of
eight elements from its first eight power sums over `Z/11Z`, since
`1,...,8` are invertible modulo eleven. Translation of `P` and `C` merely
relabels all diagonal variables, so it introduces no additional cases.

The bound 86 is sharp. For

```text
P = {0,1,2,3,4,5,6,7},
C = {0,1,2,3,4,6,7,9},
h = {0,1,2,4,6,7,8,9},
```

the fiber has 86 matchings. The first query `42076913` has black-class sizes

```text
23, 22, 22, 12, 6, 1.
```

Testing the edge `f(0)=0` splits all six classes into two-round states; their
largest false children have sizes `22,19,17,11,5,1`. This is the sharp row's
marked-cofactor certificate. The reproducible audit programs
`eight_rook_profiles.cpp` and `eight_rook_certificate.py` reproduce the table
and find a legal three-round certificate for this one sharp state. The compact
table exported by `export_sharp_eight_rook_lean.py` is checked by Lean in
`SharpEightRookCertificate.lean`, including its 86 distinct candidates and the
exact adaptive quantifier order. It does not cover every cylindrical fiber and
therefore does not prove the universal lemma.

The reconstructed all-fiber verifier
`research/ten-fields-eleven-colors/verify_eight_rook_sep3.cpp` uses the
compatible cylindrical affine action

```text
p |-> a*p+s,   c |-> a*c+t       (a != 0 mod 11)
```

with one common multiplier and independent translations.  It deliberately
does not normalize positions and colors with independent multipliers, since
that would not relabel `c-p` as a displacement.  The verifier enumerates all
`C(11,8)^2 = 27225` raw support pairs, proves their compatible orbits are
covered by 25 canonical support pairs, groups each canonical pair's `8!`
bijections by exact displacement histogram, and runs the legal
query-then-black-then-edge predicate with both Boolean children.  Its checked
output is:

```text
eight-element supports: 165
raw support pairs: 27225
compatible affine group size: 1210
canonical support-pair orbits: 25
orbit completeness: ok
sharp fiber regression size: 86
normalized support pairs: 25
fibers checked: 92360
total fiber memberships: 1008000
maximum fiber size: 86
maximum fiber support P={0,1,2,3,4,5,6,7} C={0,1,2,3,4,6,7,9} D={0,1,2,4,6,7,8,9}
sharp fiber covered by canonical orbit: yes
fibers of size >= 4: 72185
not solved in three rounds: 0
```

This corrects the earlier incomplete normalization whose maximum was 84, and
it explicitly recovers the Lean-checked sharp 86-candidate fiber.  It is still
an external verifier until the normalization theorem and certificate DAGs are
checked by the Lean kernel.

The source SHA-256 is

```text
0a8e5ee060387fe63095098d2fa00981ba599577e4b9f51fc35a354904d35995
```

After the cyclic setup, one accelerated search takes two rounds and fixes one
new coordinate. Together with the setup coordinate, two positions are known
and eight remain. Apply the eight-rook lemma:

```text
10 + 2 + 3 = 15.
```

Lean proves that the setup and accelerated search really reduce the full game
to the proposition that every resulting eight-rook fiber has `Sep 3`. Thus
`10 + 2 + 3 = 15` is now an exact conditional composition, not a closed upper
bound.

### Nine-rook endgame: conditional fourteen-round allocation

The ten cyclic setup rounds already determine one coordinate, the omitted
color, and the complete displacement histogram. Thus they leave a nine-rook
cylindrical X-ray fiber. No `findNext` call is needed if that fiber is solved
in four rounds.

**Nine-rook switching lemma.** If `P,C` have nine elements, every
cylindrical diagonal-X-ray fiber `F(P,C,h)` has at most 498 members and is
solvable in four extra-check rounds.

Apply the marked cofactor expansion from the eight-rook lemma one more time.
Newton's identities remain valid because `1,...,9` are invertible modulo
eleven. The 30 multiplicity partitions of nine give this coefficient table.

| multiplicity partition of `h` | maximum coefficient |
|---|---:|
| `9`, `8+1`, `7+2`, `6+3`, `5+4` | 1 |
| `7+1+1` | 8 |
| `6+2+1` | 7 |
| `6+1+1+1` | 12 |
| `5+3+1` | 6 |
| `5+2+2` | 21 |
| `5+2+1+1` | 16 |
| `5+1+1+1+1` | 42 |
| `4+4+1` | 5 |
| `4+3+2` | 15 |
| `4+3+1+1` | 30 |
| `4+2+2+1` | 30 |
| `4+2+1+1+1` | 52 |
| `4+1+1+1+1+1` | 72 |
| `3+3+3` | 20 |
| `3+3+2+1` | 30 |
| `3+3+1+1+1` | 52 |
| `3+2+2+2` | 33 |
| `3+2+2+1+1` | 90 |
| `3+2+1+1+1+1` | 116 |
| `3+1+1+1+1+1+1` | 184 |
| `2+2+2+2+1` | 79 |
| `2+2+2+1+1+1` | 127 |
| `2+2+1+1+1+1+1` | 216 |
| `2+1+1+1+1+1+1+1` | 324 |
| `1+1+1+1+1+1+1+1+1` | 498 |

For the separator, mark the agreement count with the first alternating-cycle
matching and mark its first edge, exactly as for eight rooks. Each
black/Boolean coefficient is then expanded at the next marked edge. The true
coefficient fixes an edge and is an eight-rook fiber. In the false coefficient,
the row expansion is a disjoint sum over the alternative edges; the next
agreement marker separates those cofactor types by its black exponent. The 30
partition rows above are closed under these two marked operations, and every
resulting response class is a subset of an eight-rook marked state. It inherits
that state's three-round strategy. This gives four rounds in total. The
induction invariant is the marked cofactor type, not the number of individual
matchings.

The coefficient 498 is sharp at

```text
P = C = {0,1,2,3,4,5,6,7,8},
h = {0,1,2,3,5,6,8,9,10}.
```

The program `nine_rook_profiles.cpp` independently audits all 30 coefficient
rows after translation normalization. There are only `10*10` normalized
position/color pairs; this is a check of the finite switching table, not a
search over Mastermind strategies.

The complete conditional schedule is

```text
10 + 4 = 14.
```

Subject to the nine-rook switching lemma, this allocation would give
`T+(10,11) <= 14`.

The reconstructed verifier
`research/ten-fields-eleven-colors/verify_nine_rook_sep4.cpp` checks the
stronger explicit separator-search version of the nine-rook claim. It does
not use the unattached source or SHA quoted in the Sep 4 proposal. It
enumerates translation/reflection-normalized support pairs, groups each
support pair's `9!` bijections by exact displacement histogram, and then runs
the legal predicate

```text
Sep_0(S)       iff |S| <= 1,
Sep_(d+1)(S)   iff exists query q, forall black b, exists checked edge e,
                 both Boolean children satisfy Sep_d.
```

Queries are restricted to current candidate bijections, which is a sound
restriction for proving existence because those queries are legal. The checked
output in this repository is:

```text
position representatives: 5
color representatives: 5
normalized support pairs: 25
fibers checked: 207270
total fiber memberships: 9072000
maximum fiber size: 498
fibers of size >= 4: 195790
not solved in four rounds: 0
```

The source SHA-256 is

```text
1b6182b58e5a2f9ab94f8e99c5fd406319bcc36c4c293de2ba949cb0c8487965
```

Reproduce it with

```sh
g++ -std=c++2a -O3 research/ten-fields-eleven-colors/verify_nine_rook_sep4.cpp -o /tmp/verify_nine_rook_sep4
/tmp/verify_nine_rook_sep4
```

This closes the standalone computational audit of the normalized Sep 4 search,
but it is still not a Lean-kernel proof. The verifier currently proves and
discards existence during recursion; it does not serialize a deterministic
certificate DAG, prove normalization completeness in Lean, or transport a
checked certificate back to arbitrary cylindrical fibers.

### Audit of the cyclic/X-ray upper bound

The ten-query cyclic setup and the equality-accelerated search now have formal
proofs. Lean checks that the eleven black counts sum to ten, the unqueried
count is reconstructed, the ten equality checks identify field zero, an active
cyclic class followed by a zero class exists, every mixed query is legal, and
the balanced false-answer recurrence is `9 -> 4 -> 1`. The supplied profile
programs reproduce the stated maximum X-ray fiber sizes, including the
86-member eight-rook and 498-member nine-rook fibers.

The profile programs do **not**, however, verify either universal adaptive
separator. `eight_rook_profiles.cpp` and `nine_rook_profiles.cpp` count
coefficients only. The new nine-rook Sep 4 verifier is an all-fiber strategy
search, but its proof objects are not imported into Lean. The Python
certificate search and its Lean-checked export cover only the named 86-member
state. Likewise, the prose claims that the multiplicity rows are closed under
marked operations do not display those rows or a map from every child to an
already solved state. A coefficient bound alone does not imply a legal
separator.

In particular, the inequality `498 < 20^3` and the coefficient table do not by
themselves supply the missing strategy. No closed 13-round protocol was
obtained.

### Exact separator and certificate infrastructure

The Lean file `BlackPegExtraCheck/Separator.lean` now defines the legal
recursive predicate requested for endgame certificates:

```text
Sep_0(S)       iff |S| <= 1,
Sep_(d+1)(S)   iff there is a legal query q such that, for every black
                 response b, there is a legal checked edge e for which both
                 Boolean children satisfy Sep_d.
```

The quantifier order permits the edge to depend on the black response. Lean
proves that `Sep_d(S)` is equivalent to existence of the existing fully legal
adaptive strategy tree of depth `d`. A finite `SeparatorCertificate` stores a
legal query, a checked edge per black class, Boolean child references, and a
named singleton at each leaf. Its executable Boolean checker is sound for
`Sep`, and both `Sep` and certificate validity are monotone under taking
subsets of a state.

No all-fiber certificate has yet been checked. In particular, the new checker
does not by itself prove that every eight-rook fiber has `Sep_3`, or that every
nine-rook fiber has `Sep_4` or `Sep_3`. Symmetry normalization and a compact
certificate covering every normalized fiber remain implementation
bottlenecks. Therefore the closed mathematical upper bound remains the
source-backed classical 44-round result; 15 and 14 remain conditional
allocations.

## Lean scope

[`BlackPegExtraCheck/TenFieldsElevenColors.lean`](../../BlackPegExtraCheck/TenFieldsElevenColors.lean)
kernel-checks the 39,916,800-secret cardinality, the 22-outcome transcript
bound, the information bounds of five and six, the derangement argument, and
the full response-fiber capacity proof ruling out legal seven-round strategies.
The derangement count comes from its recurrence, while the black-fiber bound
uses match-set injections rather than enumerating secrets.

For the lower bound, Lean now also checks the high-response fiber refinements,
the three-round capacity `6370`, and the reduction of a nine-round lower bound
to both the four-zero/false intersection inequality (4) and the five-zero/false
intersection inequality (5). The perfect-matching file additionally checks
completion/restriction, injection into both survivor states, five- and
six-factor necessity, permanent-threshold arithmetic, the six- and
seven-regular defect reductions, and explicit degree-one and degree-three
obstructions. It does not prove either universal survivor inequality.

For the upper-bound audit, Lean checks the published 44-round arithmetic and
the arithmetic of the shorter allocations. More importantly,
[`BlackPegExtraCheck/CyclicStrategy.lean`](../../BlackPegExtraCheck/CyclicStrategy.lean)
now formalizes the ten cyclic rounds, transcript reconstruction, legal mixed
queries, the two-round accelerated search, and their strategy-tree
composition. The theorem
`exists_fifteenRoundStrategy_of_eightRookCylindricalSep` constructs an actual
`TenElevenStrategy 15` from the single precise premise
`EightRookCylindricalSepThree`. No theorem turns a bare numerical premise into
a purported upper bound, and no proof of that separator premise is supplied.

The separator file is exact and executable, but currently contains checker
infrastructure rather than an all-fiber certificate. Lean accepts one explicit
three-round certificate for the named sharp 86-state example in
[`BlackPegExtraCheck/SharpEightRookCertificate.lean`](../../BlackPegExtraCheck/SharpEightRookCertificate.lean).
That example changes no numerical upper bound; a complete certificate family
or a structural universal theorem is still required.

## Primary sources

- M. El Ouali, C. Glazik, V. Sauerland, and A. Srivastav,
  [On the Query Complexity of Black-Peg AB-Mastermind](https://arxiv.org/abs/1611.05907),
  especially Theorem 3 and the `k > n` construction.
- C. Bebeacua, T. Mansour, A. Postnikov, and S. Severini,
  [On the X-rays of permutations](https://arxiv.org/abs/math/0506334),
  for the diagonal-X-ray/displacement-multiset viewpoint and the planar
  five- and six-rook degeneracies.
- A. Schrijver,
  [Counting 1-factors in regular bipartite graphs](https://doi.org/10.1006/jctb.1997.1798),
  for the permanent lower bound used in the five-fiber discussion.
