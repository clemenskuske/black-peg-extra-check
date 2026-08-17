# Research memo: beyond the audited `8 ... 44` bounds

## Current rigorous position

The closed Lean lower bound is `T+(10,11) >= 8`.  The justified mathematical
upper bound is the published classical `T+(10,11) <= 44`, which ignores the
extra equality answer; that external strategy is not represented by a Lean
tree.

The proposed fifteen-round route is now reduced exactly as follows:

```text
10 cyclic setup rounds
  + 2 equality-accelerated findNext rounds
  + 3 rounds for every eight-rook cylindrical fiber.
```

Lean checks the first twelve rounds and their composition.  It also proves
that the final premise is precisely `EightRookCylindricalSepThree`, using the
legal quantifier order in `Sep`.  The coefficient maximum 86 and a
kernel-checked three-round certificate for the named sharp state are evidence,
not a universal proof.

For the lower bound, Lean reduces `T+(10,11) >= 9` to the universal inequality
`|Z_5| > 6370` after five zero-black/false-check responses.  Completed perfect
matchings inject into `Z_5`, but the existing degree-one example shows that a
five-factor cannot simply be assumed.

## Improving the proposed 15 to 14

### 1. Prove a marked-cofactor induction for nine rooks

This is the cleanest structural target.  Define a class of *marked* permanent
coefficients that records all information actually present after a black
answer and an adaptive edge answer, not merely the unmarked displacement
partition.  Prove that one legal query/check sends every nine-rook marked
state to an eight-rook marked state, then invoke a proved universal `Sep 3`
theorem.  This would give `10 + 4 = 14`.

The critical point is the false edge child.  The true child is a single
eight-rook cofactor, whereas the false child is generally a union of
cofactors.  A valid induction must give an explicit invariant for that union
and a map for every response class.  A table indexed only by the 30 integer
partitions of nine is not enough.

Concrete next lemma:

```text
NineMarkedState S -> exists legal (q, edge-by-black),
  every child S' is contained in a named EightMarkedState.
```

The named containment makes the argument directly compatible with `Sep.mono`.

### 2. Merge the tenth setup query with the first search comparison

The present schedule spends ten black queries to recover eleven cyclic counts,
then two mixed queries to locate an active component.  Try querying only nine
pure shifts and make round ten the first mixed comparison.  The two missing
cyclic counts satisfy the total-mass equation; the mixed count supplies a
second linear statistic on one side of the cut.  The equality bit can be used
to resolve the exceptional ambiguity or identify the tested component.

A successful invariant would yield

```text
9 setup/search rounds + 2 remaining search rounds + 3 eight-rook rounds = 14.
```

This route is attractive because it improves the already formalized phase
rather than demanding a stronger separator.  It must explicitly reconstruct
the residual cylindrical profile; knowing only its total size is insufficient.

### 3. Import the nine-rook all-fiber verifier into Lean

`verify_nine_rook_sep4.cpp` now independently reproduces the normalized
nine-rook Sep 4 search:

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

The remaining task is proof production, not another existence search. Serialize
the selected query, checked edge, and child references as deterministic DAGs;
then prove the normalization/transport lemmas and check the DAGs with
`SeparatorCertificate.check`.

Use the affine action

```text
p |-> a*p+s,   c |-> a*c+t       (a != 0 mod 11)
```

to canonicalize `(P,C,h)` and transport legal queries, checked edges, and
certificates.  Generate one compact certificate DAG per canonical fiber and
have Lean check both the canonicalization theorem and every DAG with the sound
checker.  This is a reasonable fallback for `Sep 3` on eight rooks and `Sep 4`
on nine rooks: it enumerates symmetry types of small fibers, not the
39,916,800-secret game tree.

Before committing to this route, count canonical fibers and certificate nodes.
Reject a data dump whose completeness depends on an unproved normalization or
whose checker does not use the adaptive black-then-edge quantifier order.

### 4. Test whether the sharp eight-rook fiber rules out a two-round endgame

If the 86-member sharp fiber has no `Sep 2` strategy even when every residual
bijection is allowed as a query, then the tempting allocation
`10 + 2 + 2 = 14` is impossible for this setup/search route.  A negative result
needs an exhaustive *two-round separator* certificate or a structural
obstruction, not the fact that one heuristic search failed.  If it is
separable, a universal two-round theorem would be an even shorter route to 14.

## Raising the closed lower bound from 8 to 9

### 1. Complete the forbidden-query graph to a regular graph, then classify defects

The union of five completed query permutations is a bipartite graph of maximum
degree at most five.  Prove that it is contained in a five-regular bipartite
graph; equivalently, add forbidden edges until it decomposes into five
edge-disjoint perfect matchings.  Enlarging the forbidden set only decreases
the survivor permanent, so this reduces the universal problem to a
six-regular allowed graph with at most five checked edges deleted.

The repository already proves that failure of the five-factor cut condition
then has excess `s in {1,2,3,4}` and contains at least `s+1` deleted edges.
Finish by classifying these four defect types.  In each type, peel forced
edges/blocks and find a regular factor on the remaining block, or give a
bounded-congestion switching injection into matchings avoiding the deleted
edges.  The target is only 6,371, while the five-factor case gives at least
6,832.

This route directly addresses the degree-one example instead of excluding it:
its forced edge should be peeled, after which the large residual block carries
the permanent bound.

### 2. Use stable-polynomial capacity for `6`-regular minus five edges

The perfect-matching polynomial is stable, and a six-regular bipartite graph
has a canonical fractional matching.  Optimize Gurvits/Schrijver capacity
after deleting five specified edges, with separate constraints for the four
small defect cuts.  A successful inequality would prove the permanent lower
bound without finding an integral five-factor.

The calculation must retain the *locations* of the deleted edges.  A bound
depending only on the number five is likely too weak; concentration inside an
exceptional cut is exactly the hard case isolated by Lean.

### 3. Construct a switching injection away from the five checked edges

Start from perfect matchings of the six-regular base.  For a matching using a
deleted edge, switch along its shortest alternating cycle to avoid the first
deleted edge.  Bound the number of preimages of an avoiding matching using the
fact that there are only five deleted edges and eleven vertices.  Coupled
two-switches and cycles of length at least three mirror the useful part of the
cylindrical switching analysis, but here the target is a permanent lower
bound rather than a separator.

This becomes convincing only with an explicit congestion constant strong
enough to leave more than 6,370 matchings.

### 4. Strengthen the adversary if the universal five-zero path is false

Search first for a genuine counterexample to `|Z_5| > 6370` using the
`11 * 2^11` permanent DP, normalized by simultaneous row/color relabeling.  If
one exists, retain a weighted permanent or capacity potential and let the
adversary choose zero/true versus zero/false at each equality check to preserve
that potential.  This would replace the rigid all-false path by a
state-dependent adversary while continuing to use the checked three-round
capacity 6,370.

Computation here is a falsification and conjecture-forming tool.  A lower-bound
claim still needs a universal inequality or an explicit adversary invariant.

## Recommended order

1. Prove the regular-completion lemma and attack the four lower-bound defect
   types; this has the clearest finite structural bottleneck.
2. Formalize the marked state class for the eight-rook separator and test
   closure on the sharp and other coefficient-maximizing fibers.
3. Explore the nine-pure-shift plus one-mixed-query reconstruction algebra.
4. Use symmetry-reduced certificate generation only after the canonicalization
   theorem and expected certificate size are understood.
