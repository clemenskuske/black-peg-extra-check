#!/usr/bin/env python3
"""Exact overlapping-query counterexample to the one-sixth marginal claim.

The four rows below are completed legal queries (permutations of eleven
colors).  Their avoidance graph is therefore in the exact four-query class,
not merely an arbitrary dense bipartite graph.  The checked edge ``(0, 0)``
is allowed, but it occurs in more than one sixth of all perfect matchings.

The graph has a transparent block form.  On row blocks of sizes five and six
and the corresponding color blocks, its forbidden matrix is
``(J_5 - I_5) direct_sum I_6``.  The six-term formula below counts matchings by
the number ``k`` of identity edges used in the first block.  Subset DP audits
the same totals independently.
"""

from __future__ import annotations

from math import comb, factorial


SIZE = 11
QUERIES = (
    (8, 4, 1, 6, 0, 9, 3, 7, 10, 2, 5),
    (9, 4, 1, 6, 3, 8, 2, 7, 10, 0, 5),
    (3, 4, 1, 6, 8, 2, 0, 7, 10, 9, 5),
    (2, 4, 1, 6, 9, 0, 8, 7, 10, 3, 5),
)
FIRST_ROWS = (0, 4, 5, 6, 9)
FIRST_COLORS = (0, 2, 3, 9, 8)
SECOND_ROWS = (1, 2, 3, 7, 8, 10)
SECOND_COLORS = (4, 1, 6, 7, 10, 5)


def allowed_rows() -> tuple[int, ...]:
    rows = []
    for row in range(SIZE):
        forbidden = {query[row] for query in QUERIES}
        rows.append(sum(1 << color for color in range(SIZE) if color not in forbidden))
    return tuple(rows)


def permanent(rows: tuple[int, ...], force_tested_edge: bool = False) -> int:
    """Count perfect matchings by a 2^11 subset recurrence."""

    dp = [0] * (1 << SIZE)
    dp[1 if force_tested_edge else 0] = 1
    first_row = 1 if force_tested_edge else 0
    for row in range(first_row, SIZE):
        following = [0] * len(dp)
        for used, count in enumerate(dp):
            if not count:
                continue
            available = rows[row] & ~used
            while available:
                bit = available & -available
                available -= bit
                following[used | bit] += count
        dp = following
    return dp[-1]


def partial_derangement_count(points: int) -> int:
    """Permutations of six objects avoiding ``points`` specified fixed points."""

    return sum((-1) ** j * comb(points, j) * factorial(6 - j)
               for j in range(points + 1))


def block_formula(marked: bool) -> int:
    total = 0
    for k in range(6):
        choose_identity = comb(4, k - 1) if marked and k else (
            0 if marked else comb(5, k)
        )
        first_to_second = factorial(6) // factorial(k + 1)
        finish_second = partial_derangement_count(k + 1)
        total += choose_identity * first_to_second * finish_second
    return total


def main() -> None:
    assert all(sorted(query) == list(range(SIZE)) for query in QUERIES)
    rows = allowed_rows()
    assert all(query[0] != 0 for query in QUERIES)

    # Verify the claimed block form directly from the four legal queries.
    for index, row in enumerate(FIRST_ROWS):
        allowed_first = {color for color in FIRST_COLORS if rows[row] >> color & 1}
        allowed_second = {color for color in SECOND_COLORS if rows[row] >> color & 1}
        assert allowed_first == {FIRST_COLORS[index]}
        assert allowed_second == set(SECOND_COLORS)
    for index, row in enumerate(SECOND_ROWS):
        allowed_first = {color for color in FIRST_COLORS if rows[row] >> color & 1}
        allowed_second = {color for color in SECOND_COLORS if rows[row] >> color & 1}
        assert allowed_first == set(FIRST_COLORS)
        assert allowed_second == set(SECOND_COLORS) - {SECOND_COLORS[index]}

    total = permanent(rows)
    containing = permanent(rows, force_tested_edge=True)
    formula_total = block_formula(marked=False)
    formula_containing = block_formula(marked=True)
    assert total == formula_total == 1_968_535
    assert containing == formula_containing == 458_761
    assert 6 * containing - total == 784_031 > 0

    print("query-only perfect matchings:", total)
    print("matchings containing (0, 0):", containing)
    print("six-times-containing excess:", 6 * containing - total)
    print("marginal ratio:", f"{containing / total:.9f}")


if __name__ == "__main__":
    main()
