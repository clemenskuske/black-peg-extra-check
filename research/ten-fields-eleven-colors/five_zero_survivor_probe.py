#!/usr/bin/env python3
"""Audit one difficult five-zero/five-false survivor state.

This program does not search the Mastermind game tree and is not a proof of a
universal lower bound.  It evaluates the explicit degree-one five-factor
obstruction formalized in ``FiveZeroBridge.lean`` by the standard subset DP
for bipartite matchings.  The DP has only ``11 * 2^11`` states.

The output supplies two discovery/audit facts:

* the actual ten-row survivor state has 10,404 secrets; and
* completing the five queries produces the same number of perfect matchings,
  while checked color 4 has degree one in the completed graph.

Thus the instance refutes a universal *five-factor* shortcut but is not a
counterexample to the desired universal inequality ``|Z_5| > 6370``.
"""

from __future__ import annotations

import argparse
from functools import cache
from itertools import combinations


COLORS = 11
QUERIES = (
    (8, 4, 1, 0, 7, 3, 9, 2, 6, 10),
    (3, 6, 10, 1, 2, 9, 0, 4, 7, 8),
    (10, 1, 0, 9, 3, 7, 4, 6, 8, 2),
    (0, 8, 9, 4, 10, 1, 6, 3, 2, 7),
    (7, 3, 4, 6, 1, 8, 2, 0, 10, 9),
)
CHECKS = ((4, 4), (0, 4), (5, 4), (9, 4), (8, 4))


def completed_queries() -> tuple[tuple[int, ...], ...]:
    completed = []
    all_colors = set(range(COLORS))
    for query in QUERIES:
        if len(query) != 10 or len(set(query)) != 10:
            raise ValueError(f"not a legal ten-row query: {query}")
        omitted = tuple(all_colors - set(query))
        if len(omitted) != 1:
            raise ValueError(f"query does not omit exactly one color: {query}")
        completed.append(query + omitted)
    return tuple(completed)


def forbidden_rows_for(
    queries: tuple[tuple[int, ...], ...],
    checks: tuple[tuple[int, int], ...],
    *,
    complete: bool,
) -> tuple[frozenset[int], ...]:
    row_count = 11 if complete else 10
    forbidden = [set() for _ in range(row_count)]
    for query in queries:
        for row, color in enumerate(query[:row_count]):
            forbidden[row].add(color)
    for row, color in checks:
        forbidden[row].add(color)
    return tuple(frozenset(row) for row in forbidden)


def forbidden_rows(*, complete: bool) -> tuple[frozenset[int], ...]:
    return forbidden_rows_for(completed_queries(), CHECKS, complete=complete)


def matching_count(forbidden: tuple[frozenset[int], ...]) -> int:
    """Count row-saturating matchings by a 2^11 used-color DP."""

    @cache
    def visit(row: int, used: int) -> int:
        if row == len(forbidden):
            return 1
        return sum(
            visit(row + 1, used | (1 << color))
            for color in range(COLORS)
            if not (used & (1 << color)) and color not in forbidden[row]
        )

    return visit(0, 0)


def completed_color_degree(color: int) -> int:
    forbidden = forbidden_rows(complete=True)
    return sum(color not in row for row in forbidden)


def single_move_neighborhood() -> tuple[int, int, int]:
    """Check every one-swap query move and every one-check replacement."""

    queries = completed_queries()
    baseline = matching_count(
        forbidden_rows_for(queries, CHECKS, complete=False)
    )
    best = baseline
    equal = 0
    moves = 0

    for query_index in range(5):
        for first, second in combinations(range(11), 2):
            changed = [list(query) for query in queries]
            changed[query_index][first], changed[query_index][second] = (
                changed[query_index][second],
                changed[query_index][first],
            )
            value = matching_count(
                forbidden_rows_for(
                    tuple(tuple(query) for query in changed),
                    CHECKS,
                    complete=False,
                )
            )
            best = min(best, value)
            equal += value == baseline
            moves += 1

    for check_index in range(5):
        for row in range(10):
            for color in range(11):
                if (row, color) == CHECKS[check_index]:
                    continue
                changed = list(CHECKS)
                changed[check_index] = (row, color)
                value = matching_count(
                    forbidden_rows_for(
                        queries, tuple(changed), complete=False
                    )
                )
                best = min(best, value)
                equal += value == baseline
                moves += 1

    return moves, best, equal


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--neighbors",
        action="store_true",
        help="also audit all 820 single query-swap/check-replacement moves",
    )
    arguments = parser.parse_args()
    completed = completed_queries()
    ten_row = forbidden_rows(complete=False)
    eleven_row = forbidden_rows(complete=True)
    ten_count = matching_count(ten_row)
    completed_count = matching_count(eleven_row)
    degree_four = completed_color_degree(4)

    assert ten_count == 10_404
    assert completed_count == 10_404
    assert degree_four == 1

    print("omitted query colors:", [query[-1] for query in completed])
    print("ten-row survivor count:", ten_count)
    print("completed perfect-matchings:", completed_count)
    print("completed degree of checked color 4:", degree_four)
    if arguments.neighbors:
        moves, best, equal = single_move_neighborhood()
        print("single-move neighbors:", moves)
        print("best count in closed single-move neighborhood:", best)
        print("distinct neighbors tying the witness:", equal)


if __name__ == "__main__":
    main()
