#!/usr/bin/env python3
"""Search for short extra-check certificates in one eight-rook X-ray fiber.

This is a falsification/discovery aid for the structural proof, not the proof
itself.  A state is represented by a subset of the fiber.  A round chooses a
bijection, observes its agreement count, and may then test one edge chosen
adaptively for that agreement class.
"""

from __future__ import annotations

from functools import cache
from itertools import permutations
from os import environ
from random import Random


MODULUS = 11


def tuple_from_env(name: str, default: str) -> tuple[int, ...]:
    return tuple(map(int, environ.get(name, default).split(",")))


POSITIONS = tuple_from_env("ROOK_POSITIONS", "0,1,2,3,4,5,6,7")
COLORS = tuple_from_env("ROOK_COLORS", "0,1,2,3,4,6,7,9")
DIAGONALS = tuple_from_env("ROOK_DIAGONALS", "0,1,2,4,6,7,8,9")
N = len(POSITIONS)
QUERIES = tuple(permutations(COLORS))


def diagonal_signature(q: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(
        sorted((color - position) % MODULUS for position, color in zip(POSITIONS, q))
    )


FIBER = tuple(q for q in QUERIES if diagonal_signature(q) == DIAGONALS)
ALL = (1 << len(FIBER)) - 1


def members(mask: int):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def full_partition_masks(query: tuple[int, ...]) -> tuple[int, ...]:
    groups = [0] * (N + 1)
    for index, secret in enumerate(FIBER):
        black = sum(a == b for a, b in zip(query, secret))
        groups[black] |= 1 << index
    return tuple(groups)


FULL_PARTITIONS = tuple(full_partition_masks(query) for query in QUERIES)
QUERY_INDEX = {query: index for index, query in enumerate(QUERIES)}


def partition_masks(query: tuple[int, ...], mask: int) -> tuple[int, ...]:
    return tuple(
        child
        for group in FULL_PARTITIONS[QUERY_INDEX[query]]
        if (child := group & mask)
    )


def edge_mask(position: int, color: int) -> int:
    return sum(
        1 << index
        for index, secret in enumerate(FIBER)
        if secret[position] == color
    )


EDGES = tuple(
    (position, color, edge_mask(position, color))
    for position in range(N)
    for color in COLORS
)


@cache
def one_round(mask: int):
    """Return a query whose black classes have size at most two."""
    if mask.bit_count() <= 2:
        return QUERIES[0]
    for query in QUERIES:
        if all(group.bit_count() <= 2 for group in partition_masks(query, mask)):
            return query
    return None


@cache
def two_round(mask: int):
    """Return a query and one equality split per nonempty black class."""
    if one_round(mask) is not None:
        return (one_round(mask), ())
    ranked = sorted(
        QUERIES,
        key=lambda query: max(
            group.bit_count() for group in partition_masks(query, mask)
        ),
    )
    for query in ranked:
        witnesses = []
        for group in partition_masks(query, mask):
            split = None
            for position, color, equality in EDGES:
                yes = group & equality
                no = group & ~equality
                if one_round(yes) is not None and one_round(no) is not None:
                    split = (position, color, yes, no)
                    break
            if split is None:
                break
            witnesses.append(split)
        else:
            return (query, tuple(witnesses))
    return None


def three_round(mask: int, sample: int | None = None):
    """Return a first-round certificate whose children are two-round states."""
    ranked = sorted(
        QUERIES,
        key=lambda query: max(
            group.bit_count() for group in partition_masks(query, mask)
        ),
    )
    if sample is not None:
        best = ranked[: min(sample // 2, len(ranked))]
        rest = ranked[len(best) :]
        Random(20260806).shuffle(rest)
        ranked = best + rest[: max(0, sample - len(best))]
    for number, query in enumerate(ranked, 1):
        witnesses = []
        for group in partition_masks(query, mask):
            split = None
            for position, color, equality in EDGES:
                yes = group & equality
                no = group & ~equality
                yes_witness = two_round(yes)
                if yes_witness is None:
                    continue
                no_witness = two_round(no)
                if no_witness is not None:
                    split = (
                        position,
                        color,
                        yes,
                        no,
                        yes_witness,
                        no_witness,
                    )
                    break
            if split is None:
                break
            witnesses.append(split)
        else:
            return (query, tuple(witnesses), number)
    return None


def compact_query(query: tuple[int, ...]) -> str:
    return "".join("A" if color == 10 else str(color) for color in query)


def main() -> None:
    print(f"fiber size: {len(FIBER)}")
    best_query = min(
        QUERIES,
        key=lambda query: max(group.bit_count() for group in partition_masks(query, ALL)),
    )
    print(
        "best first black partition:",
        compact_query(best_query),
        sorted((group.bit_count() for group in partition_masks(best_query, ALL)), reverse=True),
    )
    if environ.get("CHECK_TWO_ROUNDS") == "1":
        direct_two = two_round(ALL)
        print("two-round certificate:", "yes" if direct_two is not None else "no")
    witness = three_round(ALL, sample=256)
    if witness is None:
        print("no three-round certificate in sampled first queries")
        return
    query, branches, number = witness
    print(f"certificate first query #{number}: {compact_query(query)}")
    for group, branch in zip(partition_masks(query, ALL), branches):
        position, color, yes, no, yes_witness, no_witness = branch
        print(
            f"  black-class {group.bit_count():2d}: test ({position},{color}); "
            f"children {yes.bit_count()}+{no.bit_count()}; "
            f"queries {compact_query(yes_witness[0])}/{compact_query(no_witness[0])}; "
            f"marked branches {len(yes_witness[1])}/{len(no_witness[1])}"
        )


if __name__ == "__main__":
    main()
