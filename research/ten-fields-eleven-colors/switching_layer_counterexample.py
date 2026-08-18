#!/usr/bin/env python3
"""Audit the obstruction to the naive four/six-cycle marginal proof.

The graph below is seven-regular on two copies of ``Fin 11``.  For the edge
``(0, 0)``, let ``C`` count perfect matchings containing the edge.  Across
those matchings, ``T4`` counts legal direct four-cycle switches and ``T6``
counts legal six-cycle switches whose endpoint shortcut is forbidden.

Direct switches have unique reverse images, while a bad-shortcut six-cycle
output has at most six reverse images.  The tempting sufficient inequality
``6*T4 + T6 >= 30*C`` is false on this graph.  The actual one-sixth marginal
inequality still holds, so this is a counterexample to that proof attempt,
not to the desired marginal theorem.
"""

from __future__ import annotations


SIZE = 11
ROWS = tuple(
    int(bits, 2)
    for bits in (
        "10101111001",
        "11110010011",
        "10110010111",
        "01001101111",
        "11110010011",
        "01001101111",
        "01011101110",
        "11110010110",
        "01011101101",
        "10101111100",
        "10111111000",
    )
)


def permanent(rows: tuple[int, ...]) -> int:
    """Count perfect matchings by subset DP."""

    dp = [0] * (1 << SIZE)
    dp[0] = 1
    for row, allowed in enumerate(rows):
        following = [0] * len(dp)
        for used, count in enumerate(dp):
            if not count or used.bit_count() != row:
                continue
            available = allowed & ~used
            while available:
                bit = available & -available
                available -= bit
                following[used | bit] += count
        dp = following
    return dp[-1]


def containing_matchings():
    """Generate matchings that contain ``(0, 0)``."""

    image = [0] * SIZE

    def visit(row: int, used: int):
        if row == SIZE:
            yield tuple(image)
            return
        available = ROWS[row] & ~used & ~1
        while available:
            bit = available & -available
            available -= bit
            image[row] = bit.bit_length() - 1
            yield from visit(row + 1, used | bit)

    yield from visit(1, 1)


def switching_counts() -> tuple[int, int, int]:
    containing = direct = bad_six = 0
    for image in containing_matchings():
        containing += 1
        for second in range(1, SIZE):
            if ROWS[second] & 1 and (ROWS[0] >> image[second]) & 1:
                direct += 1
        for first in range(1, SIZE):
            first_color = image[first]
            if not ((ROWS[0] >> first_color) & 1):
                continue
            for second in range(1, SIZE):
                if first == second or not (ROWS[second] & 1):
                    continue
                second_color = image[second]
                if not ((ROWS[first] >> second_color) & 1):
                    continue
                if (ROWS[second] >> first_color) & 1:
                    continue
                bad_six += 1
    return containing, direct, bad_six


def main() -> None:
    assert all(row.bit_count() == 7 for row in ROWS)
    assert all(sum((row >> color) & 1 for row in ROWS) == 7 for color in range(SIZE))
    total = permanent(ROWS)
    containing, direct, bad_six = switching_counts()
    assert (total, containing, direct, bad_six) == (369_396, 53_604, 177_336, 449_064)
    assert 6 * direct + bad_six == 1_513_080
    assert 30 * containing == 1_608_120
    assert 6 * direct + bad_six < 30 * containing
    assert 6 * containing <= total
    print("perfect matchings:", total)
    print("matchings containing (0, 0):", containing)
    print("four-cycle incidences:", direct)
    print("bad-shortcut six-cycle incidences:", bad_six)
    print("weighted switching count:", 6 * direct + bad_six, "<", 30 * containing)
    print("actual marginal check:", 6 * containing, "<=", total)


if __name__ == "__main__":
    main()
