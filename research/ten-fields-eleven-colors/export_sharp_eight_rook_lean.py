#!/usr/bin/env python3
"""Export the named 86-state discovery certificate as kernel-checkable Lean data.

This deliberately covers one reduced eight-rook fiber only.  It is not an
all-fiber enumeration and does not prove the universal cylindrical separator.
"""

from __future__ import annotations

from dataclasses import dataclass
from sys import argv

import eight_rook_certificate as search


FIXED = (5, 8)
FULL_BLACK_OFFSET = len(FIXED)
DEFAULT_EDGE = (0, 0)


@dataclass(frozen=True)
class DepthOne:
    query: tuple[int, ...]
    checks: tuple[tuple[int, int], ...]
    yes_leaf: tuple[int, ...]
    no_leaf: tuple[int, ...]


@dataclass(frozen=True)
class DepthTwo:
    query: tuple[int, ...]
    checks: tuple[tuple[int, int], ...]
    yes_next: tuple[int, ...]
    no_next: tuple[int, ...]


def nonempty_groups(query: tuple[int, ...], mask: int):
    partition = search.FULL_PARTITIONS[search.QUERY_INDEX[query]]
    return tuple((black, group & mask) for black, group in enumerate(partition)
                 if group & mask)


def first_member(mask: int) -> int:
    return next(search.members(mask), 0)


queries: list[tuple[int, ...]] = []
query_ids: dict[tuple[int, ...], int] = {}
depth_one: list[DepthOne] = []
depth_one_ids: dict[tuple[int, tuple[int, ...]], int] = {}
depth_two: list[DepthTwo] = []
depth_two_ids: dict[tuple[int, tuple], int] = {}


def query_id(query: tuple[int, ...]) -> int:
    if query not in query_ids:
        query_ids[query] = len(queries)
        queries.append(query)
    return query_ids[query]


def build_depth_one(mask: int, query: tuple[int, ...]) -> int:
    key = (mask, query)
    if key in depth_one_ids:
        return depth_one_ids[key]
    checks = [DEFAULT_EDGE] * 11
    yes_leaf = [0] * 11
    no_leaf = [0] * 11
    partition = search.FULL_PARTITIONS[search.QUERY_INDEX[query]]
    for reduced_black, full_group in enumerate(partition):
        group = full_group & mask
        full_black = reduced_black + FULL_BLACK_OFFSET
        members = tuple(search.members(group))
        assert len(members) <= 2
        if not members:
            continue
        if len(members) == 1:
            secret = members[0]
            edge = (0, search.FIBER[secret][0])
        else:
            first, second = members
            position = next(
                i for i in range(search.N)
                if search.FIBER[first][i] != search.FIBER[second][i]
            )
            edge = (position, search.FIBER[first][position])
        checks[full_black] = edge
        yes = group & search.edge_mask(*edge)
        no = group & ~search.edge_mask(*edge)
        assert yes.bit_count() <= 1 and no.bit_count() <= 1
        yes_leaf[full_black] = first_member(yes)
        no_leaf[full_black] = first_member(no)
    node = DepthOne(query, tuple(checks), tuple(yes_leaf), tuple(no_leaf))
    index = len(depth_one)
    depth_one_ids[key] = index
    depth_one.append(node)
    query_id(query)
    return index


def build_depth_two(mask: int, witness: tuple) -> int:
    key = (mask, witness)
    if key in depth_two_ids:
        return depth_two_ids[key]
    query, splits = witness
    checks = [DEFAULT_EDGE] * 11
    yes_next: list[int | None] = [None] * 11
    no_next: list[int | None] = [None] * 11
    if not splits:
        child = build_depth_one(mask, query)
        yes_next = [child] * 11
        no_next = [child] * 11
        node_query = search.QUERIES[0]
    else:
        groups = nonempty_groups(query, mask)
        assert len(groups) == len(splits)
        for (reduced_black, group), split in zip(groups, splits):
            position, color, yes, no = split
            assert group == (yes | no) and not (yes & no)
            full_black = reduced_black + FULL_BLACK_OFFSET
            checks[full_black] = (position, color)
            yes_query = search.one_round(yes)
            no_query = search.one_round(no)
            assert yes_query is not None and no_query is not None
            yes_next[full_black] = build_depth_one(yes, yes_query)
            no_next[full_black] = build_depth_one(no, no_query)
        fallback = build_depth_one(0, search.QUERIES[0])
        yes_next = [fallback if child is None else child for child in yes_next]
        no_next = [fallback if child is None else child for child in no_next]
        node_query = query
    node = DepthTwo(
        node_query,
        tuple(checks),
        tuple(int(child) for child in yes_next),
        tuple(int(child) for child in no_next),
    )
    index = len(depth_two)
    depth_two_ids[key] = index
    depth_two.append(node)
    query_id(node_query)
    return index


def split_mask(mask: int, query: tuple[int, ...], full_black: int,
               edge: tuple[int, int], bit: bool) -> int:
    reduced_black = full_black - FULL_BLACK_OFFSET
    if not 0 <= reduced_black <= search.N:
        return 0
    group = search.FULL_PARTITIONS[search.QUERY_INDEX[query]][reduced_black] & mask
    equality = search.edge_mask(*edge)
    return group & equality if bit else group & ~equality


def verify_depth_one(node_index: int, mask: int) -> None:
    node = depth_one[node_index]
    for black in range(11):
        for bit, leaves in ((True, node.yes_leaf), (False, node.no_leaf)):
            child = split_mask(mask, node.query, black, node.checks[black], bit)
            expected = leaves[black]
            assert all(member == expected for member in search.members(child))


def verify_depth_two(node_index: int, mask: int) -> None:
    node = depth_two[node_index]
    for black in range(11):
        for bit, children in ((True, node.yes_next), (False, node.no_next)):
            child = split_mask(mask, node.query, black, node.checks[black], bit)
            verify_depth_one(children[black], child)


def build_root():
    witness = search.three_round(search.ALL, sample=256)
    assert witness is not None
    query, branches, _number = witness
    checks = [DEFAULT_EDGE] * 11
    yes_next: list[int | None] = [None] * 11
    no_next: list[int | None] = [None] * 11
    groups = nonempty_groups(query, search.ALL)
    assert len(groups) == len(branches)
    for (reduced_black, group), branch in zip(groups, branches):
        position, color, yes, no, yes_witness, no_witness = branch
        assert group == (yes | no) and not (yes & no)
        full_black = reduced_black + FULL_BLACK_OFFSET
        checks[full_black] = (position, color)
        yes_next[full_black] = build_depth_two(yes, yes_witness)
        no_next[full_black] = build_depth_two(no, no_witness)
    fallback = build_depth_two(0, (search.QUERIES[0], ()))
    yes_next = [fallback if child is None else child for child in yes_next]
    no_next = [fallback if child is None else child for child in no_next]
    query_id(query)
    return query, tuple(checks), tuple(yes_next), tuple(no_next)


ROOT = build_root()


def verify_root() -> None:
    query, checks, yes_next, no_next = ROOT
    for black in range(11):
        for bit, children in ((True, yes_next), (False, no_next)):
            child = split_mask(search.ALL, query, black, checks[black], bit)
            verify_depth_two(children[black], child)


verify_root()


def lean_vector(items) -> str:
    return "![" + ", ".join(map(str, items)) + "]"


def lean_row(values: tuple[int, ...]) -> str:
    return lean_vector((*values, *FIXED))


def lean_edge(edge: tuple[int, int]) -> str:
    return f"({edge[0]}, {edge[1]})"


def lean_nested(rows, render=str) -> str:
    return "![\n" + ",\n".join(
        "    " + lean_vector(render(item) for item in row) for row in rows
    ) + "\n  ]"


def render_module() -> str:
    candidates = "[\n" + ",\n".join(
        "    " + lean_row(secret) for secret in search.FIBER
    ) + "\n  ]"
    query_table = "![\n" + ",\n".join(
        "    " + lean_row(query) for query in queries
    ) + "\n  ]"
    d1_queries = lean_vector(query_ids[node.query] for node in depth_one)
    d1_checks = lean_nested((node.checks for node in depth_one), lean_edge)
    d1_yes = lean_nested((node.yes_leaf for node in depth_one))
    d1_no = lean_nested((node.no_leaf for node in depth_one))
    d2_queries = lean_vector(query_ids[node.query] for node in depth_two)
    d2_checks = lean_nested((node.checks for node in depth_two), lean_edge)
    d2_yes = lean_nested((node.yes_next for node in depth_two))
    d2_no = lean_nested((node.no_next for node in depth_two))
    root_query, root_checks, root_yes, root_no = ROOT
    root_check_table = "![\n    " + ", ".join(
        lean_edge(edge) for edge in root_checks
    ) + "\n  ]"
    return f'''/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.Separator
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# A checked certificate for one sharp eight-rook fiber

This is deliberately a certificate for the named 86-state reduced fiber only.
It is evidence for, but not a proof of, `EightRookCylindricalSepThree`.
-/

namespace BlackPegExtraCheck

def sharpEightRookRows : List (Fin 10 -> Fin 11) :=
  {candidates}

def sharpEightRookValues (index : Fin {len(search.FIBER)}) : Fin 10 -> Fin 11 :=
  sharpEightRookRows[index.val]'(by
    change index.val < {len(search.FIBER)}
    exact index.isLt)

def sharpEightRookSecret (index : Fin {len(search.FIBER)}) : TenElevenSecret where
  toFun := sharpEightRookValues index
  inj' := by
    fin_cases index <;> decide +kernel

def sharpEightRookCandidates : Finset TenElevenSecret :=
  Finset.univ.image sharpEightRookSecret

def sharpEightRookQueryValues : Fin {len(queries)} -> Fin 10 -> Fin 11 :=
  {query_table}

def sharpEightRookQuery (index : Fin {len(queries)}) : TenElevenSecret where
  toFun := sharpEightRookQueryValues index
  inj' := by
    fin_cases index <;> decide

def sharpEightRookDepthOneQuery : Fin {len(depth_one)} -> Fin {len(queries)} :=
  {d1_queries}

def sharpEightRookDepthOneCheck :
    Fin {len(depth_one)} -> Fin 11 -> Fin 10 × Fin 11 :=
  {d1_checks}

def sharpEightRookDepthOneYesLeaf :
    Fin {len(depth_one)} -> Fin 11 -> Fin {len(search.FIBER)} :=
  {d1_yes}

def sharpEightRookDepthOneNoLeaf :
    Fin {len(depth_one)} -> Fin 11 -> Fin {len(search.FIBER)} :=
  {d1_no}

def sharpEightRookDepthOneCertificate
    (index : Fin {len(depth_one)}) : SeparatorCertificate 1 :=
  .node (sharpEightRookQuery (sharpEightRookDepthOneQuery index))
    (sharpEightRookDepthOneCheck index) fun black bit =>
      .leaf (sharpEightRookSecret
        (if bit then sharpEightRookDepthOneYesLeaf index black
          else sharpEightRookDepthOneNoLeaf index black))

def sharpEightRookDepthTwoQuery : Fin {len(depth_two)} -> Fin {len(queries)} :=
  {d2_queries}

def sharpEightRookDepthTwoCheck :
    Fin {len(depth_two)} -> Fin 11 -> Fin 10 × Fin 11 :=
  {d2_checks}

def sharpEightRookDepthTwoYesNext :
    Fin {len(depth_two)} -> Fin 11 -> Fin {len(depth_one)} :=
  {d2_yes}

def sharpEightRookDepthTwoNoNext :
    Fin {len(depth_two)} -> Fin 11 -> Fin {len(depth_one)} :=
  {d2_no}

def sharpEightRookDepthTwoCertificate
    (index : Fin {len(depth_two)}) : SeparatorCertificate 2 :=
  .node (sharpEightRookQuery (sharpEightRookDepthTwoQuery index))
    (sharpEightRookDepthTwoCheck index) fun black bit =>
      sharpEightRookDepthOneCertificate
        (if bit then sharpEightRookDepthTwoYesNext index black
          else sharpEightRookDepthTwoNoNext index black)

def sharpEightRookRootCheck : Fin 11 -> Fin 10 × Fin 11 :=
  {root_check_table}

def sharpEightRookCertificate : SeparatorCertificate 3 :=
  .node (sharpEightRookQuery {query_ids[root_query]})
    sharpEightRookRootCheck fun black bit =>
      sharpEightRookDepthTwoCertificate
        (if bit then ({lean_vector(root_yes)} : Fin 11 -> Fin {len(depth_two)}) black
          else ({lean_vector(root_no)} : Fin 11 -> Fin {len(depth_two)}) black)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The explicit list contains 86 distinct legal ten-field secrets.
theorem sharpEightRookCandidates_card : sharpEightRookCandidates.card = 86 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The exact Boolean checker unfolds a three-level certificate over 86 candidates.
theorem sharpEightRookCertificate_accepted :
    sharpEightRookCertificate.check sharpEightRookCandidates = true := by
  decide +kernel

/-- This theorem is intentionally about one explicit state, not every fiber. -/
theorem sharpEightRookCandidates_sep_three :
    Sep 3 sharpEightRookCandidates :=
  SeparatorCertificate.check_sound _ _ sharpEightRookCertificate_accepted

end BlackPegExtraCheck
'''


def render_patch() -> str:
    module = render_module()
    added = "".join("+" + line for line in module.splitlines(keepends=True))
    if module and not module.endswith("\n"):
        added += "+\n"
    return (
        "*** Begin Patch\n"
        "*** Add File: /workspaces/black-peg-extra-check/BlackPegExtraCheck/"
        "SharpEightRookCertificate.lean\n"
        + added
        + "*** End Patch\n"
    )


if __name__ == "__main__":
    if "--patch" in argv:
        print(render_patch(), end="")
    else:
        print(f"candidates={len(search.FIBER)}")
        print(f"queries={len(queries)} depth_one={len(depth_one)} depth_two={len(depth_two)}")
        print("certificate simulation: accepted")
