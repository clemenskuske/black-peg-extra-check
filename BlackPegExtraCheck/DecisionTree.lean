/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm

/-!
# Information lower bound for black-peg permutation Mastermind with an extra check

The game has `n!` possible secrets. In one round, the black-peg answer has at
most `n + 1` values and the extra coordinate check has two values. This remains
true when the coordinate check is selected after observing the black-peg answer.

Consequently, a solved deterministic strategy of depth `rounds` induces an
injective map from secrets to transcripts in an alphabet of size
`2 * (n + 1)`. The theorem `decisionTreeLowerBound` formalizes the resulting
cardinality inequality.
-/

namespace BlackPegExtraCheck

/-- A secret permutation on `n` positions. -/
abbrev Secret (n : Nat) := Equiv.Perm (Fin n)

/-- The black-peg count, represented by one of `0, ..., n`. -/
abbrev BlackAnswer (n : Nat) := Fin (n + 1)

/-- One round returns a black-peg count and one Boolean coordinate-check bit. -/
abbrev RoundAnswer (n : Nat) := BlackAnswer n × Bool

/-- A length-`rounds` transcript. Shorter plays can be padded after solving. -/
abbrev Transcript (n rounds : Nat) := Fin rounds → RoundAnswer n

@[simp] theorem card_secret (n : Nat) :
    Fintype.card (Secret n) = Nat.factorial n := by
  simp [Secret, Fintype.card_perm]

@[simp] theorem card_roundAnswer (n : Nat) :
    Fintype.card (RoundAnswer n) = 2 * (n + 1) := by
  simp [RoundAnswer, BlackAnswer, Nat.mul_comm]

@[simp] theorem card_transcript (n rounds : Nat) :
    Fintype.card (Transcript n rounds) = (2 * (n + 1)) ^ rounds := by
  simp [Transcript, Nat.mul_comm]

/--
The decision-tree lower bound. `encode` is the complete padded transcript
produced by a deterministic strategy. If the strategy always identifies the
secret, two distinct secrets cannot have the same transcript, so `encode` is
injective.
-/
theorem decisionTreeLowerBound {n rounds : Nat}
    (encode : Secret n → Transcript n rounds)
    (solves : Function.Injective encode) :
    Nat.factorial n ≤ (2 * (n + 1)) ^ rounds := by
  simpa [Nat.mul_comm] using Fintype.card_le_of_injective encode solves

end BlackPegExtraCheck
