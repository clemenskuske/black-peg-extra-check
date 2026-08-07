import Mathlib.Data.Fintype.Perm

/-!
---
title: Decision-tree lower bound for permutation Mastermind with an extra check
type: theorem
---
A secret is a permutation of `n` positions.  A round returns a black-peg count
in `{0, ..., n}` and one Boolean answer, so a padded transcript of `r` rounds
has alphabet size `2(n+1)` in every coordinate.  If a deterministic strategy
solves every secret, the map from secrets to complete transcripts is injective;
hence `n! ≤ (2(n+1))^r`.
-/

namespace Lax46.DecisionTree

/-- A secret permutation on `n` positions. -/
abbrev Secret (n : Nat) := Equiv.Perm (Fin n)

/-- The black-peg count, represented by one of `0, ..., n`. -/
abbrev BlackAnswer (n : Nat) := Fin (n + 1)

/-- One round returns a black-peg count and one Boolean extra-check bit. -/
abbrev RoundAnswer (n : Nat) := BlackAnswer n × Bool

/-- A padded transcript containing exactly `rounds` answers. -/
abbrev Transcript (n rounds : Nat) := Fin rounds → RoundAnswer n

/-- The information-theoretic decision-tree lower bound. -/
axiom decisionTreeLowerBound {n rounds : Nat}
    (encode : Secret n → Transcript n rounds)
    (solves : Function.Injective encode) :
    Nat.factorial n ≤ (2 * (n + 1)) ^ rounds

end Lax46.DecisionTree
