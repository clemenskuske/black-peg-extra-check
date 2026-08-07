import Lax46.DecisionTree
import Mathlib.Data.Fintype.CardEmbedding

/-!
---
title: Six-round information lower bound for ten fields and eleven colors
---
In the ten-field, eleven-color game, a secret is an injective assignment of a
color to every field.  A round has eleven possible black-peg counts and one
Boolean extra-check answer.  Any solving deterministic strategy therefore
encodes the `11!` secrets injectively into an alphabet of size `22` per round,
which is impossible in five or fewer rounds.
-/

namespace Lax46.TenElevenInformation

/-- A ten-field secret drawn without repetition from eleven colors. -/
abbrev Secret := Fin 10 ↪ Fin 11

/-- A padded answer transcript for the ten-field game. -/
abbrev Transcript (rounds : Nat) := Lax46.DecisionTree.Transcript 10 rounds

/-- Every injective transcript encoding of the game uses at least six rounds. -/
axiom lowerBoundSix {rounds : Nat}
    (encode : Secret → Transcript rounds)
    (solves : Function.Injective encode) :
    6 ≤ rounds

end Lax46.TenElevenInformation
