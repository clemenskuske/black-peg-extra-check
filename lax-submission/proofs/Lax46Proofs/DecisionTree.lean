import Lax46.DecisionTree
import Mathlib.Data.Fintype.BigOperators

namespace Lax46Proofs.DecisionTree

open Lax46.DecisionTree

@[simp] theorem cardSecret (n : Nat) :
    Fintype.card (Secret n) = Nat.factorial n := by
  simp [Secret, Fintype.card_perm]

@[simp] theorem cardRoundAnswer (n : Nat) :
    Fintype.card (RoundAnswer n) = 2 * (n + 1) := by
  simp [RoundAnswer, BlackAnswer, Nat.mul_comm]

@[simp] theorem cardTranscript (n rounds : Nat) :
    Fintype.card (Transcript n rounds) = (2 * (n + 1)) ^ rounds := by
  simp [Transcript, Nat.mul_comm]

/--
---
conclusion: Lax46.DecisionTree.decisionTreeLowerBound
---
The injective transcript map embeds the finite type of permutations into the
finite transcript type.  Substituting their two cardinalities gives the stated
inequality.
-/
theorem decisionTreeLowerBound {n rounds : Nat}
    (encode : Secret n → Transcript n rounds)
    (solves : Function.Injective encode) :
    Nat.factorial n ≤ (2 * (n + 1)) ^ rounds := by
  simpa [Nat.mul_comm] using Fintype.card_le_of_injective encode solves

end Lax46Proofs.DecisionTree
