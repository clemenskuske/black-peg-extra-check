import Lax46.TenElevenInformation
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace Lax46Proofs.TenElevenInformation

open Lax46.TenElevenInformation

@[simp] theorem cardSecret : Fintype.card Secret = 39916800 := by
  norm_num [Secret, Nat.descFactorial]

@[simp] theorem cardTranscript (rounds : Nat) :
    Fintype.card (Transcript rounds) = 22 ^ rounds := by
  simp [Transcript, Lax46.DecisionTree.Transcript]

theorem transcriptCapacity {rounds : Nat}
    (encode : Secret → Transcript rounds)
    (solves : Function.Injective encode) :
    39916800 ≤ 22 ^ rounds := by
  calc
    39916800 = Fintype.card Secret := cardSecret.symm
    _ ≤ Fintype.card (Transcript rounds) :=
      Fintype.card_le_of_injective encode solves
    _ = 22 ^ rounds := cardTranscript rounds

/--
---
conclusion: Lax46.TenElevenInformation.lowerBoundSix
---
There are `39,916,800` secrets.  If at most five rounds were used, transcript
capacity would be at most `22^5 = 5,153,632`, contradicting injectivity.
-/
theorem lowerBoundSix {rounds : Nat}
    (encode : Secret → Transcript rounds)
    (solves : Function.Injective encode) :
    6 ≤ rounds := by
  have capacity := transcriptCapacity encode solves
  by_contra not_six_le
  have rounds_le : rounds ≤ 5 := by omega
  have power_le : 22 ^ rounds ≤ 22 ^ 5 :=
    Nat.pow_le_pow_right (by norm_num) rounds_le
  have impossible : 39916800 ≤ 22 ^ 5 := capacity.trans power_le
  norm_num at impossible

end Lax46Proofs.TenElevenInformation
