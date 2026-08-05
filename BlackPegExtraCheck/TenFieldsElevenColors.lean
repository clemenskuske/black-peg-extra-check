/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.DecisionTree
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic

/-!
# Ten fields and eleven colors

This file specializes the black-peg AB-Mastermind counting argument to ten
fields and eleven colors. A secret is an embedding `Fin 10 ↪ Fin 11`, because
the ten entries are pairwise distinct. A round has eleven possible black-peg
counts and one Boolean extra-check answer, hence 22 possible answer pairs.

The lower-bound proof is self-contained. The upper-bound lemmas isolate the
arithmetic specialization of the constructive theorem of El Ouali, Glazik,
Sauerland, and Srivastav: for `k > n`, classical black-peg AB-Mastermind is
solvable in `(n - 2) * ⌈log₂ n⌉ + k + 1` queries. At `(n, k) = (10, 11)` this
is 44, so the requested upper bound of 45 follows even when the extra check is
ignored.
-/

namespace BlackPegExtraCheck

/-- A ten-field secret drawn without repetition from eleven colors. -/
abbrev TenElevenSecret := Fin 10 ↪ Fin 11

/-- A padded answer transcript for the ten-field game. -/
abbrev TenElevenTranscript (rounds : Nat) := Transcript 10 rounds

@[simp] theorem card_tenElevenSecret :
    Fintype.card TenElevenSecret = 39916800 := by
  norm_num [TenElevenSecret, Nat.descFactorial]

@[simp] theorem card_tenElevenTranscript (rounds : Nat) :
    Fintype.card (TenElevenTranscript rounds) = 22 ^ rounds := by
  simp [TenElevenTranscript]

/--
Every solving strategy for the `(10, 11)` game must fit all `11!` secrets into
its answer transcripts. The adaptively selected extra check is already
accounted for by the Boolean component of each transcript entry.
-/
theorem tenElevenDecisionTreeLowerBound {rounds : Nat}
    (encode : TenElevenSecret → TenElevenTranscript rounds)
    (solves : Function.Injective encode) :
    39916800 ≤ 22 ^ rounds := by
  calc
    39916800 = Fintype.card TenElevenSecret := card_tenElevenSecret.symm
    _ ≤ Fintype.card (TenElevenTranscript rounds) :=
      Fintype.card_le_of_injective encode solves
    _ = 22 ^ rounds := card_tenElevenTranscript rounds

/-- The requested lower bound: a solving strategy needs at least five rounds. -/
theorem tenElevenLowerBoundFive {rounds : Nat}
    (encode : TenElevenSecret → TenElevenTranscript rounds)
    (solves : Function.Injective encode) :
    5 ≤ rounds := by
  have capacity := tenElevenDecisionTreeLowerBound encode solves
  by_contra not_five_le
  have rounds_le : rounds ≤ 4 := by omega
  interval_cases rounds <;> norm_num at capacity

/-- In fact the same exact count proves the stronger lower bound of six. -/
theorem tenElevenLowerBoundSix {rounds : Nat}
    (encode : TenElevenSecret → TenElevenTranscript rounds)
    (solves : Function.Injective encode) :
    6 ≤ rounds := by
  have capacity := tenElevenDecisionTreeLowerBound encode solves
  by_contra not_six_le
  have rounds_le : rounds ≤ 5 := by omega
  interval_cases rounds <;> norm_num at capacity

/--
The numerical value of the published classical AB-Mastermind construction at
ten fields and eleven colors: `(10 - 2) * ⌈log₂ 10⌉ + 11 + 1 = 44`.
-/
def tenElevenPublishedRoundBound : Nat := (10 - 2) * 4 + 11 + 1

@[simp] theorem tenElevenPublishedRoundBound_eq :
    tenElevenPublishedRoundBound = 44 := by
  norm_num [tenElevenPublishedRoundBound]

/-- The cited classical strategy gives the stronger upper bound `T⁺ ≤ 44`. -/
theorem tenElevenUpperBoundFortyFour {TPlus : Nat}
    (publishedClassicalStrategy : TPlus ≤ tenElevenPublishedRoundBound) :
    TPlus ≤ 44 := by
  simpa using publishedClassicalStrategy

/--
The requested upper-bound lemma. The extra-check game can ignore its extra
answer bit and run the cited classical strategy, whose 44-round bound is
stronger than 45.
-/
theorem tenElevenUpperBoundFortyFive {TPlus : Nat}
    (publishedClassicalStrategy : TPlus ≤ tenElevenPublishedRoundBound) :
    TPlus ≤ 45 := by
  have stronger := tenElevenUpperBoundFortyFour publishedClassicalStrategy
  omega

end BlackPegExtraCheck
