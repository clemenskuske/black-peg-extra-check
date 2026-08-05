/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.DecisionTree
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Ten fields and eleven colors

This file specializes the black-peg AB-Mastermind counting argument to ten
fields and eleven colors. A secret is an embedding `Fin 10 ↪ Fin 11`, because
the ten entries are pairwise distinct. A round has eleven possible black-peg
counts and one Boolean extra-check answer, hence 22 possible answer pairs.

The information lower bound gives six rounds. A structural refinement gives
seven: after the first query, the zero-black branch contains a relabeled copy
of every derangement of eleven colors. One equality check removes at most
`10!` of these secrets, leaving too many for five further rounds.

For the upper bound, the file records both the published 44-round classical
bound and the 28-round cost of the hybrid protocol described in the proof
notes. The latter pipelines the extra equality checks through the paper's
four-round `findNext` routine.
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
  have power_le : 22 ^ rounds ≤ 22 ^ 4 :=
    Nat.pow_le_pow_right (by norm_num) rounds_le
  have impossible : 39916800 ≤ 22 ^ 4 := capacity.trans power_le
  norm_num at impossible

/-- In fact the same exact count proves the stronger lower bound of six. -/
theorem tenElevenLowerBoundSix {rounds : Nat}
    (encode : TenElevenSecret → TenElevenTranscript rounds)
    (solves : Function.Injective encode) :
    6 ≤ rounds := by
  have capacity := tenElevenDecisionTreeLowerBound encode solves
  by_contra not_six_le
  have rounds_le : rounds ≤ 5 := by omega
  have power_le : 22 ^ rounds ≤ 22 ^ 5 :=
    Nat.pow_le_pow_right (by norm_num) rounds_le
  have impossible : 39916800 ≤ 22 ^ 5 := capacity.trans power_le
  norm_num at impossible

/-! ## A structural seven-round lower bound -/

/-- Permutations of `Fin (n + 1)` are determined by their first `n` values. -/
theorem perm_eq_of_castSucc_eq {n : Nat} {σ τ : Equiv.Perm (Fin (n + 1))}
    (agree : ∀ i : Fin n, σ i.castSucc = τ i.castSucc) :
    σ = τ := by
  have agree_last : σ (Fin.last n) = τ (Fin.last n) := by
    obtain ⟨x, hx⟩ := τ.surjective (σ (Fin.last n))
    induction x using Fin.lastCases with
    | last => exact hx.symm
    | cast i =>
        have collision : σ i.castSucc = σ (Fin.last n) := (agree i).trans hx
        exact (Fin.castSucc_ne_last i (σ.injective collision)).elim
  apply Equiv.Perm.ext
  intro x
  induction x using Fin.lastCases with
  | last => exact agree_last
  | cast i => exact agree i

/-- Secrets producing zero black pegs against `guess`. -/
def ZeroBlackSecrets (guess : TenElevenSecret) :=
  {secret : TenElevenSecret // ∀ i, secret i ≠ guess i}

noncomputable instance (guess : TenElevenSecret) : Fintype (ZeroBlackSecrets guess) :=
  by
    classical
    exact Subtype.fintype _

/--
A permutation of the eleven colors that sends the canonical ten-color
inclusion to an arbitrary legal first guess.
-/
noncomputable def guessRelabeling (guess : TenElevenSecret) : Equiv.Perm (Fin 11) :=
  Classical.choose <| Equiv.Perm.exists_extending_pair
    (fun i : Fin 10 => i.castSucc) guess (Fin.castSucc_injective 10) guess.injective

@[simp] theorem guessRelabeling_apply (guess : TenElevenSecret) (i : Fin 10) :
    guessRelabeling guess i.castSucc = guess i := by
  exact (Classical.choose_spec <| Equiv.Perm.exists_extending_pair
    (fun i : Fin 10 => i.castSucc) guess (Fin.castSucc_injective 10) guess.injective) i

/-- Restrict a relabeled eleven-color derangement to the ten game fields. -/
noncomputable def derangementZeroSecret (guess : TenElevenSecret)
    (d : derangements (Fin 11)) : ZeroBlackSecrets guess := by
  let restricted : TenElevenSecret :=
    (Fin.castSuccEmb.trans d.1.toEmbedding).trans (guessRelabeling guess).toEmbedding
  refine ⟨restricted, ?_⟩
  intro i
  change guessRelabeling guess (d.1 i.castSucc) ≠ guess i
  rw [← guessRelabeling_apply guess i]
  intro collision
  exact d.2 i.castSucc ((guessRelabeling guess).injective collision)

/-- Restricting the derangements loses no information. -/
theorem derangementZeroSecret_injective (guess : TenElevenSecret) :
    Function.Injective (derangementZeroSecret guess) := by
  intro d e restricted_eq
  apply Subtype.ext
  apply perm_eq_of_castSucc_eq
  intro i
  apply (guessRelabeling guess).injective
  exact congrArg (fun secret : ZeroBlackSecrets guess => secret.1 i) restricted_eq

@[simp] theorem card_derangements_fin_eleven :
    Fintype.card (derangements (Fin 11)) = 14684570 := by
  rw [card_derangements_fin_eq_numDerangements]
  norm_num [numDerangements]

/-- Every zero-black branch contains at least all eleven-color derangements. -/
theorem card_zeroBlackSecrets_lower (guess : TenElevenSecret) :
    14684570 ≤ Fintype.card (ZeroBlackSecrets guess) := by
  rw [← card_derangements_fin_eleven]
  exact Fintype.card_le_of_injective
    (derangementZeroSecret guess) (derangementZeroSecret_injective guess)

/-- Secrets with a prescribed value at one coordinate. -/
def FixedCoordinateSecrets (i : Fin 10) (color : Fin 11) :=
  {secret : TenElevenSecret // secret i = color}

noncomputable instance (i : Fin 10) (color : Fin 11) :
    Fintype (FixedCoordinateSecrets i color) :=
  by
    classical
    exact Subtype.fintype _

/-- The other nine positions. -/
abbrev OtherPositions (i : Fin 10) := {j : Fin 10 // j ≠ i}

/-- The other ten colors. -/
abbrev OtherColors (color : Fin 11) := {c : Fin 11 // c ≠ color}

/-- Delete a prescribed coordinate and color from a fixed-coordinate secret. -/
def removeFixedCoordinate (i : Fin 10) (color : Fin 11) :
    FixedCoordinateSecrets i color → (OtherPositions i ↪ OtherColors color) :=
  fun secret =>
    { toFun := fun j =>
        ⟨secret.1 j.1, by
          intro equals_color
          have collision : secret.1 j.1 = secret.1 i :=
            equals_color.trans secret.2.symm
          exact j.2 (secret.1.injective collision)⟩
      inj' := fun _ _ equal_values =>
        Subtype.ext <| secret.1.injective <| congrArg Subtype.val equal_values }

/-- Deleting the fixed coordinate is injective. -/
theorem removeFixedCoordinate_injective (i : Fin 10) (color : Fin 11) :
    Function.Injective (removeFixedCoordinate i color) := by
  intro secret₁ secret₂ restrictions_equal
  apply Subtype.ext
  apply Function.Embedding.ext
  intro j
  by_cases hji : j = i
  · subst j
    exact secret₁.2.trans secret₂.2.symm
  · have restricted_equal := congrArg
      (fun restriction : OtherPositions i ↪ OtherColors color => restriction ⟨j, hji⟩)
      restrictions_equal
    exact congrArg Subtype.val restricted_equal

/-- At most `10!` secrets can answer true to one coordinate-equality check. -/
theorem card_fixedCoordinateSecrets_upper (i : Fin 10) (color : Fin 11) :
    Fintype.card (FixedCoordinateSecrets i color) ≤ 3628800 := by
  calc
    Fintype.card (FixedCoordinateSecrets i color)
        ≤ Fintype.card (OtherPositions i ↪ OtherColors color) :=
      Fintype.card_le_of_injective
        (removeFixedCoordinate i color) (removeFixedCoordinate_injective i color)
    _ = 3628800 := by
      rw [Fintype.card_embedding_eq]
      norm_num [OtherPositions, OtherColors, Nat.descFactorial]

/-- Zero-black secrets that also answer true to the selected equality check. -/
def ZeroTrueSecrets (guess : TenElevenSecret) (i : Fin 10) (color : Fin 11) :=
  {secret : ZeroBlackSecrets guess // secret.1 i = color}

noncomputable instance (guess : TenElevenSecret) (i : Fin 10) (color : Fin 11) :
    Fintype (ZeroTrueSecrets guess i color) :=
  by
    classical
    exact Subtype.fintype _

/-- Zero-black secrets that answer false to the selected equality check. -/
def ZeroFalseSecrets (guess : TenElevenSecret) (i : Fin 10) (color : Fin 11) :=
  {secret : ZeroBlackSecrets guess // secret.1 i ≠ color}

noncomputable instance (guess : TenElevenSecret) (i : Fin 10) (color : Fin 11) :
    Fintype (ZeroFalseSecrets guess i color) :=
  by
    classical
    exact Subtype.fintype _

/-- Forgetting the zero-black proof embeds the true branch into the full fiber. -/
def zeroTrueToFixed (guess : TenElevenSecret) (i : Fin 10) (color : Fin 11) :
    ZeroTrueSecrets guess i color → FixedCoordinateSecrets i color :=
  fun secret => ⟨secret.1.1, secret.2⟩

theorem zeroTrueToFixed_injective (guess : TenElevenSecret) (i : Fin 10)
    (color : Fin 11) :
    Function.Injective (zeroTrueToFixed guess i color) := by
  intro secret₁ secret₂ equal_fixed
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun secret : FixedCoordinateSecrets i color => secret.1) equal_fixed

/-- A true equality answer removes at most `10!` zero-black secrets. -/
theorem card_zeroTrueSecrets_upper (guess : TenElevenSecret) (i : Fin 10)
    (color : Fin 11) :
    Fintype.card (ZeroTrueSecrets guess i color) ≤ 3628800 := by
  exact (Fintype.card_le_of_injective
    (zeroTrueToFixed guess i color) (zeroTrueToFixed_injective guess i color)).trans
      (card_fixedCoordinateSecrets_upper i color)

/--
After any first query, the adversary may answer zero black pegs and `false` to
the selected equality check while retaining more than `22^5` secrets.
-/
theorem card_zeroFalseSecrets_large (guess : TenElevenSecret) (i : Fin 10)
    (color : Fin 11) :
    22 ^ 5 < Fintype.card (ZeroFalseSecrets guess i color) := by
  have zero_large := card_zeroBlackSecrets_lower guess
  have true_small := card_zeroTrueSecrets_upper guess i color
  have false_card := Fintype.card_subtype_compl
    (fun secret : ZeroBlackSecrets guess => secret.1 i = color)
  change Fintype.card (ZeroFalseSecrets guess i color) =
    Fintype.card (ZeroBlackSecrets guess) -
      Fintype.card (ZeroTrueSecrets guess i color) at false_card
  norm_num at zero_large true_small ⊢
  omega

/--
The structural lower bound `T⁺(10,11) ≥ 7`: no continuation of only five
rounds can solve the zero/false branch left by the first round of a six-round
strategy.
-/
theorem tenElevenLowerBoundSeven (firstGuess : TenElevenSecret)
    (checkPosition : Fin 10) (checkColor : Fin 11)
    (continuation : ZeroFalseSecrets firstGuess checkPosition checkColor →
      TenElevenTranscript 5)
    (solvesBranch : Function.Injective continuation) :
    False := by
  have capacity := Fintype.card_le_of_injective continuation solvesBranch
  rw [card_tenElevenTranscript] at capacity
  exact (Nat.not_lt_of_ge capacity)
    (card_zeroFalseSecrets_large firstGuess checkPosition checkColor)

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

/-! ## Hybrid upper bound using the extra checks -/

/--
Ten cyclic setup rounds, four padded `findNext` calls of four rounds each, and
two finishing rounds. The proof notes justify why the pipelined extra checks
reduce the open positions from nine to at most three during the four calls.
-/
def tenElevenHybridRoundBound : Nat := 10 + 3 * 4 + 4 + 2

@[simp] theorem tenElevenHybridRoundBound_eq :
    tenElevenHybridRoundBound = 28 := by
  norm_num [tenElevenHybridRoundBound]

/-- The hybrid protocol gives the improved upper bound `T⁺(10,11) ≤ 28`. -/
theorem tenElevenUpperBoundTwentyEight {TPlus : Nat}
    (hybridStrategy : TPlus ≤ tenElevenHybridRoundBound) :
    TPlus ≤ 28 := by
  simpa using hybridStrategy

end BlackPegExtraCheck
