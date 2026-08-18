/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.DecisionTree
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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

The information lower bound gives six rounds. A first structural refinement
gives seven using a large zero/false branch. A response-fiber capacity
recurrence then proves eight: even if every later extra check were an arbitrary
Boolean predicate, six rounds distinguish at most `10,676,379` candidates,
fewer than the zero/false branch left after round one.

For the upper bound, the file records the arithmetic of the published
44-round classical bound and of shorter proposed allocations.  The arithmetic
definitions are not strategy theorems.  Exact cyclic composition and the
remaining separator premise are formalized separately in `CyclicStrategy`.
-/

namespace BlackPegExtraCheck

open scoped BigOperators

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

/-! ## A response-fiber capacity bound and the eight-round lower bound -/

/-- The positions where `secret` agrees with `guess`. -/
def MatchSet (guess secret : TenElevenSecret) : Finset (Fin 10) :=
  Finset.univ.filter fun i => secret i = guess i

/-- Secrets agreeing with `guess` throughout the prescribed position set. -/
noncomputable def FixedSetFinset (guess : TenElevenSecret) (S : Finset (Fin 10)) :
    Finset TenElevenSecret :=
  Finset.univ.filter fun secret => ∀ i ∈ S, secret i = guess i

/-- Positions outside a prescribed set. -/
abbrev RemainingPositions (S : Finset (Fin 10)) :=
  ↥(Finset.univ \ S)

/-- Colors not consumed by the prescribed matches. -/
abbrev RemainingColors (guess : TenElevenSecret) (S : Finset (Fin 10)) :=
  ↥(Finset.univ \ S.image guess)

/-- Delete all prescribed matches from a secret. -/
noncomputable def removeFixedSet (guess : TenElevenSecret) (S : Finset (Fin 10)) :
    ↥(FixedSetFinset guess S) →
      (RemainingPositions S ↪ RemainingColors guess S) :=
  fun secret =>
    { toFun := fun i =>
        ⟨secret.1 i.1, by
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_image, not_exists, not_and]
          intro j hj
          have fixed_j : secret.1 j = guess j :=
            (Finset.mem_filter.1 secret.2).2 j hj
          intro secret_i_eq_guess_j
          have collision : secret.1 i.1 = secret.1 j :=
            secret_i_eq_guess_j.symm.trans fixed_j.symm
          have hi_not : i.1 ∉ S := (Finset.mem_sdiff.1 i.property).2
          exact hi_not ((secret.1.injective collision) ▸ hj)⟩
      inj' := fun _ _ h => Subtype.ext (secret.1.injective (congrArg Subtype.val h)) }

theorem removeFixedSet_injective (guess : TenElevenSecret) (S : Finset (Fin 10)) :
    Function.Injective (removeFixedSet guess S) := by
  intro secret₁ secret₂ restrictions_equal
  apply Subtype.ext
  apply Function.Embedding.ext
  intro i
  by_cases hi : i ∈ S
  · have fixed₁ := (Finset.mem_filter.1 secret₁.2).2 i hi
    have fixed₂ := (Finset.mem_filter.1 secret₂.2).2 i hi
    exact fixed₁.trans fixed₂.symm
  · have restricted_equal := congrArg
      (fun restriction : RemainingPositions S ↪ RemainingColors guess S =>
        restriction ⟨i, by simp [hi]⟩)
      restrictions_equal
    exact congrArg Subtype.val restricted_equal

theorem card_remainingPositions (S : Finset (Fin 10)) :
    Fintype.card (RemainingPositions S) = 10 - S.card := by
  simp [RemainingPositions]

theorem card_remainingColors (guess : TenElevenSecret) (S : Finset (Fin 10)) :
    Fintype.card (RemainingColors guess S) = 11 - S.card := by
  rw [Fintype.card_coe, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  rw [Finset.card_image_of_injective _ guess.injective]

/-- Fixing `b` specified matches leaves at most `(11-b)!` extensions. -/
theorem card_fixedSetFinset_upper (guess : TenElevenSecret) (S : Finset (Fin 10)) :
    (FixedSetFinset guess S).card ≤
      (11 - S.card).descFactorial (10 - S.card) := by
  rw [← Fintype.card_coe]
  calc
    Fintype.card ↥(FixedSetFinset guess S) ≤
        Fintype.card (RemainingPositions S ↪ RemainingColors guess S) :=
      Fintype.card_le_of_injective (removeFixedSet guess S)
        (removeFixedSet_injective guess S)
    _ = (11 - S.card).descFactorial (10 - S.card) := by
      rw [Fintype.card_embedding_eq, card_remainingPositions, card_remainingColors]

noncomputable def BlackFiberFinset (guess : TenElevenSecret) (b : Nat) :
    Finset TenElevenSecret :=
  Finset.univ.filter fun secret => (MatchSet guess secret).card = b

theorem blackFiber_subset_fixedSet_union (guess : TenElevenSecret) (b : Nat) :
    BlackFiberFinset guess b ⊆
      ((Finset.univ : Finset (Fin 10)).powersetCard b).biUnion
        (FixedSetFinset guess) := by
  classical
  intro secret hsecret
  have hcard : (MatchSet guess secret).card = b :=
    (Finset.mem_filter.1 hsecret).2
  apply Finset.mem_biUnion.2
  refine ⟨MatchSet guess secret, ?_, ?_⟩
  · exact Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hcard⟩
  · apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i hi
    exact (Finset.mem_filter.1 hi).2

/--
A black-answer fiber with value `b` has at most
`choose 10 b * (11-b)!` secrets. This is a union bound over its match set, not
an enumeration of secrets.
-/
theorem card_blackFiberFinset_upper (guess : TenElevenSecret) (b : Nat) :
    (BlackFiberFinset guess b).card ≤
      Nat.choose 10 b * (11 - b).descFactorial (10 - b) := by
  classical
  calc
    (BlackFiberFinset guess b).card ≤
        ((Finset.univ.powersetCard b).biUnion (FixedSetFinset guess)).card :=
      Finset.card_le_card (blackFiber_subset_fixedSet_union guess b)
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin 10)).powersetCard b,
        (FixedSetFinset guess S).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ (Finset.univ : Finset (Fin 10)).powersetCard b,
        (11 - b).descFactorial (10 - b) := by
      exact Finset.sum_le_sum fun S hS => by
        have hcard : S.card = b := (Finset.mem_powersetCard.1 hS).2
        simpa [hcard] using card_fixedSetFinset_upper guess S
    _ = Nat.choose 10 b * (11 - b).descFactorial (10 - b) := by
      simp

def tenElevenBlackAnswer (guess secret : TenElevenSecret) : Fin 11 :=
  ⟨(MatchSet guess secret).card, by
    have hle : (MatchSet guess secret).card ≤ 10 := by
      exact (MatchSet guess secret).card_le_univ.trans_eq (by simp)
    omega⟩

def tenElevenBlackFiberCap (b : Fin 11) : Nat :=
  Nat.choose 10 b.1 * (11 - b.1).descFactorial (10 - b.1)

theorem card_tenElevenBlackFiber_upper (guess : TenElevenSecret) (b : Fin 11) :
    (Finset.univ.filter fun secret => tenElevenBlackAnswer guess secret = b).card ≤
      tenElevenBlackFiberCap b := by
  have subset :
      (Finset.univ.filter fun secret => tenElevenBlackAnswer guess secret = b) ⊆
        BlackFiberFinset guess b.1 := by
    intro secret hsecret
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, ?_⟩
    exact congrArg Fin.val (Finset.mem_filter.1 hsecret).2
  exact (Finset.card_le_card subset).trans (card_blackFiberFinset_upper guess b.1)

/-! ### Sharper high-response fiber bounds -/

/--
There is only one color outside the range of a ten-color guess.  Consequently,
any two colors that both avoid every entry of the guess are equal.
-/
theorem color_eq_of_avoids_guess (guess : TenElevenSecret) {c d : Fin 11}
    (hc : ∀ i, c ≠ guess i) (hd : ∀ i, d ≠ guess i) : c = d := by
  have hc_last : (guessRelabeling guess).symm c = Fin.last 10 := by
    generalize hx : (guessRelabeling guess).symm c = x
    induction x using Fin.lastCases with
    | last => rfl
    | cast i =>
        exfalso
        apply hc i
        have relabeled := congrArg (guessRelabeling guess) hx
        simpa using relabeled
  have hd_last : (guessRelabeling guess).symm d = Fin.last 10 := by
    generalize hx : (guessRelabeling guess).symm d = x
    induction x using Fin.lastCases with
    | last => rfl
    | cast i =>
        exfalso
        apply hd i
        have relabeled := congrArg (guessRelabeling guess) hx
        simpa using relabeled
  exact (guessRelabeling guess).symm.injective (hc_last.trans hd_last.symm)

/-- The unique color omitted by a ten-color injection. -/
noncomputable def omittedColor (guess : TenElevenSecret) : Fin 11 :=
  guessRelabeling guess (Fin.last 10)

theorem omittedColor_ne_guess (guess : TenElevenSecret) (i : Fin 10) :
    omittedColor guess ≠ guess i := by
  rw [omittedColor, ← guessRelabeling_apply guess i]
  intro equal
  exact Fin.castSucc_ne_last i ((guessRelabeling guess).injective equal).symm

/-- Replace one entry of a guess by its omitted color. -/
noncomputable def replaceWithOmitted (guess : TenElevenSecret) (i : Fin 10) :
    TenElevenSecret where
  toFun j := if j = i then omittedColor guess else guess j
  inj' := by
    intro a b equal
    by_cases hai : a = i
    · subst a
      by_cases hbi : b = i
      · exact hbi.symm
      · exfalso
        have collision : omittedColor guess = guess b := by
          simpa [hbi] using equal
        exact omittedColor_ne_guess guess b collision
    · by_cases hbi : b = i
      · subst b
        exfalso
        have collision : guess a = omittedColor guess := by
          simpa [hai] using equal
        exact omittedColor_ne_guess guess a collision.symm
      · exact guess.injective (by simpa [hai, hbi] using equal)

@[simp] theorem replaceWithOmitted_apply_same (guess : TenElevenSecret)
    (i : Fin 10) : replaceWithOmitted guess i i = omittedColor guess := by
  change (if i = i then omittedColor guess else guess i) = omittedColor guess
  simp

@[simp] theorem replaceWithOmitted_apply_ne (guess : TenElevenSecret)
    {i j : Fin 10} (hji : j ≠ i) :
    replaceWithOmitted guess i j = guess j := by
  change (if j = i then omittedColor guess else guess j) = guess j
  rw [if_neg hji]

theorem replaceWithOmitted_ne_guess (guess : TenElevenSecret) (i : Fin 10) :
    replaceWithOmitted guess i ≠ guess := by
  intro equal
  have at_i := congrArg (fun secret : TenElevenSecret => secret i) equal
  exact omittedColor_ne_guess guess i (by simpa using at_i)

theorem replaceWithOmitted_injective (guess : TenElevenSecret) :
    Function.Injective (replaceWithOmitted guess) := by
  intro i j equal
  by_contra hij
  have at_i := congrArg (fun secret : TenElevenSecret => secret i) equal
  have collision : omittedColor guess = guess i := by
    simpa [hij] using at_i
  exact omittedColor_ne_guess guess i collision

@[simp] theorem matchSet_replaceWithOmitted (guess : TenElevenSecret)
    (i : Fin 10) :
    MatchSet guess (replaceWithOmitted guess i) = Finset.univ.erase i := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [MatchSet, omittedColor_ne_guess]
  · simp [MatchSet, hji]

/--
Secrets whose unique nonmatch against `guess` is at `i`.  Nine matches force
the remaining entry to be the unique color omitted by `guess`.
-/
noncomputable def NineMatchFinset (guess : TenElevenSecret) (i : Fin 10) :
    Finset TenElevenSecret :=
  Finset.univ.filter fun secret =>
    secret i ≠ guess i ∧ ∀ j, j ≠ i → secret j = guess j

theorem card_nineMatchFinset_le_one (guess : TenElevenSecret) (i : Fin 10) :
    (NineMatchFinset guess i).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro secret hsecret other hother
  have hs := (Finset.mem_filter.1 hsecret).2
  have ho := (Finset.mem_filter.1 hother).2
  apply Function.Embedding.ext
  intro j
  by_cases hji : j = i
  · subst j
    apply color_eq_of_avoids_guess guess
    · intro k
      by_cases hki : k = i
      · subst k
        exact hs.1
      · intro collision
        have at_k : secret k = guess k := hs.2 k hki
        have same_value : secret i = secret k := collision.trans at_k.symm
        exact hki (secret.injective same_value).symm
    · intro k
      by_cases hki : k = i
      · subst k
        exact ho.1
      · intro collision
        have at_k : other k = guess k := ho.2 k hki
        have same_value : other i = other k := collision.trans at_k.symm
        exact hki (other.injective same_value).symm
  · exact (hs.2 j hji).trans (ho.2 j hji).symm

/-- A black response of nine has at most ten secrets, one per nonmatching field. -/
theorem card_blackFiberFinset_nine_upper (guess : TenElevenSecret) :
    (BlackFiberFinset guess 9).card ≤ 10 := by
  classical
  let cover : Finset TenElevenSecret :=
    (Finset.univ : Finset (Fin 10)).biUnion (NineMatchFinset guess)
  have subset : BlackFiberFinset guess 9 ⊆ cover := by
    intro secret hsecret
    have match_card : (MatchSet guess secret).card = 9 :=
      (Finset.mem_filter.1 hsecret).2
    have exists_nonmatch : ∃ i : Fin 10, i ∉ MatchSet guess secret := by
      by_contra all_match
      have every_match : ∀ i : Fin 10, i ∈ MatchSet guess secret := by
        intro i
        by_contra hi
        exact all_match ⟨i, hi⟩
      have all : MatchSet guess secret = Finset.univ :=
        Finset.eq_univ_of_forall every_match
      rw [all] at match_card
      norm_num at match_card
    obtain ⟨i, hi⟩ := exists_nonmatch
    have match_subset : MatchSet guess secret ⊆
        (Finset.univ : Finset (Fin 10)).erase i := by
      intro j hj
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro hji
      subst j
      exact hi hj
    have erase_card : ((Finset.univ : Finset (Fin 10)).erase i).card = 9 := by simp
    have match_eq_erase : MatchSet guess secret =
        (Finset.univ : Finset (Fin 10)).erase i := by
      apply Finset.eq_of_subset_of_card_le match_subset
      omega
    apply Finset.mem_biUnion.2
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa [MatchSet] using hi
    · intro j hji
      have hj : j ∈ (Finset.univ : Finset (Fin 10)).erase i := by simp [hji]
      rw [← match_eq_erase] at hj
      exact (Finset.mem_filter.1 hj).2
  calc
    (BlackFiberFinset guess 9).card ≤ cover.card := Finset.card_le_card subset
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin 10)), (NineMatchFinset guess i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin 10)), 1 := by
      exact Finset.sum_le_sum fun i _hi => card_nineMatchFinset_le_one guess i
    _ = 10 := by simp

/-- Secrets whose exact match set against `guess` is `S`. -/
noncomputable def ExactMatchSetFinset (guess : TenElevenSecret)
    (S : Finset (Fin 10)) : Finset TenElevenSecret :=
  Finset.univ.filter fun secret => MatchSet guess secret = S

theorem exactMatchSet_subset_fixedSet (guess : TenElevenSecret)
    (S : Finset (Fin 10)) :
    ExactMatchSetFinset guess S ⊆ FixedSetFinset guess S := by
  intro secret hsecret
  have exact : MatchSet guess secret = S :=
    (Finset.mem_filter.1 hsecret).2
  apply Finset.mem_filter.2
  refine ⟨Finset.mem_univ _, ?_⟩
  intro i hi
  have hmatch : i ∈ MatchSet guess secret := by
    rw [exact]
    exact hi
  exact (Finset.mem_filter.1 hmatch).2

/-- Three explicit extensions that have at least one match outside `S`. -/
noncomputable def ThreeNonExactExtensions (guess : TenElevenSecret)
    (S : Finset (Fin 10)) : Finset TenElevenSecret :=
  insert guess ((Finset.univ \ S).image (replaceWithOmitted guess))

theorem card_threeNonExactExtensions (guess : TenElevenSecret)
    (S : Finset (Fin 10)) (hS : S.card = 8) :
    (ThreeNonExactExtensions guess S).card = 3 := by
  classical
  have guess_not_image :
      guess ∉ (Finset.univ \ S).image (replaceWithOmitted guess) := by
    intro hguess
    obtain ⟨i, _hi, equal⟩ := Finset.mem_image.1 hguess
    exact replaceWithOmitted_ne_guess guess i equal
  rw [ThreeNonExactExtensions, Finset.card_insert_of_notMem guess_not_image,
    Finset.card_image_of_injective _ (replaceWithOmitted_injective guess)]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  simp [hS]

theorem threeNonExactExtensions_subset_sdiff (guess : TenElevenSecret)
    (S : Finset (Fin 10)) (hS : S.card = 8) :
    ThreeNonExactExtensions guess S ⊆
      FixedSetFinset guess S \ ExactMatchSetFinset guess S := by
  intro secret hsecret
  apply Finset.mem_sdiff.2
  rw [ThreeNonExactExtensions] at hsecret
  rcases Finset.mem_insert.1 hsecret with hsame | hreplacement
  · subst secret
    refine ⟨by simp [FixedSetFinset], ?_⟩
    intro hguess
    have exact : MatchSet guess guess = S :=
      (Finset.mem_filter.1 hguess).2
    have match_all : MatchSet guess guess = Finset.univ := by
      ext i
      simp [MatchSet]
    have : S.card = 10 := by
      rw [← exact, match_all]
      simp
    omega
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hreplacement
    have hi_not : i ∉ S := (Finset.mem_sdiff.1 hi).2
    constructor
    · apply Finset.mem_filter.2
      refine ⟨Finset.mem_univ _, ?_⟩
      intro j hj
      apply replaceWithOmitted_apply_ne
      intro hji
      subst j
      exact hi_not hj
    · intro hexact
      have exact : MatchSet guess (replaceWithOmitted guess i) = S :=
        (Finset.mem_filter.1 hexact).2
      have match_card : (MatchSet guess (replaceWithOmitted guess i)).card = 9 := by
        rw [matchSet_replaceWithOmitted]
        simp
      have same_card := congrArg Finset.card exact
      omega

/-- For eight prescribed matches, precisely nonmatching leaves at most three extensions. -/
theorem card_exactMatchSetFinset_eight_upper (guess : TenElevenSecret)
    (S : Finset (Fin 10)) (hS : S.card = 8) :
    (ExactMatchSetFinset guess S).card ≤ 3 := by
  have witnesses := Finset.card_le_card
    (threeNonExactExtensions_subset_sdiff guess S hS)
  rw [card_threeNonExactExtensions guess S hS] at witnesses
  have difference := Finset.card_sdiff_of_subset
    (exactMatchSet_subset_fixedSet guess S)
  have fixed_upper := card_fixedSetFinset_upper guess S
  rw [hS] at fixed_upper
  norm_num at fixed_upper
  omega

set_option maxRecDepth 2000 in
/-- A black response of eight has at most `choose(10,8) * 3 = 135` secrets. -/
theorem card_blackFiberFinset_eight_upper (guess : TenElevenSecret) :
    (BlackFiberFinset guess 8).card ≤ 135 := by
  classical
  have subset : BlackFiberFinset guess 8 ⊆
      ((Finset.univ : Finset (Fin 10)).powersetCard 8).biUnion
        (ExactMatchSetFinset guess) := by
    intro secret hsecret
    have match_card : (MatchSet guess secret).card = 8 :=
      (Finset.mem_filter.1 hsecret).2
    refine Finset.mem_biUnion.mpr ⟨MatchSet guess secret, ?_, ?_⟩
    · exact Finset.mem_powersetCard.2
        ⟨Finset.subset_univ _, match_card⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  calc
    (BlackFiberFinset guess 8).card ≤
        (((Finset.univ : Finset (Fin 10)).powersetCard 8).biUnion
          (ExactMatchSetFinset guess)).card := Finset.card_le_card subset
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin 10)).powersetCard 8,
        (ExactMatchSetFinset guess S).card := Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ (Finset.univ : Finset (Fin 10)).powersetCard 8, 3 := by
      apply Finset.sum_le_sum
      intro S hS
      exact card_exactMatchSetFinset_eight_upper guess S
        (Finset.mem_powersetCard.1 hS).2
    _ = 135 := by norm_num [Nat.choose]

/--
A black-fiber cap specialized to short continuations.  Responses eight and
nine are sharpened because the general match-set union bound also counts
extensions having additional matches.
-/
def tenElevenShortBlackFiberCap (b : Fin 11) : Nat :=
  if b.1 = 9 then 10
  else if b.1 = 8 then 135
  else tenElevenBlackFiberCap b

theorem card_tenElevenShortBlackFiber_upper (guess : TenElevenSecret) (b : Fin 11) :
    (Finset.univ.filter fun secret => tenElevenBlackAnswer guess secret = b).card ≤
      tenElevenShortBlackFiberCap b := by
  by_cases hb : b.1 = 9
  · rw [tenElevenShortBlackFiberCap, if_pos hb]
    have subset :
        (Finset.univ.filter fun secret => tenElevenBlackAnswer guess secret = b) ⊆
          BlackFiberFinset guess 9 := by
      intro secret hsecret
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_univ _, ?_⟩
      have answer_eq := congrArg Fin.val (Finset.mem_filter.1 hsecret).2
      exact answer_eq.trans hb
    exact (Finset.card_le_card subset).trans (card_blackFiberFinset_nine_upper guess)
  · rw [tenElevenShortBlackFiberCap, if_neg hb]
    by_cases hb8 : b.1 = 8
    · rw [if_pos hb8]
      have subset :
          (Finset.univ.filter fun secret => tenElevenBlackAnswer guess secret = b) ⊆
            BlackFiberFinset guess 8 := by
        intro secret hsecret
        apply Finset.mem_filter.2
        refine ⟨Finset.mem_univ _, ?_⟩
        have answer_eq := congrArg Fin.val (Finset.mem_filter.1 hsecret).2
        exact answer_eq.trans hb8
      exact (Finset.card_le_card subset).trans
        (card_blackFiberFinset_eight_upper guess)
    · rw [if_neg hb8]
      exact card_tenElevenBlackFiber_upper guess b

/--
A relaxed strategy still uses legal black queries, but its extra bit may be an
arbitrary Boolean predicate. Bounding this stronger game also bounds the real
coordinate-equality game.
-/
inductive TenElevenRelaxedStrategy : Nat → Type
  | leaf : TenElevenRelaxedStrategy 0
  | node {rounds : Nat}
      (guess : TenElevenSecret)
      (extra : Fin 11 → TenElevenSecret → Bool)
      (next : Fin 11 → Bool → TenElevenRelaxedStrategy rounds) :
      TenElevenRelaxedStrategy (rounds + 1)

namespace TenElevenRelaxedStrategy

noncomputable def blackBranch (candidates : Finset TenElevenSecret)
    (guess : TenElevenSecret) (b : Fin 11) : Finset TenElevenSecret :=
  candidates.filter fun secret => tenElevenBlackAnswer guess secret = b

noncomputable def answerBranch (candidates : Finset TenElevenSecret)
    (guess : TenElevenSecret) (extra : Fin 11 → TenElevenSecret → Bool)
    (b : Fin 11) (bit : Bool) : Finset TenElevenSecret :=
  (blackBranch candidates guess b).filter fun secret => extra b secret = bit

def Solves : {rounds : Nat} →
    TenElevenRelaxedStrategy rounds → Finset TenElevenSecret → Prop
  | 0, .leaf, candidates => candidates.card ≤ 1
  | _ + 1, .node guess extra next, candidates =>
      ∀ b bit, (next b bit).Solves (answerBranch candidates guess extra b bit)

end TenElevenRelaxedStrategy

/-- Universal candidate capacity for the relaxed game. -/
def tenElevenRelaxedCapacity : Nat → Nat
  | 0 => 1
  | rounds + 1 => ∑ b : Fin 11,
      min (tenElevenBlackFiberCap b) (2 * tenElevenRelaxedCapacity rounds)

@[simp] theorem tenElevenRelaxedCapacity_six :
    tenElevenRelaxedCapacity 6 = 10676379 := by
  decide

theorem TenElevenRelaxedStrategy.card_le_capacity {rounds : Nat}
    (tree : TenElevenRelaxedStrategy rounds) (candidates : Finset TenElevenSecret)
    (solves : tree.Solves candidates) :
    candidates.card ≤ tenElevenRelaxedCapacity rounds := by
  induction tree generalizing candidates with
  | leaf => exact solves
  | @node rounds guess extra next ih =>
      rw [tenElevenRelaxedCapacity]
      rw [Finset.card_eq_sum_card_fiberwise
        (s := candidates) (t := Finset.univ)
        (f := tenElevenBlackAnswer guess) (by simp)]
      apply Finset.sum_le_sum
      intro b _hb
      apply le_min
      · apply (Finset.card_le_card ?_).trans (card_tenElevenBlackFiber_upper guess b)
        intro secret hsecret
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hsecret).2⟩
      · change (TenElevenRelaxedStrategy.blackBranch candidates guess b).card ≤ _
        rw [Finset.card_eq_sum_card_fiberwise
          (s := TenElevenRelaxedStrategy.blackBranch candidates guess b)
          (t := Finset.univ) (f := extra b) (by
            intro _secret _hsecret
            exact Finset.mem_univ _)]
        change (∑ bit : Bool,
          (TenElevenRelaxedStrategy.answerBranch candidates guess extra b bit).card) ≤ _
        calc
          ∑ bit : Bool,
              (TenElevenRelaxedStrategy.answerBranch candidates guess extra b bit).card
              ≤ ∑ _bit : Bool, tenElevenRelaxedCapacity rounds := by
            apply Finset.sum_le_sum
            intro bit _hbit
            exact ih b bit
              (TenElevenRelaxedStrategy.answerBranch candidates guess extra b bit)
              (solves b bit)
          _ = 2 * tenElevenRelaxedCapacity rounds := by simp

/--
Short-horizon capacity using the refined fibers for black responses eight and
nine.  The improvement first matters in round two and will be used to audit a
five-round zero/false adversary for a prospective nine-round lower bound.
-/
def tenElevenShortCapacity : Nat → Nat
  | 0 => 1
  | rounds + 1 => ∑ b : Fin 11,
      min (tenElevenShortBlackFiberCap b) (2 * tenElevenShortCapacity rounds)

@[simp] theorem tenElevenShortCapacity_three :
    tenElevenShortCapacity 3 = 6370 := by
  decide

@[simp] theorem tenElevenShortCapacity_four :
    tenElevenShortCapacity 4 = 92206 := by
  decide

theorem TenElevenRelaxedStrategy.card_le_shortCapacity {rounds : Nat}
    (tree : TenElevenRelaxedStrategy rounds) (candidates : Finset TenElevenSecret)
    (solves : tree.Solves candidates) :
    candidates.card ≤ tenElevenShortCapacity rounds := by
  induction tree generalizing candidates with
  | leaf => exact solves
  | @node rounds guess extra next ih =>
      rw [tenElevenShortCapacity]
      rw [Finset.card_eq_sum_card_fiberwise
        (s := candidates) (t := Finset.univ)
        (f := tenElevenBlackAnswer guess) (by simp)]
      apply Finset.sum_le_sum
      intro b _hb
      apply le_min
      · apply (Finset.card_le_card ?_).trans
          (card_tenElevenShortBlackFiber_upper guess b)
        intro secret hsecret
        exact Finset.mem_filter.2
          ⟨Finset.mem_univ _, (Finset.mem_filter.1 hsecret).2⟩
      · change (TenElevenRelaxedStrategy.blackBranch candidates guess b).card ≤ _
        rw [Finset.card_eq_sum_card_fiberwise
          (s := TenElevenRelaxedStrategy.blackBranch candidates guess b)
          (t := Finset.univ) (f := extra b) (by
            intro _secret _hsecret
            exact Finset.mem_univ _)]
        change (∑ bit : Bool,
          (TenElevenRelaxedStrategy.answerBranch candidates guess extra b bit).card) ≤ _
        calc
          ∑ bit : Bool,
              (TenElevenRelaxedStrategy.answerBranch candidates guess extra b bit).card
              ≤ ∑ _bit : Bool, tenElevenShortCapacity rounds := by
            apply Finset.sum_le_sum
            intro bit _hbit
            exact ih b bit
              (TenElevenRelaxedStrategy.answerBranch candidates guess extra b bit)
              (solves b bit)
          _ = 2 * tenElevenShortCapacity rounds := by simp

/-- No relaxed three-round continuation can distinguish 6,371 candidates. -/
theorem no_three_round_continuation_of_large
    (tree : TenElevenRelaxedStrategy 3) (candidates : Finset TenElevenSecret)
    (large : 6370 < candidates.card) : ¬ tree.Solves candidates := by
  intro solves
  have upper := tree.card_le_shortCapacity candidates solves
  rw [tenElevenShortCapacity_three] at upper
  omega

/-- No relaxed four-round continuation can distinguish 92,207 candidates. -/
theorem no_four_round_continuation_of_large
    (tree : TenElevenRelaxedStrategy 4) (candidates : Finset TenElevenSecret)
    (large : 92206 < candidates.card) : ¬ tree.Solves candidates := by
  intro solves
  have upper := tree.card_le_shortCapacity candidates solves
  rw [tenElevenShortCapacity_four] at upper
  omega

noncomputable def ZeroFalseFinset (guess : TenElevenSecret) (i : Fin 10)
    (color : Fin 11) : Finset TenElevenSecret :=
  Finset.univ.filter fun secret =>
    (∀ j, secret j ≠ guess j) ∧ secret i ≠ color

noncomputable def zeroFalseFinsetEquiv (guess : TenElevenSecret) (i : Fin 10)
    (color : Fin 11) :
    ↥(ZeroFalseFinset guess i color) ≃ ZeroFalseSecrets guess i color where
  toFun secret := by
    have properties := (Finset.mem_filter.1 secret.2).2
    exact ⟨⟨secret.1, properties.1⟩, properties.2⟩
  invFun secret :=
    ⟨secret.1.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, secret.1.2, secret.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem card_zeroFalseFinset (guess : TenElevenSecret) (i : Fin 10)
    (color : Fin 11) :
    (ZeroFalseFinset guess i color).card =
      Fintype.card (ZeroFalseSecrets guess i color) := by
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (zeroFalseFinsetEquiv guess i color)

theorem card_zeroFalseFinset_exceeds_capacity_six (guess : TenElevenSecret)
    (i : Fin 10) (color : Fin 11) :
    tenElevenRelaxedCapacity 6 < (ZeroFalseFinset guess i color).card := by
  rw [card_zeroFalseFinset, tenElevenRelaxedCapacity_six]
  have zero_large := card_zeroBlackSecrets_lower guess
  have true_small := card_zeroTrueSecrets_upper guess i color
  have false_card := Fintype.card_subtype_compl
    (fun secret : ZeroBlackSecrets guess => secret.1 i = color)
  change Fintype.card (ZeroFalseSecrets guess i color) =
    Fintype.card (ZeroBlackSecrets guess) -
      Fintype.card (ZeroTrueSecrets guess i color) at false_card
  omega

theorem tenElevenBlackAnswer_eq_zero_iff (guess secret : TenElevenSecret) :
    tenElevenBlackAnswer guess secret = 0 ↔ ∀ i, secret i ≠ guess i := by
  constructor
  · intro answer_zero i equal_at_i
    have card_zero : (MatchSet guess secret).card = 0 :=
      congrArg Fin.val answer_zero
    have set_empty : MatchSet guess secret = ∅ := Finset.card_eq_zero.1 card_zero
    have member : i ∈ MatchSet guess secret := by simp [MatchSet, equal_at_i]
    rw [set_empty] at member
    simp at member
  · intro no_matches
    apply Fin.ext
    simp [tenElevenBlackAnswer, MatchSet, no_matches]

/-- Legal adaptive strategies with a coordinate-equality extra check. -/
inductive TenElevenStrategy : Nat → Type
  | leaf : TenElevenStrategy 0
  | node {rounds : Nat}
      (guess : TenElevenSecret)
      (check : Fin 11 → Fin 10 × Fin 11)
      (next : Fin 11 → Bool → TenElevenStrategy rounds) :
      TenElevenStrategy (rounds + 1)

def TenElevenStrategy.toRelaxed : {rounds : Nat} →
    TenElevenStrategy rounds → TenElevenRelaxedStrategy rounds
  | 0, .leaf => .leaf
  | _ + 1, .node guess check next =>
      .node guess
        (fun b secret => decide (secret (check b).1 = (check b).2))
        (fun b bit => (next b bit).toRelaxed)

def TenElevenStrategy.Solves {rounds : Nat} (tree : TenElevenStrategy rounds)
    (candidates : Finset TenElevenSecret) : Prop :=
  tree.toRelaxed.Solves candidates

theorem first_zero_false_branch (guess : TenElevenSecret)
    (check : Fin 11 → Fin 10 × Fin 11) :
    TenElevenRelaxedStrategy.answerBranch Finset.univ guess
        (fun b secret => decide (secret (check b).1 = (check b).2)) 0 false =
      ZeroFalseFinset guess (check 0).1 (check 0).2 := by
  classical
  ext secret
  simp [TenElevenRelaxedStrategy.answerBranch,
    TenElevenRelaxedStrategy.blackBranch, ZeroFalseFinset,
    tenElevenBlackAnswer_eq_zero_iff]

/--
The structural lower bound `T⁺(10,11) ≥ 8`: no legal seven-round strategy
solves every secret. Any shorter strategy can be padded to seven rounds.
-/
theorem tenElevenLowerBoundEight
    (tree : TenElevenStrategy 7) (solves : tree.Solves Finset.univ) : False := by
  cases tree with
  | node guess check next =>
      have branch_solves := solves (0 : Fin 11) false
      rw [first_zero_false_branch guess check] at branch_solves
      have upper := TenElevenRelaxedStrategy.card_le_capacity
        ((next 0 false).toRelaxed)
        (ZeroFalseFinset guess (check 0).1 (check 0).2) branch_solves
      have upper' :
          (ZeroFalseFinset guess (check 0).1 (check 0).2).card ≤
            tenElevenRelaxedCapacity 6 := by
        simpa using upper
      have lower := card_zeroFalseFinset_exceeds_capacity_six
        guess (check 0).1 (check 0).2
      omega

/-! ### Exact reduction of a nine-round lower bound to five zero/false rounds -/

/-- Apply one legal zero-black/false-check response to a candidate set. -/
noncomputable def zeroFalseStep (candidates : Finset TenElevenSecret)
    (guess : TenElevenSecret) (edge : Fin 10 × Fin 11) : Finset TenElevenSecret :=
  TenElevenRelaxedStrategy.answerBranch candidates guess
    (fun _b secret => decide (secret edge.1 = edge.2)) 0 false

@[simp] theorem mem_zeroFalseStep (candidates : Finset TenElevenSecret)
    (guess : TenElevenSecret) (edge : Fin 10 × Fin 11)
    (secret : TenElevenSecret) :
    secret ∈ zeroFalseStep candidates guess edge ↔
      secret ∈ candidates ∧
      (∀ i, secret i ≠ guess i) ∧ secret edge.1 ≠ edge.2 := by
  simp [zeroFalseStep, TenElevenRelaxedStrategy.answerBranch,
    TenElevenRelaxedStrategy.blackBranch, tenElevenBlackAnswer_eq_zero_iff,
    and_assoc]

/-- The survivors of five consecutive zero-black/false-check responses. -/
noncomputable def FiveZeroFalseFinset
    (guess₀ guess₁ guess₂ guess₃ guess₄ : TenElevenSecret)
    (edge₀ edge₁ edge₂ edge₃ edge₄ : Fin 10 × Fin 11) :
    Finset TenElevenSecret :=
  zeroFalseStep
    (zeroFalseStep
      (zeroFalseStep
        (zeroFalseStep
          (zeroFalseStep Finset.univ guess₀ edge₀) guess₁ edge₁)
        guess₂ edge₂)
      guess₃ edge₃)
    guess₄ edge₄

/-- The survivors of four consecutive zero-black/false-check responses. -/
noncomputable def FourZeroFalseFinset
    (guess₀ guess₁ guess₂ guess₃ : TenElevenSecret)
    (edge₀ edge₁ edge₂ edge₃ : Fin 10 × Fin 11) : Finset TenElevenSecret :=
  zeroFalseStep
    (zeroFalseStep
      (zeroFalseStep
        (zeroFalseStep Finset.univ guess₀ edge₀) guess₁ edge₁)
      guess₂ edge₂)
    guess₃ edge₃

/--
Conditional adversary reduction for the open ninth round.  It does not assume
the desired conclusion: its sole hypothesis is the concrete intersection
statement that every five-query zero/false survivor set has more than the
refined three-round capacity `6370`.
-/
theorem tenElevenLowerBoundNine_of_fiveZeroFalse_large
    (fiveZeroFalseLarge :
      ∀ (guess₀ guess₁ guess₂ guess₃ guess₄ : TenElevenSecret)
        (edge₀ edge₁ edge₂ edge₃ edge₄ : Fin 10 × Fin 11),
        6370 < (FiveZeroFalseFinset guess₀ guess₁ guess₂ guess₃ guess₄
          edge₀ edge₁ edge₂ edge₃ edge₄).card)
    (tree : TenElevenStrategy 8) (solves : tree.Solves Finset.univ) : False := by
  cases tree with
  | node guess₀ check₀ next₀ =>
      have solves₁ := solves (0 : Fin 11) false
      cases tree₁ : next₀ 0 false with
      | node guess₁ check₁ next₁ =>
          change (next₀ 0 false).toRelaxed.Solves _ at solves₁
          rw [tree₁] at solves₁
          have solves₂ := solves₁ (0 : Fin 11) false
          cases tree₂ : next₁ 0 false with
          | node guess₂ check₂ next₂ =>
              change (next₁ 0 false).toRelaxed.Solves _ at solves₂
              rw [tree₂] at solves₂
              have solves₃ := solves₂ (0 : Fin 11) false
              cases tree₃ : next₂ 0 false with
              | node guess₃ check₃ next₃ =>
                  change (next₂ 0 false).toRelaxed.Solves _ at solves₃
                  rw [tree₃] at solves₃
                  have solves₄ := solves₃ (0 : Fin 11) false
                  cases tree₄ : next₃ 0 false with
                  | node guess₄ check₄ next₄ =>
                      change (next₃ 0 false).toRelaxed.Solves _ at solves₄
                      rw [tree₄] at solves₄
                      have solves₅ := solves₄ (0 : Fin 11) false
                      have large := fiveZeroFalseLarge
                        guess₀ guess₁ guess₂ guess₃ guess₄
                        (check₀ 0) (check₁ 0) (check₂ 0) (check₃ 0) (check₄ 0)
                      apply no_three_round_continuation_of_large
                        ((next₄ 0 false).toRelaxed)
                        (FiveZeroFalseFinset guess₀ guess₁ guess₂ guess₃ guess₄
                          (check₀ 0) (check₁ 0) (check₂ 0) (check₃ 0) (check₄ 0))
                        large
                      simpa [FiveZeroFalseFinset, zeroFalseStep,
                        TenElevenRelaxedStrategy.answerBranch,
                        TenElevenRelaxedStrategy.blackBranch,
                        tree₁, tree₂, tree₃, tree₄]
                        using solves₅

/--
A second conditional adversary reduction for the ninth round.  Four consecutive
zero/false answers leave four rounds.  The sole hypothesis is the concrete
four-query intersection bound above the kernel-checked relaxed capacity 92,206.
-/
theorem tenElevenLowerBoundNine_of_fourZeroFalse_large
    (fourZeroFalseLarge :
      ∀ (guess₀ guess₁ guess₂ guess₃ : TenElevenSecret)
        (edge₀ edge₁ edge₂ edge₃ : Fin 10 × Fin 11),
        92206 < (FourZeroFalseFinset guess₀ guess₁ guess₂ guess₃
          edge₀ edge₁ edge₂ edge₃).card)
    (tree : TenElevenStrategy 8) (solves : tree.Solves Finset.univ) : False := by
  cases tree with
  | node guess₀ check₀ next₀ =>
      have solves₁ := solves (0 : Fin 11) false
      cases tree₁ : next₀ 0 false with
      | node guess₁ check₁ next₁ =>
          change (next₀ 0 false).toRelaxed.Solves _ at solves₁
          rw [tree₁] at solves₁
          have solves₂ := solves₁ (0 : Fin 11) false
          cases tree₂ : next₁ 0 false with
          | node guess₂ check₂ next₂ =>
              change (next₁ 0 false).toRelaxed.Solves _ at solves₂
              rw [tree₂] at solves₂
              have solves₃ := solves₂ (0 : Fin 11) false
              cases tree₃ : next₂ 0 false with
              | node guess₃ check₃ next₃ =>
                  change (next₂ 0 false).toRelaxed.Solves _ at solves₃
                  rw [tree₃] at solves₃
                  have solves₄ := solves₃ (0 : Fin 11) false
                  have large := fourZeroFalseLarge guess₀ guess₁ guess₂ guess₃
                    (check₀ 0) (check₁ 0) (check₂ 0) (check₃ 0)
                  apply no_four_round_continuation_of_large
                    ((next₃ 0 false).toRelaxed)
                    (FourZeroFalseFinset guess₀ guess₁ guess₂ guess₃
                      (check₀ 0) (check₁ 0) (check₂ 0) (check₃ 0))
                    large
                  simpa [FourZeroFalseFinset, zeroFalseStep,
                    TenElevenRelaxedStrategy.answerBranch,
                    TenElevenRelaxedStrategy.blackBranch,
                    tree₁, tree₂, tree₃]
                    using solves₄

/--
The numerical value of the published classical AB-Mastermind construction at
ten fields and eleven colors: `(10 - 2) * ⌈log₂ 10⌉ + 11 + 1 = 44`.
-/
def tenElevenPublishedRoundBound : Nat := (10 - 2) * 4 + 11 + 1

@[simp] theorem tenElevenPublishedRoundBound_eq :
    tenElevenPublishedRoundBound = 44 := by
  norm_num [tenElevenPublishedRoundBound]

/-- The externally cited classical strategy implies the upper bound `T⁺ ≤ 44`. -/
theorem tenElevenUpperBoundFortyFour_of_publishedStrategy {TPlus : Nat}
    (publishedClassicalStrategy : TPlus ≤ tenElevenPublishedRoundBound) :
    TPlus ≤ 44 := by
  simpa using publishedClassicalStrategy

/--
The requested upper-bound lemma. The extra-check game can ignore its extra
answer bit and run the cited classical strategy, whose 44-round bound is
stronger than 45.
-/
theorem tenElevenUpperBoundFortyFive_of_publishedStrategy {TPlus : Nat}
    (publishedClassicalStrategy : TPlus ≤ tenElevenPublishedRoundBound) :
    TPlus ≤ 45 := by
  have stronger :=
    tenElevenUpperBoundFortyFour_of_publishedStrategy publishedClassicalStrategy
  omega

/-! ## Arithmetic of proposed hybrid allocations -/

/--
Ten cyclic setup rounds, four padded `findNext` calls of four rounds each, and
one finishing round. The proof notes justify why the pipelined extra checks
reduce the open positions from nine to at most three during the four calls.
-/
def tenElevenHybridRoundBound : Nat := 10 + 3 * 4 + 4 + 1

@[simp] theorem tenElevenHybridRoundBound_eq :
    tenElevenHybridRoundBound = 27 := by
  norm_num [tenElevenHybridRoundBound]

/-! ## Three-call hybrid allocation -/

/--
Ten cyclic setup rounds, three padded `findNext` calls, and the three-round
five-position endgame from the proof notes.
-/
def tenElevenThreeCallRoundBound : Nat := 10 + 3 * 4 + 3

@[simp] theorem tenElevenThreeCallRoundBound_eq :
    tenElevenThreeCallRoundBound = 25 := by
  norm_num [tenElevenThreeCallRoundBound]

/-! ## Shrinking-search hybrid allocation -/

/--
Ten setup rounds, three `findNext` calls on nine, eight, and seven open
positions, and the three-round five-position endgame.
-/
def tenElevenShrinkingSearchRoundBound : Nat := 10 + 4 + 3 + 3 + 3

@[simp] theorem tenElevenShrinkingSearchRoundBound_eq :
    tenElevenShrinkingSearchRoundBound = 23 := by
  norm_num [tenElevenShrinkingSearchRoundBound]

/-! ## Two-search cylindrical-X-ray allocation -/

/--
Ten cyclic setup rounds, two `findNext` calls on nine and eight open
positions, and the two-round six-position cylindrical-X-ray endgame.
-/
def tenElevenCylindricalSearchRoundBound : Nat := 10 + 4 + 3 + 2

@[simp] theorem tenElevenCylindricalSearchRoundBound_eq :
    tenElevenCylindricalSearchRoundBound = 19 := by
  norm_num [tenElevenCylindricalSearchRoundBound]

/-! ## Equality-accelerated cyclic search -/

/--
Ten setup rounds, three two-round equality-accelerated `findNext` calls, and
the two-round six-position cylindrical-X-ray endgame.
-/
def tenElevenAcceleratedSearchRoundBound : Nat := 10 + 3 * 2 + 2

@[simp] theorem tenElevenAcceleratedSearchRoundBound_eq :
    tenElevenAcceleratedSearchRoundBound = 18 := by
  norm_num [tenElevenAcceleratedSearchRoundBound]

/-! ## Seven-position cylindrical-X-ray endgame -/

/--
Ten setup rounds, two two-round equality-accelerated `findNext` calls, and the
two-round seven-position cylindrical-X-ray endgame.
-/
def tenElevenSevenRookRoundBound : Nat := 10 + 2 * 2 + 2

@[simp] theorem tenElevenSevenRookRoundBound_eq :
    tenElevenSevenRookRoundBound = 16 := by
  norm_num [tenElevenSevenRookRoundBound]

/-! ## Eight-position cylindrical-X-ray endgame -/

/--
Ten setup rounds, one two-round equality-accelerated `findNext` call, and the
three-round eight-position cylindrical-X-ray endgame.
-/
def tenElevenEightRookRoundBound : Nat := 10 + 2 + 3

@[simp] theorem tenElevenEightRookRoundBound_eq :
    tenElevenEightRookRoundBound = 15 := by
  norm_num [tenElevenEightRookRoundBound]

/-! ## Nine-position cylindrical-X-ray endgame -/

/-- Ten cyclic setup rounds and the four-round nine-rook X-ray endgame. -/
def tenElevenNineRookRoundBound : Nat := 10 + 4

@[simp] theorem tenElevenNineRookRoundBound_eq :
    tenElevenNineRookRoundBound = 14 := by
  norm_num [tenElevenNineRookRoundBound]

end BlackPegExtraCheck
