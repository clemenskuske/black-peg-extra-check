/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.FirstAnswerFourFiber

/-!
# The canonical zero-match first-answer fiber

This file gives an unconditional fallback for the canonical first black answer
zero. Equality checks fix five coordinates; color/field symmetry then
transports the remaining five-coordinate uncertainty to the checked
five-block certificate.
-/

namespace BlackPegExtraCheck

noncomputable def anchorToCanonicalColors
    (anchor : TenElevenSecret) : Equiv.Perm (Fin 11) :=
  Classical.choose <| Equiv.Perm.exists_extending_pair
    (fun position : Fin 10 => anchor position)
    (fun position : Fin 10 => position.castSucc)
    anchor.injective (Fin.castSucc_injective 10)

theorem anchorToCanonicalColors_apply
    (anchor : TenElevenSecret) (position : Fin 10) :
    anchorToCanonicalColors anchor (anchor position) =
      position.castSucc := by
  exact (Classical.choose_spec <| Equiv.Perm.exists_extending_pair
    (fun position : Fin 10 => anchor position)
    (fun position : Fin 10 => position.castSucc)
    anchor.injective (Fin.castSucc_injective 10)) position

/-- Five commonly fixed coordinates reduce to the checked five-block state. -/
theorem sep_five_of_common_fixed
    (candidates : Finset TenElevenSecret)
    (fixed : Finset (Fin 10))
    (anchor : TenElevenSecret)
    (fixedCard : 5 ≤ fixed.card)
    (commonFixed : ∀ secret ∈ candidates, ∀ position ∈ fixed,
      secret position = anchor position) :
    Sep 5 candidates := by
  classical
  let colors := anchorToCanonicalColors anchor
  let support : Finset (Fin 10) := fixedᶜ
  have supportCard : support.card ≤ 5 := by
    have complementCard := Finset.card_compl fixed
    simp only [Fintype.card_fin] at complementCard
    simp [support]
    omega
  have mappedSep : Sep 5
      (TenElevenSymmetry.mapCandidates (Equiv.refl _) colors candidates) := by
    apply sep_five_of_support _ support supportCard
    intro mappedSecret mappedMem position positionOutside
    rcases Finset.mem_map.1 mappedMem with
      ⟨secret, secretMem, rfl⟩
    change TenElevenSymmetry.mapSecret (Equiv.refl (Fin 10)) colors
      secret position = position.castSucc
    rw [TenElevenSymmetry.mapSecret_apply]
    simp only [Equiv.refl_symm, Equiv.refl_apply]
    have positionFixed : position ∈ fixed := by
      simpa [support] using positionOutside
    rw [commonFixed secret secretMem position positionFixed]
    exact anchorToCanonicalColors_apply anchor position
  exact TenElevenSymmetry.Sep.unmap
    (Equiv.refl (Fin 10)).symm colors.symm mappedSep

/--
Repeated equality checks identify one coordinate from a bounded color set and
then invoke a uniform continuation for each possible fixed color.
-/
theorem sep_of_bounded_color_set_then
    (remaining baseDepth : Nat)
    (candidates : Finset TenElevenSecret)
    (guess : TenElevenSecret) (black : Fin 11)
    (position : Fin 10) (colors : Finset (Fin 11))
    (colorsCard : colors.card ≤ remaining + 1)
    (commonBlack : ∀ secret ∈ candidates,
      tenElevenBlackAnswer guess secret = black)
    (allowedColor : ∀ secret ∈ candidates, secret position ∈ colors)
    (finish : ∀ color ∈ colors,
      Sep baseDepth (candidates.filter fun secret =>
        secret position = color)) :
    Sep (remaining + baseDepth) candidates := by
  classical
  induction remaining generalizing candidates colors with
  | zero =>
      by_cases candidatesEmpty : candidates = ∅
      · rw [candidatesEmpty]
        simpa using Sep.empty baseDepth
      · obtain ⟨anchor, anchorMem⟩ :=
          Finset.nonempty_iff_ne_empty.mpr candidatesEmpty
        have anchorColorMem := allowedColor anchor anchorMem
        apply Sep.mono (larger :=
          candidates.filter fun secret => secret position = anchor position)
        · intro secret secretMem
          rw [Finset.mem_filter]
          refine ⟨secretMem, ?_⟩
          exact Finset.card_le_one.mp colorsCard
            (secret position) (allowedColor secret secretMem)
            (anchor position) anchorColorMem
        · simpa using finish (anchor position) anchorColorMem
  | succ remaining ih =>
      by_cases candidatesEmpty : candidates = ∅
      · rw [candidatesEmpty]
        exact Sep.empty (Nat.succ remaining + baseDepth)
      · obtain ⟨anchor, anchorMem⟩ :=
          Finset.nonempty_iff_ne_empty.mpr candidatesEmpty
        let testColor := anchor position
        have testColorMem : testColor ∈ colors :=
          allowedColor anchor anchorMem
        rw [show Nat.succ remaining + baseDepth =
          (remaining + baseDepth) + 1 by omega, sep_succ_iff]
        refine ⟨guess, ?_⟩
        intro answer
        refine ⟨(position, testColor), ?_, ?_⟩
        · by_cases answerExpected : answer = black
          · subst answer
            have branchSubset :
                checkedBranch candidates guess black
                    (position, testColor) true ⊆
                  candidates.filter fun secret =>
                    secret position = testColor := by
              intro secret secretMem
              have properties :=
                (mem_checkedBranch _ _ _ _ _ _).1 secretMem
              rw [Finset.mem_filter]
              refine ⟨properties.1, ?_⟩
              simpa using properties.2.2
            have separates :=
              Sep.mono branchSubset (finish testColor testColorMem)
            simpa [Nat.add_comm] using separates.pad_add remaining
          · have branchEmpty :
                checkedBranch candidates guess answer
                  (position, testColor) true = ∅ := by
              apply Finset.eq_empty_of_forall_notMem
              intro secret secretMem
              have properties :=
                (mem_checkedBranch _ _ _ _ _ _).1 secretMem
              exact answerExpected
                (properties.2.1.symm.trans
                  (commonBlack secret properties.1))
            rw [branchEmpty]
            exact Sep.empty (remaining + baseDepth)
        · by_cases answerExpected : answer = black
          · subst answer
            apply ih
                (checkedBranch candidates guess black
                  (position, testColor) false)
                (colors.erase testColor)
            · have eraseCard :=
                Finset.card_erase_add_one testColorMem
              omega
            · intro secret secretMem
              exact commonBlack secret
                ((mem_checkedBranch _ _ _ _ _ _).1 secretMem).1
            · intro secret secretMem
              have properties :=
                (mem_checkedBranch _ _ _ _ _ _).1 secretMem
              have notTest : secret position ≠ testColor := by
                simpa using properties.2.2
              exact Finset.mem_erase.mpr
                ⟨notTest, allowedColor secret properties.1⟩
            · intro color colorMem
              have colorOriginal : color ∈ colors :=
                (Finset.mem_erase.1 colorMem).2
              apply Sep.mono (larger :=
                candidates.filter fun secret =>
                  secret position = color)
              · intro secret secretMem
                rw [Finset.mem_filter] at secretMem ⊢
                exact ⟨
                  ((mem_checkedBranch _ _ _ _ _ _).1 secretMem.1).1,
                  secretMem.2⟩
              · exact finish color colorOriginal
          · have branchEmpty :
                checkedBranch candidates guess answer
                  (position, testColor) false = ∅ := by
              apply Finset.eq_empty_of_forall_notMem
              intro secret secretMem
              have properties :=
                (mem_checkedBranch _ _ _ _ _ _).1 secretMem
              exact answerExpected
                (properties.2.1.symm.trans
                  (commonBlack secret properties.1))
            rw [branchEmpty]
            exact Sep.empty (remaining + baseDepth)

/-- Residual rounds when an indicated number of coordinates remain to fix. -/
def zeroFiberRounds : Nat → Nat
  | 0 => 5
  | remaining + 1 => (remaining + 5) + zeroFiberRounds remaining

@[simp] theorem zeroFiberRounds_zero : zeroFiberRounds 0 = 5 := rfl

@[simp] theorem zeroFiberRounds_succ (remaining : Nat) :
    zeroFiberRounds (remaining + 1) =
      (remaining + 5) + zeroFiberRounds remaining := rfl

@[simp] theorem zeroFiberRounds_four : zeroFiberRounds 4 = 31 := by
  norm_num [zeroFiberRounds]

noncomputable def fixedColors
    (anchor : TenElevenSecret) (fixed : Finset (Fin 10)) :
    Finset (Fin 11) :=
  fixed.image anchor

theorem fixedColors_card
    (anchor : TenElevenSecret) (fixed : Finset (Fin 10)) :
    (fixedColors anchor fixed).card = fixed.card := by
  rw [fixedColors, Finset.card_image_of_injective _ anchor.injective]

theorem exists_position_outside_fixed_avoiding_colors
    (anchor : TenElevenSecret) (fixed : Finset (Fin 10))
    (fixedSmall : fixed.card < 5) :
    ∃ position : Fin 10,
      position ∉ fixed ∧ position.castSucc ∉ fixedColors anchor fixed := by
  classical
  by_contra noPosition
  push Not at noPosition
  have subset :
      fixedᶜ.map Fin.castSuccEmb ⊆ fixedColors anchor fixed := by
    intro color colorMem
    rcases Finset.mem_map.1 colorMem with
      ⟨position, positionMem, rfl⟩
    have positionOutside : position ∉ fixed := by simpa using positionMem
    exact noPosition position positionOutside
  have cards := Finset.card_le_card subset
  rw [Finset.card_map, fixedColors_card] at cards
  have complementCard := Finset.card_compl fixed
  simp only [Fintype.card_fin] at complementCard
  omega

noncomputable def zeroFiberAllowedColors
    (anchor : TenElevenSecret) (fixed : Finset (Fin 10))
    (position : Fin 10) : Finset (Fin 11) :=
  Finset.univ \ insert position.castSucc (fixedColors anchor fixed)

theorem zeroFiberAllowedColors_card
    (anchor : TenElevenSecret) (fixed : Finset (Fin 10))
    (position : Fin 10)
    (canonicalFresh : position.castSucc ∉ fixedColors anchor fixed) :
    (zeroFiberAllowedColors anchor fixed position).card =
      10 - fixed.card := by
  classical
  rw [zeroFiberAllowedColors,
    Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  rw [Finset.card_insert_of_notMem canonicalFresh, fixedColors_card]
  simp

theorem color_mem_zeroFiberAllowedColors
    (candidates : Finset TenElevenSecret)
    (anchor secret : TenElevenSecret)
    (anchorMem : anchor ∈ candidates) (secretMem : secret ∈ candidates)
    (fixed : Finset (Fin 10)) (position : Fin 10)
    (positionOutside : position ∉ fixed)
    (commonZero : ∀ candidate ∈ candidates,
      tenElevenBlackAnswer canonicalFirstGuess candidate = (0 : Fin 11))
    (fixedAgreement : ∀ first ∈ candidates, ∀ second ∈ candidates,
      ∀ fixedPosition ∈ fixed,
        first fixedPosition = second fixedPosition) :
    secret position ∈ zeroFiberAllowedColors anchor fixed position := by
  classical
  rw [zeroFiberAllowedColors, Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [Finset.mem_insert]
  push Not
  constructor
  · intro canonical
    have matched :
        position ∈ MatchSet canonicalFirstGuess secret :=
      (mem_MatchSet_iff canonicalFirstGuess secret position).2 canonical
    have zeroAnswer := commonZero secret secretMem
    have zeroCard := congrArg Fin.val zeroAnswer
    change (MatchSet canonicalFirstGuess secret).card = 0 at zeroCard
    have emptyMatches := Finset.card_eq_zero.mp zeroCard
    rw [emptyMatches] at matched
    simp at matched
  · intro fixedColorMem
    rw [fixedColors] at fixedColorMem
    rcases Finset.mem_image.1 fixedColorMem with
      ⟨fixedPosition, fixedPositionMem, colorEqual⟩
    have fixedEqual :=
      fixedAgreement secret secretMem anchor anchorMem
        fixedPosition fixedPositionMem
    have collision : secret position = secret fixedPosition := by
      rw [fixedEqual]
      exact colorEqual.symm
    exact positionOutside
      (secret.injective collision ▸ fixedPositionMem)

set_option maxHeartbeats 1200000 in
-- Recursive separator composition exceeds the default elaboration budget.
/--
If a zero-match candidate set already agrees on 5 minus remaining
coordinates, equality checks and the five-block certificate close it.
-/
theorem zeroFiber_sep_of_fixed
    (remaining : Nat)
    (candidates : Finset TenElevenSecret)
    (fixed : Finset (Fin 10))
    (fixedCount : fixed.card + remaining = 5)
    (commonZero : ∀ secret ∈ candidates,
      tenElevenBlackAnswer canonicalFirstGuess secret = (0 : Fin 11))
    (fixedAgreement : ∀ first ∈ candidates, ∀ second ∈ candidates,
      ∀ position ∈ fixed, first position = second position) :
    Sep (zeroFiberRounds remaining) candidates := by
  classical
  induction remaining generalizing candidates fixed with
  | zero =>
      by_cases candidatesEmpty : candidates = ∅
      · rw [candidatesEmpty]
        exact Sep.empty 5
      · obtain ⟨anchor, anchorMem⟩ :=
          Finset.nonempty_iff_ne_empty.mpr candidatesEmpty
        apply sep_five_of_common_fixed candidates fixed anchor
        · omega
        · intro secret secretMem position positionMem
          exact fixedAgreement secret secretMem anchor anchorMem
            position positionMem
  | succ remaining ih =>
      by_cases candidatesEmpty : candidates = ∅
      · rw [candidatesEmpty]
        exact Sep.empty (zeroFiberRounds (Nat.succ remaining))
      · obtain ⟨anchor, anchorMem⟩ :=
          Finset.nonempty_iff_ne_empty.mpr candidatesEmpty
        have fixedSmall : fixed.card < 5 := by omega
        obtain ⟨position, positionOutside, canonicalFresh⟩ :=
          exists_position_outside_fixed_avoiding_colors
            anchor fixed fixedSmall
        let colors := zeroFiberAllowedColors anchor fixed position
        have colorsCard : colors.card ≤ (remaining + 5) + 1 := by
          have exactCard :=
            zeroFiberAllowedColors_card anchor fixed position canonicalFresh
          simp [colors, exactCard]
          omega
        rw [zeroFiberRounds_succ]
        apply sep_of_bounded_color_set_then
            (remaining + 5) (zeroFiberRounds remaining)
            candidates canonicalFirstGuess (0 : Fin 11)
            position colors colorsCard commonZero
        · intro secret secretMem
          exact color_mem_zeroFiberAllowedColors
            candidates anchor secret anchorMem secretMem fixed position
            positionOutside commonZero fixedAgreement
        · intro color colorMem
          let branch := candidates.filter fun secret =>
            secret position = color
          change Sep (zeroFiberRounds remaining) branch
          apply ih branch (insert position fixed)
          · rw [Finset.card_insert_of_notMem positionOutside]
            omega
          · intro secret secretMem
            exact commonZero secret (Finset.mem_filter.1 secretMem).1
          · intro first firstMem second secondMem fixedPosition fixedPositionMem
            have firstProperties := Finset.mem_filter.1 firstMem
            have secondProperties := Finset.mem_filter.1 secondMem
            simp only [Finset.mem_insert] at fixedPositionMem
            rcases fixedPositionMem with fixedPositionEq | oldFixed
            · subst fixedPosition
              exact firstProperties.2.trans secondProperties.2.symm
            · exact fixedAgreement first firstProperties.1
                second secondProperties.1 fixedPosition oldFixed

noncomputable def zeroFirstFalseColors : Finset (Fin 11) :=
  (Finset.univ.erase (0 : Fin 11)).erase (1 : Fin 11)

@[simp] theorem zeroFirstFalseColors_card :
    zeroFirstFalseColors.card = 9 := by
  decide

theorem zeroFirstFalseColors_allowed
    (secret : TenElevenSecret)
    (secretMem : secret ∈
      checkedBranch (Finset.univ : Finset TenElevenSecret)
        canonicalFirstGuess (0 : Fin 11) (0, 1) false) :
    secret 0 ∈ zeroFirstFalseColors := by
  have properties :=
    (mem_checkedBranch _ _ _ _ _ _).1 secretMem
  have notOne : secret 0 ≠ 1 := by
    simpa using properties.2.2
  have notZero : secret 0 ≠ 0 := by
    intro equal
    have matched : (0 : Fin 10) ∈ MatchSet canonicalFirstGuess secret :=
      (mem_MatchSet_iff canonicalFirstGuess secret 0).2 equal
    have zeroCard := congrArg Fin.val properties.2.1
    change (MatchSet canonicalFirstGuess secret).card = 0 at zeroCard
    have emptyMatches := Finset.card_eq_zero.mp zeroCard
    rw [emptyMatches] at matched
    simp at matched
  simp [zeroFirstFalseColors, notZero, notOne]

set_option maxHeartbeats 1200000 in
-- Four recursive separator layers exceed the default elaboration budget.
set_option maxRecDepth 10000 in
-- The expanded separator proof term exceeds the default recursion depth.
theorem zeroFiberFirstTrue_sep_thirtyNine :
    Sep 39
      (checkedBranch (Finset.univ : Finset TenElevenSecret)
        canonicalFirstGuess (0 : Fin 11) (0, 1) true) := by
  let candidates :=
    checkedBranch (Finset.univ : Finset TenElevenSecret)
      canonicalFirstGuess (0 : Fin 11) (0, 1) true
  have core : Sep (zeroFiberRounds 4) candidates := by
    apply zeroFiber_sep_of_fixed 4 candidates {0}
    · simp
    · intro secret secretMem
      exact ((mem_checkedBranch _ _ _ _ _ _).1 secretMem).2.1
    · intro first firstMem second secondMem position positionMem
      have positionZero : position = 0 := by simpa using positionMem
      subst position
      have firstProperties :=
        (mem_checkedBranch _ _ _ _ _ _).1 firstMem
      have secondProperties :=
        (mem_checkedBranch _ _ _ _ _ _).1 secondMem
      have firstEqual : first 0 = 1 := by simpa using firstProperties.2.2
      have secondEqual : second 0 = 1 := by simpa using secondProperties.2.2
      exact firstEqual.trans secondEqual.symm
  rw [zeroFiberRounds_four] at core
  exact core.pad_add 8

set_option maxHeartbeats 1200000 in
-- Equality identification and four layers exceed the elaboration budget.
set_option maxRecDepth 10000 in
-- The expanded separator proof term exceeds the default recursion depth.
theorem zeroFiberFirstFalse_sep_thirtyNine :
    Sep 39
      (checkedBranch (Finset.univ : Finset TenElevenSecret)
        canonicalFirstGuess (0 : Fin 11) (0, 1) false) := by
  let candidates :=
    checkedBranch (Finset.univ : Finset TenElevenSecret)
      canonicalFirstGuess (0 : Fin 11) (0, 1) false
  change Sep 39 candidates
  have commonZero : ∀ secret ∈ candidates,
      tenElevenBlackAnswer canonicalFirstGuess secret = (0 : Fin 11) := by
    intro secret secretMem
    exact ((mem_checkedBranch _ _ _ _ _ _).1 secretMem).2.1
  have identifies : Sep (8 + zeroFiberRounds 4) candidates := by
    apply sep_of_bounded_color_set_then 8 (zeroFiberRounds 4)
      candidates canonicalFirstGuess (0 : Fin 11) 0
      zeroFirstFalseColors
    · simp
    · exact commonZero
    · intro secret secretMem
      exact zeroFirstFalseColors_allowed secret secretMem
    · intro color colorMem
      let branch := candidates.filter fun secret => secret 0 = color
      change Sep (zeroFiberRounds 4) branch
      apply zeroFiber_sep_of_fixed 4 branch {0}
      · simp
      · intro secret secretMem
        exact commonZero secret (Finset.mem_filter.1 secretMem).1
      · intro first firstMem second secondMem position positionMem
        have positionZero : position = 0 := by simpa using positionMem
        subst position
        have firstProperties := Finset.mem_filter.1 firstMem
        have secondProperties := Finset.mem_filter.1 secondMem
        exact firstProperties.2.trans secondProperties.2.symm
  rw [zeroFiberRounds_four] at identifies
  exact identifies

/--
The canonical first black-answer fiber zero is solved in at most forty total
rounds, including the canonical first query.
-/
theorem canonical_first_answer_zero_total_forty :
    ∃ edge : Fin 10 × Fin 11,
      Sep 39 (checkedBranch (Finset.univ : Finset TenElevenSecret)
        canonicalFirstGuess (0 : Fin 11) edge true) ∧
      Sep 39 (checkedBranch (Finset.univ : Finset TenElevenSecret)
        canonicalFirstGuess (0 : Fin 11) edge false) := by
  exact ⟨(0, 1), zeroFiberFirstTrue_sep_thirtyNine,
    zeroFiberFirstFalse_sep_thirtyNine⟩


theorem probe_answer_eq_one_of_zero_of_last
    (secret : TenElevenSecret) (position : Fin 10)
    (zeroAnswer :
      tenElevenBlackAnswer canonicalFirstGuess secret = (0 : Fin 11))
    (lastColor : secret position = Fin.last 10) :
    tenElevenBlackAnswer (probeGuess position) secret = (1 : Fin 11) := by
  apply Fin.ext
  have cards := canonical_card_add_one_of_last secret position lastColor
  have zeroCard := congrArg Fin.val zeroAnswer
  change (MatchSet canonicalFirstGuess secret).card = 0 at zeroCard
  change (MatchSet (probeGuess position) secret).card = 1
  omega

theorem probe_answer_eq_zero_of_zero_of_other
    (secret : TenElevenSecret) (position : Fin 10)
    (zeroAnswer :
      tenElevenBlackAnswer canonicalFirstGuess secret = (0 : Fin 11))
    (notCanonical : secret position ≠ position.castSucc)
    (notLast : secret position ≠ Fin.last 10) :
    tenElevenBlackAnswer (probeGuess position) secret = (0 : Fin 11) := by
  apply Fin.ext
  have cards :=
    probe_card_eq_of_other secret position notCanonical notLast
  have zeroCard := congrArg Fin.val zeroAnswer
  change (MatchSet canonicalFirstGuess secret).card = 0 at zeroCard
  change (MatchSet (probeGuess position) secret).card = 0
  omega

noncomputable def zeroProbeFalseColors : Finset (Fin 11) :=
  (((Finset.univ.erase (0 : Fin 11)).erase (1 : Fin 11)).erase
    (2 : Fin 11)).erase (Fin.last 10)

@[simp] theorem zeroProbeFalseColors_card :
    zeroProbeFalseColors.card = 7 := by
  decide

set_option maxHeartbeats 1200000 in
-- The first probe expands the recursive separator beyond the default budget.
set_option maxRecDepth 10000 in
-- The expanded proof term exceeds the default recursion depth.
/--
After the initial zero answer and false equality bit, one probe round tests
color ten through its black answer and color two through its equality bit.
-/
theorem zeroFiberFirstFalse_sep_thirtyEight :
    Sep 38
      (checkedBranch (Finset.univ : Finset TenElevenSecret)
        canonicalFirstGuess (0 : Fin 11) (0, 1) false) := by
  classical
  let candidates :=
    checkedBranch (Finset.univ : Finset TenElevenSecret)
      canonicalFirstGuess (0 : Fin 11) (0, 1) false
  have commonZero : ∀ secret ∈ candidates,
      tenElevenBlackAnswer canonicalFirstGuess secret = (0 : Fin 11) := by
    intro secret secretMem
    exact ((mem_checkedBranch _ _ _ _ _ _).1 secretMem).2.1
  have notCanonicalZero : ∀ secret ∈ candidates,
      secret 0 ≠ (0 : Fin 11) := by
    intro secret secretMem equal
    have matched : (0 : Fin 10) ∈ MatchSet canonicalFirstGuess secret :=
      (mem_MatchSet_iff canonicalFirstGuess secret 0).2 equal
    have zeroCard := congrArg Fin.val (commonZero secret secretMem)
    change (MatchSet canonicalFirstGuess secret).card = 0 at zeroCard
    rw [Finset.card_eq_zero.mp zeroCard] at matched
    simp at matched
  have notInitialTest : ∀ secret ∈ candidates,
      secret 0 ≠ (1 : Fin 11) := by
    intro secret secretMem
    have properties :=
      (mem_checkedBranch _ _ _ _ _ _).1 secretMem
    simpa using properties.2.2
  have fixedContinuation :
      ∀ (branch : Finset TenElevenSecret),
        (∀ secret ∈ branch,
          tenElevenBlackAnswer canonicalFirstGuess secret = (0 : Fin 11)) →
        (∀ first ∈ branch, ∀ second ∈ branch, first 0 = second 0) →
        Sep 37 branch := by
    intro branch branchZero branchFixed
    have core : Sep (zeroFiberRounds 4) branch := by
      apply zeroFiber_sep_of_fixed 4 branch {0}
      · simp
      · exact branchZero
      · intro first firstMem second secondMem position positionMem
        have positionZero : position = 0 := by simpa using positionMem
        subst position
        exact branchFixed first firstMem second secondMem
    rw [zeroFiberRounds_four] at core
    exact core.pad_add 6
  rw [show 38 = 37 + 1 by omega, sep_succ_iff]
  refine ⟨probeGuess 0, ?_⟩
  intro black
  refine ⟨(0, 2), ?_, ?_⟩
  · by_cases blackZero : black = (0 : Fin 11)
    · subst black
      apply fixedContinuation
      · intro secret secretMem
        exact commonZero secret
          ((mem_checkedBranch _ _ _ _ _ _).1 secretMem).1
      · intro first firstMem second secondMem
        have firstProperties :=
          (mem_checkedBranch _ _ _ _ _ _).1 firstMem
        have secondProperties :=
          (mem_checkedBranch _ _ _ _ _ _).1 secondMem
        have firstEqual : first 0 = 2 := by simpa using firstProperties.2.2
        have secondEqual : second 0 = 2 := by simpa using secondProperties.2.2
        exact firstEqual.trans secondEqual.symm
    · by_cases blackOne : black = (1 : Fin 11)
      · subst black
        have branchEmpty :
            checkedBranch candidates (probeGuess 0) 1 (0, 2) true = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro secret secretMem
          have properties :=
            (mem_checkedBranch _ _ _ _ _ _).1 secretMem
          have candidateMem := properties.1
          have zero := commonZero secret candidateMem
          have notLast : secret 0 ≠ Fin.last 10 := by
            intro last
            have equalTwo : secret 0 = 2 := by
              simpa using properties.2.2
            have values := congrArg Fin.val (equalTwo.symm.trans last)
            norm_num at values
          have answerZero := probe_answer_eq_zero_of_zero_of_other
            secret 0 zero (notCanonicalZero secret candidateMem) notLast
          have impossible := properties.2.1.symm.trans answerZero
          have values := congrArg Fin.val impossible
          norm_num at values
        rw [branchEmpty]
        exact Sep.empty 37
      · have branchEmpty :
            checkedBranch candidates (probeGuess 0) black (0, 2) true = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro secret secretMem
          have properties :=
            (mem_checkedBranch _ _ _ _ _ _).1 secretMem
          have candidateMem := properties.1
          have zero := commonZero secret candidateMem
          by_cases last : secret 0 = Fin.last 10
          · have answerOne :=
              probe_answer_eq_one_of_zero_of_last secret 0 zero last
            exact blackOne (properties.2.1.symm.trans answerOne)
          · have answerZero := probe_answer_eq_zero_of_zero_of_other
              secret 0 zero (notCanonicalZero secret candidateMem) last
            exact blackZero (properties.2.1.symm.trans answerZero)
        rw [branchEmpty]
        exact Sep.empty 37
  · by_cases blackOne : black = (1 : Fin 11)
    · subst black
      apply fixedContinuation
      · intro secret secretMem
        exact commonZero secret
          ((mem_checkedBranch _ _ _ _ _ _).1 secretMem).1
      · intro first firstMem second secondMem
        have firstProperties :=
          (mem_checkedBranch _ _ _ _ _ _).1 firstMem
        have secondProperties :=
          (mem_checkedBranch _ _ _ _ _ _).1 secondMem
        have firstLast : first 0 = Fin.last 10 := by
          by_contra notLast
          have answerZero := probe_answer_eq_zero_of_zero_of_other
            first 0
            (commonZero first firstProperties.1)
            (notCanonicalZero first firstProperties.1) notLast
          have impossible := firstProperties.2.1.symm.trans answerZero
          have values := congrArg Fin.val impossible
          norm_num at values
        have secondLast : second 0 = Fin.last 10 := by
          by_contra notLast
          have answerZero := probe_answer_eq_zero_of_zero_of_other
            second 0
            (commonZero second secondProperties.1)
            (notCanonicalZero second secondProperties.1) notLast
          have impossible := secondProperties.2.1.symm.trans answerZero
          have values := congrArg Fin.val impossible
          norm_num at values
        exact firstLast.trans secondLast.symm
    · by_cases blackZero : black = (0 : Fin 11)
      · subst black
        let branch :=
          checkedBranch candidates (probeGuess 0) 0 (0, 2) false
        have branchZero : ∀ secret ∈ branch,
            tenElevenBlackAnswer canonicalFirstGuess secret = (0 : Fin 11) := by
          intro secret secretMem
          exact commonZero secret
            ((mem_checkedBranch _ _ _ _ _ _).1 secretMem).1
        have allowed : ∀ secret ∈ branch,
            secret 0 ∈ zeroProbeFalseColors := by
          intro secret secretMem
          have properties :=
            (mem_checkedBranch _ _ _ _ _ _).1 secretMem
          have candidateMem := properties.1
          have notTwo : secret 0 ≠ (2 : Fin 11) := by
            simpa using properties.2.2
          have notLast : secret 0 ≠ Fin.last 10 := by
            intro last
            have answerOne := probe_answer_eq_one_of_zero_of_last
              secret 0 (commonZero secret candidateMem) last
            have impossible := properties.2.1.symm.trans answerOne
            have values := congrArg Fin.val impossible
            norm_num at values
          have notTen : secret 0 ≠ (10 : Fin 11) := by
            simpa using notLast
          simp [zeroProbeFalseColors,
            notCanonicalZero secret candidateMem,
            notInitialTest secret candidateMem, notTwo, notTen]
        change Sep 37 branch
        have identifies : Sep (6 + zeroFiberRounds 4) branch := by
          apply sep_of_bounded_color_set_then 6 (zeroFiberRounds 4)
            branch canonicalFirstGuess (0 : Fin 11) 0
            zeroProbeFalseColors
          · simp
          · exact branchZero
          · exact allowed
          · intro color colorMem
            let colorBranch := branch.filter fun secret => secret 0 = color
            change Sep (zeroFiberRounds 4) colorBranch
            apply zeroFiber_sep_of_fixed 4 colorBranch {0}
            · simp
            · intro secret secretMem
              exact branchZero secret (Finset.mem_filter.1 secretMem).1
            · intro first firstMem second secondMem position positionMem
              have positionZero : position = 0 := by simpa using positionMem
              subst position
              have firstProperties := Finset.mem_filter.1 firstMem
              have secondProperties := Finset.mem_filter.1 secondMem
              exact firstProperties.2.trans secondProperties.2.symm
        rw [zeroFiberRounds_four] at identifies
        exact identifies
      · have branchEmpty :
            checkedBranch candidates (probeGuess 0) black (0, 2) false = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro secret secretMem
          have properties :=
            (mem_checkedBranch _ _ _ _ _ _).1 secretMem
          have candidateMem := properties.1
          have zero := commonZero secret candidateMem
          by_cases last : secret 0 = Fin.last 10
          · have answerOne :=
              probe_answer_eq_one_of_zero_of_last secret 0 zero last
            exact blackOne (properties.2.1.symm.trans answerOne)
          · have answerZero := probe_answer_eq_zero_of_zero_of_other
              secret 0 zero (notCanonicalZero secret candidateMem) last
            exact blackZero (properties.2.1.symm.trans answerZero)
        rw [branchEmpty]
        exact Sep.empty 37

set_option maxHeartbeats 1200000 in
-- Expanding the recursive separator exceeds the default elaboration budget.
set_option maxRecDepth 10000 in
-- The concrete padded proof term exceeds the default recursion depth.
theorem zeroFiberFirstTrue_sep_thirtyEight :
    Sep 38
      (checkedBranch (Finset.univ : Finset TenElevenSecret)
        canonicalFirstGuess (0 : Fin 11) (0, 1) true) := by
  let candidates :=
    checkedBranch (Finset.univ : Finset TenElevenSecret)
      canonicalFirstGuess (0 : Fin 11) (0, 1) true
  have core : Sep (zeroFiberRounds 4) candidates := by
    apply zeroFiber_sep_of_fixed 4 candidates {0}
    · simp
    · intro secret secretMem
      exact ((mem_checkedBranch _ _ _ _ _ _).1 secretMem).2.1
    · intro first firstMem second secondMem position positionMem
      have positionZero : position = 0 := by simpa using positionMem
      subst position
      have firstProperties :=
        (mem_checkedBranch _ _ _ _ _ _).1 firstMem
      have secondProperties :=
        (mem_checkedBranch _ _ _ _ _ _).1 secondMem
      have firstEqual : first 0 = 1 := by simpa using firstProperties.2.2
      have secondEqual : second 0 = 1 := by simpa using secondProperties.2.2
      exact firstEqual.trans secondEqual.symm
  rw [zeroFiberRounds_four] at core
  exact core.pad_add 7

set_option maxHeartbeats 1200000 in
-- Combining the two first-check branches exceeds the default elaboration budget.
set_option maxRecDepth 10000 in
-- The final proof term exceeds the default recursion depth.
/--
The canonical first black-answer fiber zero is solved in at most thirty-nine
total rounds, including the canonical first query.
-/
theorem canonical_first_answer_zero_total_thirtyNine :
    ∃ edge : Fin 10 × Fin 11,
      Sep 38 (checkedBranch (Finset.univ : Finset TenElevenSecret)
        canonicalFirstGuess (0 : Fin 11) edge true) ∧
      Sep 38 (checkedBranch (Finset.univ : Finset TenElevenSecret)
        canonicalFirstGuess (0 : Fin 11) edge false) := by
  refine ⟨(0, 1), ?_, zeroFiberFirstFalse_sep_thirtyEight⟩
  exact zeroFiberFirstTrue_sep_thirtyEight


end BlackPegExtraCheck
