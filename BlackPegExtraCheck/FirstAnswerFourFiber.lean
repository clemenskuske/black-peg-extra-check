/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.FirstAnswerHighFibers

/-!
# The canonical four-match first-answer fiber

This file reduces the canonical first black answer four to the verified
five-block residual certificate.
-/

namespace BlackPegExtraCheck

theorem Sep.pad_add {depth : Nat} {candidates : Finset TenElevenSecret}
    (separates : Sep depth candidates) (extra : Nat) :
    Sep (depth + extra) candidates := by
  induction extra with
  | zero => simpa
  | succ extra ih =>
      rw [Nat.add_succ]
      exact Sep.pad ih

theorem sep_five_of_common_matchSet_and_fixed
    (candidates : Finset TenElevenSecret)
    (matchPositions : Finset (Fin 10))
    (fixedPosition : Fin 10) (fixedColor : Fin 11)
    (matchesCard : 4 ≤ matchPositions.card)
    (fixedNotMatch : fixedPosition ∉ matchPositions)
    (commonMatches : ∀ secret ∈ candidates,
      MatchSet canonicalFirstGuess secret = matchPositions)
    (commonFixed : ∀ secret ∈ candidates,
      secret fixedPosition = fixedColor) :
    Sep 5 candidates := by
  classical
  let colors : Equiv.Perm (Fin 11) :=
    Equiv.swap fixedColor fixedPosition.castSucc
  let support : Finset (Fin 10) := matchPositionsᶜ.erase fixedPosition
  have fixedInComplement : fixedPosition ∈ matchPositionsᶜ := by
    simp [fixedNotMatch]
  have supportCard : support.card ≤ 5 := by
    have complementCard := Finset.card_compl matchPositions
    have eraseCard := Finset.card_erase_add_one fixedInComplement
    simp only [Fintype.card_fin] at complementCard
    simp [support] at eraseCard ⊢
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
    by_cases positionFixed : position = fixedPosition
    · subst position
      rw [commonFixed secret secretMem]
      exact Equiv.swap_apply_left _ _
    · have positionMatched : position ∈ matchPositions := by
        by_contra positionNotMatched
        have positionComplement : position ∈ matchPositionsᶜ := by
          simp [positionNotMatched]
        exact positionOutside
          (Finset.mem_erase.mpr ⟨positionFixed, positionComplement⟩)
      have secretMatched :
          secret position = position.castSucc := by
        apply (mem_MatchSet_iff canonicalFirstGuess secret position).1
        rw [commonMatches secret secretMem]
        exact positionMatched
      rw [secretMatched]
      apply Equiv.swap_apply_of_ne_of_ne
      · intro colorEqual
        have collision :
            secret position = secret fixedPosition := by
          rw [secretMatched, commonFixed secret secretMem]
          exact colorEqual
        exact positionFixed (secret.injective collision)
      · intro positionEqual
        exact positionFixed (Fin.castSucc_injective 10 positionEqual)
  exact TenElevenSymmetry.Sep.unmap
    (Equiv.refl (Fin 10)).symm colors.symm mappedSep


theorem sep_of_bounded_color_set
    (remaining : Nat)
    (candidates : Finset TenElevenSecret)
    (firstBlack : Fin 11)
    (matchPositions : Finset (Fin 10))
    (position : Fin 10)
    (colors : Finset (Fin 11))
    (matchesCard : 4 ≤ matchPositions.card)
    (positionNotMatch : position ∉ matchPositions)
    (colorsCard : colors.card ≤ remaining + 1)
    (commonMatches : ∀ secret ∈ candidates,
      MatchSet canonicalFirstGuess secret = matchPositions)
    (commonBlack : ∀ secret ∈ candidates,
      tenElevenBlackAnswer canonicalFirstGuess secret = firstBlack)
    (allowedColor : ∀ secret ∈ candidates, secret position ∈ colors) :
    Sep (remaining + 5) candidates := by
  classical
  induction remaining generalizing candidates colors with
  | zero =>
      by_cases candidatesEmpty : candidates = ∅
      · rw [candidatesEmpty]
        exact Sep.empty 5
      · obtain ⟨anchor, anchorMem⟩ :=
          Finset.nonempty_iff_ne_empty.mpr candidatesEmpty
        have commonPosition : ∀ secret ∈ candidates,
            secret position = anchor position := by
          intro secret secretMem
          exact Finset.card_le_one.mp colorsCard
            (secret position) (allowedColor secret secretMem)
            (anchor position) (allowedColor anchor anchorMem)
        exact sep_five_of_common_matchSet_and_fixed candidates
          matchPositions position (anchor position) matchesCard
          positionNotMatch commonMatches commonPosition
  | succ remaining ih =>
      by_cases candidatesEmpty : candidates = ∅
      · rw [candidatesEmpty]
        exact Sep.empty (Nat.succ remaining + 5)
      · obtain ⟨anchor, anchorMem⟩ :=
          Finset.nonempty_iff_ne_empty.mpr candidatesEmpty
        let testColor := anchor position
        have testColorMem : testColor ∈ colors :=
          allowedColor anchor anchorMem
        rw [show Nat.succ remaining + 5 = (remaining + 5) + 1 by omega,
          sep_succ_iff]
        refine ⟨canonicalFirstGuess, ?_⟩
        intro black
        refine ⟨(position, testColor), ?_, ?_⟩
        · by_cases blackExpected : black = firstBlack
          · subst black
            have yesFixed : ∀ secret ∈
                checkedBranch candidates canonicalFirstGuess firstBlack
                  (position, testColor) true,
                secret position = testColor := by
              intro secret secretMem
              have properties :=
                (mem_checkedBranch _ _ _ _ _ _).1 secretMem
              simpa using properties.2.2
            have yesSep : Sep 5
                (checkedBranch candidates canonicalFirstGuess firstBlack
                  (position, testColor) true) := by
              apply sep_five_of_common_matchSet_and_fixed _
                matchPositions position testColor matchesCard
                positionNotMatch
              · intro secret secretMem
                exact commonMatches secret
                  ((mem_checkedBranch _ _ _ _ _ _).1 secretMem).1
              · exact yesFixed
            simpa [Nat.add_comm] using yesSep.pad_add remaining
          · have branchEmpty :
                checkedBranch candidates canonicalFirstGuess black
                  (position, testColor) true = ∅ := by
              apply Finset.eq_empty_of_forall_notMem
              intro secret secretMem
              have properties :=
                (mem_checkedBranch _ _ _ _ _ _).1 secretMem
              exact blackExpected
                (properties.2.1.symm.trans
                  (commonBlack secret properties.1))
            rw [branchEmpty]
            exact Sep.empty (remaining + 5)
        · by_cases blackExpected : black = firstBlack
          · subst black
            apply ih
                (checkedBranch candidates canonicalFirstGuess firstBlack
                  (position, testColor) false)
                (colors.erase testColor)
            · have eraseCard :=
                Finset.card_erase_add_one testColorMem
              omega
            · intro secret secretMem
              exact commonMatches secret
                ((mem_checkedBranch _ _ _ _ _ _).1 secretMem).1
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
          · have branchEmpty :
                checkedBranch candidates canonicalFirstGuess black
                  (position, testColor) false = ∅ := by
              apply Finset.eq_empty_of_forall_notMem
              intro secret secretMem
              have properties :=
                (mem_checkedBranch _ _ _ _ _ _).1 secretMem
              exact blackExpected
                (properties.2.1.symm.trans
                  (commonBlack secret properties.1))
            rw [branchEmpty]
            exact Sep.empty (remaining + 5)



noncomputable def fourFiberSupportColors
    (matchPositions : Finset (Fin 10)) (position : Fin 10) :
    Finset (Fin 11) :=
  (matchPositionsᶜ.erase position).map Fin.castSuccEmb

theorem fourFiberSupportColors_card
    (matchPositions : Finset (Fin 10)) (position : Fin 10)
    (matchesCard : matchPositions.card = 4)
    (positionNotMatch : position ∉ matchPositions) :
    (fourFiberSupportColors matchPositions position).card = 5 := by
  have positionComplement : position ∈ matchPositionsᶜ := by
    simp [positionNotMatch]
  have complementCard := Finset.card_compl matchPositions
  have eraseCard := Finset.card_erase_add_one positionComplement
  simp only [Fintype.card_fin] at complementCard
  rw [fourFiberSupportColors, Finset.card_map]
  omega

theorem color_at_unmatched_mem_fourFiberSupportColors
    (secret : TenElevenSecret)
    (matchPositions : Finset (Fin 10)) (position : Fin 10)
    (commonMatches :
      MatchSet canonicalFirstGuess secret = matchPositions)
    (positionNotMatch : position ∉ matchPositions) :
    secret position ∈
      insert (Fin.last 10) (fourFiberSupportColors matchPositions position) := by
  classical
  by_cases lastColor : secret position = Fin.last 10
  · simp [lastColor]
  · apply Finset.mem_insert.mpr
    right
    have colorLtTen : (secret position).val < 10 := by
      by_contra colorNotLt
      apply lastColor
      apply Fin.ext
      simp only [Fin.last]
      omega
    let source : Fin 10 := ⟨(secret position).val, colorLtTen⟩
    have sourceColor : source.castSucc = secret position := by
      apply Fin.ext
      rfl
    have positionNeSource : position ≠ source := by
      intro positionSource
      apply positionNotMatch
      rw [← commonMatches]
      apply (mem_MatchSet_iff canonicalFirstGuess secret position).2
      simpa [positionSource] using sourceColor.symm
    have sourceNotMatch : source ∉ matchPositions := by
      intro sourceMatched
      have sourceFixed :
          secret source = source.castSucc := by
        apply (mem_MatchSet_iff canonicalFirstGuess secret source).1
        rw [commonMatches]
        exact sourceMatched
      have collision : secret position = secret source := by
        rw [sourceFixed]
        exact sourceColor.symm
      exact positionNeSource (secret.injective collision)
    rw [fourFiberSupportColors]
    apply Finset.mem_map.mpr
    refine ⟨source, ?_, sourceColor⟩
    exact Finset.mem_erase.mpr
      ⟨positionNeSource.symm, by simp [sourceNotMatch]⟩


theorem probe_answer_eq_five_of_matchSet_card_four_of_last
    (secret : TenElevenSecret) (position : Fin 10)
    (matchesCard :
      (MatchSet canonicalFirstGuess secret).card = 4)
    (lastColor : secret position = Fin.last 10) :
    tenElevenBlackAnswer (probeGuess position) secret = (5 : Fin 11) := by
  apply Fin.ext
  change (MatchSet (probeGuess position) secret).card = 5
  have cards := canonical_card_add_one_of_last secret position lastColor
  omega

theorem probe_answer_eq_four_of_matchSet_card_four_of_other
    (secret : TenElevenSecret) (position : Fin 10)
    (matchesCard :
      (MatchSet canonicalFirstGuess secret).card = 4)
    (notCanonical : secret position ≠ position.castSucc)
    (notLast : secret position ≠ Fin.last 10) :
    tenElevenBlackAnswer (probeGuess position) secret = (4 : Fin 11) := by
  apply Fin.ext
  change (MatchSet (probeGuess position) secret).card = 4
  have cards :=
    probe_card_eq_of_other secret position notCanonical notLast
  omega

set_option maxHeartbeats 1200000 in
-- The nine nested separator layers duplicate the color-identification branches.
theorem sep_nine_of_common_matchSet_card_four
    (candidates : Finset TenElevenSecret)
    (matchPositions : Finset (Fin 10))
    (matchesCard : matchPositions.card = 4)
    (commonMatches : ∀ secret ∈ candidates,
      MatchSet canonicalFirstGuess secret = matchPositions) :
    Sep 9 candidates := by
  classical
  by_cases candidatesEmpty : candidates = ∅
  · rw [candidatesEmpty]
    exact Sep.empty 9
  · have complementCard : matchPositionsᶜ.card = 6 := by
      have cardEquation := Finset.card_compl matchPositions
      simp only [Fintype.card_fin] at cardEquation
      omega
    obtain ⟨position, positionComplement⟩ :
        ∃ position, position ∈ matchPositionsᶜ := by
      have complementNonempty : matchPositionsᶜ.Nonempty := by
        apply Finset.card_pos.mp
        omega
      exact complementNonempty
    have positionNotMatch : position ∉ matchPositions := by
      simpa using positionComplement
    let supportColors := fourFiberSupportColors matchPositions position
    have supportColorsCard : supportColors.card = 5 := by
      exact fourFiberSupportColors_card matchPositions position
        matchesCard positionNotMatch
    obtain ⟨testColor, testColorMem⟩ : ∃ color, color ∈ supportColors := by
      have supportColorsNonempty : supportColors.Nonempty := by
        apply Finset.card_pos.mp
        omega
      exact supportColorsNonempty
    have commonCanonicalBlack : ∀ secret ∈ candidates,
        tenElevenBlackAnswer canonicalFirstGuess secret = (4 : Fin 11) := by
      intro secret secretMem
      apply Fin.ext
      change (MatchSet canonicalFirstGuess secret).card = 4
      rw [commonMatches secret secretMem, matchesCard]
    have notCanonical : ∀ secret ∈ candidates,
        secret position ≠ position.castSucc := by
      intro secret secretMem equal
      apply positionNotMatch
      rw [← commonMatches secret secretMem]
      exact (mem_MatchSet_iff canonicalFirstGuess secret position).2 equal
    rw [show 9 = 8 + 1 by omega, sep_succ_iff]
    refine ⟨probeGuess position, ?_⟩
    intro black
    refine ⟨(position, testColor), ?_, ?_⟩
    · by_cases blackFive : black = (5 : Fin 11)
      · subst black
        have branchEmpty :
            checkedBranch candidates (probeGuess position) 5
              (position, testColor) true = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro secret secretMem
          have properties :=
            (mem_checkedBranch _ _ _ _ _ _).1 secretMem
          have probeIfOther :=
            probe_answer_eq_four_of_matchSet_card_four_of_other
          by_cases secretLast : secret position = Fin.last 10
          · have testNotLast : testColor ≠ Fin.last 10 := by
              intro testLast
              have supportRange := testColorMem
              change testColor ∈
                (matchPositionsᶜ.erase position).map Fin.castSuccEmb
                at supportRange
              rw [testLast] at supportRange
              rcases Finset.mem_map.1 supportRange with
                ⟨source, _, sourceLast⟩
              exact Fin.castSucc_ne_last source sourceLast
            have decision : secret position = testColor := by
              simpa using properties.2.2
            exact testNotLast (decision.symm.trans secretLast)
          · have answerFour := probeIfOther secret position
                (by
                  rw [commonMatches secret properties.1]
                  exact matchesCard)
                (notCanonical secret properties.1) secretLast
            have impossible := properties.2.1.symm.trans answerFour
            have values := congrArg Fin.val impossible
            norm_num at values
        rw [branchEmpty]
        exact Sep.empty 8
      · by_cases blackFour : black = (4 : Fin 11)
        · subst black
          have fixedTest : ∀ secret ∈
              checkedBranch candidates (probeGuess position) 4
                (position, testColor) true,
              secret position = testColor := by
            intro secret secretMem
            have properties :=
              (mem_checkedBranch _ _ _ _ _ _).1 secretMem
            simpa using properties.2.2
          have separates := sep_five_of_common_matchSet_and_fixed
            (checkedBranch candidates (probeGuess position) 4
              (position, testColor) true)
            matchPositions position testColor (by omega)
            positionNotMatch
            (by
              intro secret secretMem
              exact commonMatches secret
                ((mem_checkedBranch _ _ _ _ _ _).1 secretMem).1)
            fixedTest
          exact separates.pad_add 3
        · have branchEmpty :
              checkedBranch candidates (probeGuess position) black
                (position, testColor) true = ∅ := by
            apply Finset.eq_empty_of_forall_notMem
            intro secret secretMem
            have properties :=
              (mem_checkedBranch _ _ _ _ _ _).1 secretMem
            by_cases secretLast : secret position = Fin.last 10
            · have answerFive :=
                probe_answer_eq_five_of_matchSet_card_four_of_last
                  secret position
                  (by
                    rw [commonMatches secret properties.1]
                    exact matchesCard)
                  secretLast
              exact blackFive (properties.2.1.symm.trans answerFive)
            · have answerFour :=
                probe_answer_eq_four_of_matchSet_card_four_of_other
                  secret position
                  (by
                    rw [commonMatches secret properties.1]
                    exact matchesCard)
                  (notCanonical secret properties.1) secretLast
              exact blackFour (properties.2.1.symm.trans answerFour)
          rw [branchEmpty]
          exact Sep.empty 8
    · by_cases blackFive : black = (5 : Fin 11)
      · subst black
        have fixedLast : ∀ secret ∈
            checkedBranch candidates (probeGuess position) 5
              (position, testColor) false,
            secret position = Fin.last 10 := by
          intro secret secretMem
          have properties :=
            (mem_checkedBranch _ _ _ _ _ _).1 secretMem
          by_contra secretNotLast
          have answerFour :=
            probe_answer_eq_four_of_matchSet_card_four_of_other
              secret position
              (by
                rw [commonMatches secret properties.1]
                exact matchesCard)
              (notCanonical secret properties.1) secretNotLast
          have impossible := properties.2.1.symm.trans answerFour
          have values := congrArg Fin.val impossible
          norm_num at values
        have separates := sep_five_of_common_matchSet_and_fixed
          (checkedBranch candidates (probeGuess position) 5
            (position, testColor) false)
          matchPositions position (Fin.last 10) (by omega)
          positionNotMatch
          (by
            intro secret secretMem
            exact commonMatches secret
              ((mem_checkedBranch _ _ _ _ _ _).1 secretMem).1)
          fixedLast
        exact separates.pad_add 3
      · by_cases blackFour : black = (4 : Fin 11)
        · subst black
          let remainingColors := supportColors.erase testColor
          have remainingColorsCard : remainingColors.card ≤ 3 + 1 := by
            have eraseCard := Finset.card_erase_add_one testColorMem
            simp [remainingColors]
            omega
          apply sep_of_bounded_color_set 3
              (checkedBranch candidates (probeGuess position) 4
                (position, testColor) false)
              (4 : Fin 11) matchPositions position remainingColors
              (by omega) positionNotMatch remainingColorsCard
          · intro secret secretMem
            exact commonMatches secret
              ((mem_checkedBranch _ _ _ _ _ _).1 secretMem).1
          · intro secret secretMem
            exact commonCanonicalBlack secret
              ((mem_checkedBranch _ _ _ _ _ _).1 secretMem).1
          · intro secret secretMem
            have properties :=
              (mem_checkedBranch _ _ _ _ _ _).1 secretMem
            have secretNotLast : secret position ≠ Fin.last 10 := by
              intro secretLast
              have answerFive :=
                probe_answer_eq_five_of_matchSet_card_four_of_last
                  secret position
                  (by
                    rw [commonMatches secret properties.1]
                    exact matchesCard)
                  secretLast
              have impossible := properties.2.1.symm.trans answerFive
              have values := congrArg Fin.val impossible
              norm_num at values
            have secretNotTest : secret position ≠ testColor := by
              simpa using properties.2.2
            have colorAllowed :=
              color_at_unmatched_mem_fourFiberSupportColors secret
                matchPositions position
                (commonMatches secret properties.1) positionNotMatch
            have colorSupport : secret position ∈ supportColors := by
              rcases Finset.mem_insert.mp colorAllowed with
                last | supported
              · exact (secretNotLast last).elim
              · exact supported
            exact Finset.mem_erase.mpr
              ⟨secretNotTest, colorSupport⟩
        · have branchEmpty :
              checkedBranch candidates (probeGuess position) black
                (position, testColor) false = ∅ := by
            apply Finset.eq_empty_of_forall_notMem
            intro secret secretMem
            have properties :=
              (mem_checkedBranch _ _ _ _ _ _).1 secretMem
            by_cases secretLast : secret position = Fin.last 10
            · have answerFive :=
                probe_answer_eq_five_of_matchSet_card_four_of_last
                  secret position
                  (by
                    rw [commonMatches secret properties.1]
                    exact matchesCard)
                  secretLast
              exact blackFive (properties.2.1.symm.trans answerFive)
            · have answerFour :=
                probe_answer_eq_four_of_matchSet_card_four_of_other
                  secret position
                  (by
                    rw [commonMatches secret properties.1]
                    exact matchesCard)
                  (notCanonical secret properties.1) secretLast
              exact blackFour (properties.2.1.symm.trans answerFour)
          rw [branchEmpty]
          exact Sep.empty 8


theorem fourFiberState4_sep_nine
    (firstBit : Bool)
    (black1 : Fin 11) (bit1 : Bool)
    (black2 : Fin 11) (bit2 : Bool)
    (black3 : Fin 11) (bit3 : Bool)
    (black4 : Fin 11) (bit4 : Bool) :
    Sep 9 (highFiberState4 (4 : Fin 11) firstBit black1 bit1
      black2 bit2 black3 bit3 black4 bit4) := by
  classical
  let candidates := highFiberState4 (4 : Fin 11) firstBit black1 bit1
    black2 bit2 black3 bit3 black4 bit4
  change Sep 9 candidates
  by_cases candidatesEmpty : candidates = ∅
  · rw [candidatesEmpty]
    exact Sep.empty 9
  · obtain ⟨anchor, anchorMem⟩ :=
      Finset.nonempty_iff_ne_empty.mpr candidatesEmpty
    let matchPositions := MatchSet canonicalFirstGuess anchor
    have matchesCard : matchPositions.card = 4 := by
      have anchorCanonical :=
        (mem_highFiberState4 (4 : Fin 11) firstBit black1 bit1
          black2 bit2 black3 bit3 black4 bit4 anchor).1 anchorMem |>.1
      have values := congrArg Fin.val anchorCanonical
      change (MatchSet canonicalFirstGuess anchor).card = 4 at values
      exact values
    apply sep_nine_of_common_matchSet_card_four candidates
      matchPositions matchesCard
    intro secret secretMem
    exact highFiberState4_common_matchSet (4 : Fin 11) firstBit
      black1 bit1 black2 bit2 black3 bit3 black4 bit4
      secretMem anchorMem

theorem fourFiberState3_sep_ten
    (firstBit : Bool)
    (black1 : Fin 11) (bit1 : Bool)
    (black2 : Fin 11) (bit2 : Bool)
    (black3 : Fin 11) (bit3 : Bool) :
    Sep 10 (highFiberState3 (4 : Fin 11) firstBit black1 bit1
      black2 bit2 black3 bit3) := by
  rw [sep_succ_iff]
  refine ⟨probeGuess 7, ?_⟩
  intro black4
  refine ⟨(8, 8), ?_, ?_⟩
  · exact fourFiberState4_sep_nine firstBit
      black1 bit1 black2 bit2 black3 bit3 black4 true
  · exact fourFiberState4_sep_nine firstBit
      black1 bit1 black2 bit2 black3 bit3 black4 false

theorem fourFiberState2_sep_eleven
    (firstBit : Bool)
    (black1 : Fin 11) (bit1 : Bool)
    (black2 : Fin 11) (bit2 : Bool) :
    Sep 11 (highFiberState2 (4 : Fin 11) firstBit black1 bit1
      black2 bit2) := by
  rw [sep_succ_iff]
  refine ⟨probeGuess 5, ?_⟩
  intro black3
  refine ⟨(6, 6), ?_, ?_⟩
  · exact fourFiberState3_sep_ten firstBit
      black1 bit1 black2 bit2 black3 true
  · exact fourFiberState3_sep_ten firstBit
      black1 bit1 black2 bit2 black3 false

theorem fourFiberState1_sep_twelve
    (firstBit : Bool)
    (black1 : Fin 11) (bit1 : Bool) :
    Sep 12 (highFiberState1 (4 : Fin 11) firstBit black1 bit1) := by
  rw [sep_succ_iff]
  refine ⟨probeGuess 3, ?_⟩
  intro black2
  refine ⟨(4, 4), ?_, ?_⟩
  · exact fourFiberState2_sep_eleven firstBit black1 bit1 black2 true
  · exact fourFiberState2_sep_eleven firstBit black1 bit1 black2 false

theorem fourFiberState0_sep_thirteen
    (firstBit : Bool) :
    Sep 13 (highFiberState0 (4 : Fin 11) firstBit) := by
  rw [sep_succ_iff]
  refine ⟨probeGuess 1, ?_⟩
  intro black1
  refine ⟨(2, 2), ?_, ?_⟩
  · exact fourFiberState1_sep_twelve firstBit black1 true
  · exact fourFiberState1_sep_twelve firstBit black1 false

/--
The canonical first black-answer fiber four is solved in at most fourteen
total rounds, including the canonical first query.
-/
theorem canonical_first_answer_four_total_fourteen :
    ∃ edge : Fin 10 × Fin 11,
      Sep 13 (checkedBranch (Finset.univ : Finset TenElevenSecret)
        canonicalFirstGuess (4 : Fin 11) edge true) ∧
      Sep 13 (checkedBranch (Finset.univ : Finset TenElevenSecret)
        canonicalFirstGuess (4 : Fin 11) edge false) := by
  refine ⟨(0, 0), ?_, ?_⟩
  · exact fourFiberState0_sep_thirteen true
  · exact fourFiberState0_sep_thirteen false

end BlackPegExtraCheck
