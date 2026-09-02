/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.FiveBlockTerminal

namespace BlackPegExtraCheck

theorem fiveLevel5_sep_zero : ∀ index, Sep 0 (fiveLevel5State index) := by
  intro index
  exact fiveLevel5_card index

theorem fiveLevel4_sep_1 : ∀ index, Sep 1 (fiveLevel4State index) := by
  simpa using sep_of_layer
    fiveLevel4State fiveLevel4Guess fiveLevel4Check fiveLevel4Next
    fiveLevel5State fiveLevel4Transitions fiveLevel5_sep_zero

theorem fiveLevel3_sep_2 : ∀ index, Sep 2 (fiveLevel3State index) := by
  simpa using sep_of_layer
    fiveLevel3State fiveLevel3Guess fiveLevel3Check fiveLevel3Next
    fiveLevel4State fiveLevel3Transitions fiveLevel4_sep_1

theorem fiveLevel2_sep_3 : ∀ index, Sep 3 (fiveLevel2State index) := by
  simpa using sep_of_layer
    fiveLevel2State fiveLevel2Guess fiveLevel2Check fiveLevel2Next
    fiveLevel3State fiveLevel2Transitions fiveLevel3_sep_2

theorem fiveLevel1_sep_4 : ∀ index, Sep 4 (fiveLevel1State index) := by
  simpa using sep_of_layer
    fiveLevel1State fiveLevel1Guess fiveLevel1Check fiveLevel1Next
    fiveLevel2State fiveLevel1Transitions fiveLevel2_sep_3

theorem fiveLevel0_sep_5 : ∀ index, Sep 5 (fiveLevel0State index) := by
  simpa using sep_of_layer
    fiveLevel0State fiveLevel0Guess fiveLevel0Check fiveLevel0Next
    fiveLevel1State fiveLevel0Transitions fiveLevel1_sep_4

/-- The normalized 720-state residual class is solved in five rounds. -/
theorem fiveBlockCandidates_sep_five : Sep 5 fiveBlockCandidates := by
  simpa [fiveLevel0State] using fiveLevel0_sep_5 (0 : Fin 1)

end BlackPegExtraCheck
