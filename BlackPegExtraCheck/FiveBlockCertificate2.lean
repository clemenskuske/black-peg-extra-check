/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.FiveBlockCertificate2Cases0
import BlackPegExtraCheck.FiveBlockCertificate2Cases1
import BlackPegExtraCheck.FiveBlockCertificate2Cases2
import BlackPegExtraCheck.FiveBlockCertificate2Cases3
import BlackPegExtraCheck.FiveBlockCertificate2Cases4
import BlackPegExtraCheck.FiveBlockCertificate2Cases5
import BlackPegExtraCheck.FiveBlockCertificate2Cases6
import BlackPegExtraCheck.FiveBlockCertificate2Cases7

namespace BlackPegExtraCheck

theorem fiveLevel2Transitions : ∀ node black bit,
    checkedBranch (fiveLevel2State node) (fiveLevel2Guess node) black
      (fiveLevel2Check node black) bit =
        fiveLevel3State (fiveLevel2Next node black bit) := by
  intro node
  change fiveLevel2TransitionAt node
  fin_cases node
  · exact fiveLevel2Transition_0
  · exact fiveLevel2Transition_1
  · exact fiveLevel2Transition_2
  · exact fiveLevel2Transition_3
  · exact fiveLevel2Transition_4
  · exact fiveLevel2Transition_5
  · exact fiveLevel2Transition_6
  · exact fiveLevel2Transition_7
  · exact fiveLevel2Transition_8
  · exact fiveLevel2Transition_9
  · exact fiveLevel2Transition_10
  · exact fiveLevel2Transition_11
  · exact fiveLevel2Transition_12
  · exact fiveLevel2Transition_13
  · exact fiveLevel2Transition_14
  · exact fiveLevel2Transition_15
  · exact fiveLevel2Transition_16
  · exact fiveLevel2Transition_17
  · exact fiveLevel2Transition_18
  · exact fiveLevel2Transition_19
  · exact fiveLevel2Transition_20
  · exact fiveLevel2Transition_21
  · exact fiveLevel2Transition_22
  · exact fiveLevel2Transition_23
  · exact fiveLevel2Transition_24
  · exact fiveLevel2Transition_25
  · exact fiveLevel2Transition_26
  · exact fiveLevel2Transition_27
  · exact fiveLevel2Transition_28
  · exact fiveLevel2Transition_29
  · exact fiveLevel2Transition_30
  · exact fiveLevel2Transition_31
  · exact fiveLevel2Transition_32
  · exact fiveLevel2Transition_33
  · exact fiveLevel2Transition_34
  · exact fiveLevel2Transition_35
  · exact fiveLevel2Transition_36
  · exact fiveLevel2Transition_37
  · exact fiveLevel2Transition_38
  · exact fiveLevel2Transition_39
  · exact fiveLevel2Transition_40
  · exact fiveLevel2Transition_41
  · exact fiveLevel2Transition_42
  · exact fiveLevel2Transition_43
  · exact fiveLevel2Transition_44
  · exact fiveLevel2Transition_45
  · exact fiveLevel2Transition_46
  · exact fiveLevel2Transition_47
  · exact fiveLevel2Transition_48
  · exact fiveLevel2Transition_49
  · exact fiveLevel2Transition_50
  · exact fiveLevel2Transition_51
  · exact fiveLevel2Transition_52
  · exact fiveLevel2Transition_53
  · exact fiveLevel2Transition_54
  · exact fiveLevel2Transition_55
  · exact fiveLevel2Transition_56
  · exact fiveLevel2Transition_57
  · exact fiveLevel2Transition_58
  · exact fiveLevel2Transition_59
  · exact fiveLevel2Transition_60

end BlackPegExtraCheck
