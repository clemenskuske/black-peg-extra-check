/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.FiveBlockCertificate3Data

namespace BlackPegExtraCheck

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem fiveLevel3Transition_240 : fiveLevel3TransitionAt 240 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem fiveLevel3Transition_241 : fiveLevel3TransitionAt 241 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem fiveLevel3Transition_242 : fiveLevel3TransitionAt 242 := by
  decide +kernel

end BlackPegExtraCheck
