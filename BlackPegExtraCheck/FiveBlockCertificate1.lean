/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.FiveBlockCertificate0

namespace BlackPegExtraCheck

def fiveLevel2DescriptorValues : List (Fin 12 × Fin 6 × Bool) :=
  [
    (0, 0, true),
    (1, 0, true),
    (3, 1, true),
    (5, 2, true),
    (2, 1, true),
    (2, 0, true),
    (3, 0, true),
    (4, 3, true),
    (4, 3, false),
    (4, 2, true),
    (5, 2, false),
    (4, 1, true),
    (4, 0, true),
    (5, 1, true),
    (2, 1, false),
    (4, 2, false),
    (2, 0, false),
    (3, 0, false),
    (5, 0, true),
    (5, 1, false),
    (4, 1, false),
    (4, 0, false),
    (5, 0, false),
    (9, 4, false),
    (6, 5, false),
    (6, 4, true),
    (6, 3, true),
    (6, 4, false),
    (6, 1, false),
    (10, 2, true),
    (7, 1, true),
    (6, 3, false),
    (9, 2, true),
    (6, 2, true),
    (6, 2, false),
    (6, 1, true),
    (9, 1, true),
    (11, 0, true),
    (7, 0, false),
    (9, 3, false),
    (11, 4, false),
    (11, 3, true),
    (9, 0, false),
    (11, 1, true),
    (7, 1, false),
    (7, 0, true),
    (8, 0, false),
    (10, 2, false),
    (10, 1, true),
    (10, 0, false),
    (11, 3, false),
    (9, 3, true),
    (9, 2, false),
    (11, 2, false),
    (10, 1, false),
    (11, 0, false),
    (9, 1, false),
    (9, 0, true),
    (10, 0, true),
    (11, 2, true),
    (11, 1, false)
  ]

def fiveLevel2Descriptor (index : Fin 61) : Fin 12 × Fin 6 × Bool :=
  fiveLevel2DescriptorValues[index.val]'(by simpa [fiveLevel2DescriptorValues] using index.isLt)

def fiveLevel1CheckValues : List (Fin 6 → Fin 10 × Fin 11) :=
  [
    ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)],
    ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)],
    ![(1, 1), (1, 1), (0, 0), (0, 0), (0, 0), (0, 0)],
    ![(1, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)],
    ![(1, 3), (1, 2), (1, 2), (3, 1), (0, 0), (0, 0)],
    ![(2, 2), (4, 10), (1, 1), (0, 0), (0, 0), (0, 0)],
    ![(0, 0), (3, 2), (2, 3), (1, 2), (1, 2), (0, 0)],
    ![(0, 10), (0, 1), (0, 0), (0, 0), (0, 0), (0, 0)],
    ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)],
    ![(0, 10), (0, 1), (0, 1), (1, 2), (0, 0), (0, 0)],
    ![(2, 2), (1, 1), (0, 1), (0, 0), (0, 0), (0, 0)],
    ![(0, 2), (0, 4), (2, 3), (0, 4), (0, 0), (0, 0)]
  ]

def fiveLevel1CheckReduced (index : Fin 12) : Fin 6 → Fin 10 × Fin 11 :=
  fiveLevel1CheckValues[index.val]'(by simpa [fiveLevel1CheckValues] using index.isLt)

def fiveLevel1YesValues : List (Fin 6 → Fin 61) :=
  [
    ![0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0],
    ![5, 4, 0, 0, 0, 0],
    ![6, 2, 0, 0, 0, 0],
    ![12, 11, 9, 7, 0, 0],
    ![18, 13, 3, 0, 0, 0],
    ![0, 35, 33, 26, 25, 0],
    ![45, 30, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![57, 36, 32, 51, 0, 0],
    ![58, 48, 29, 0, 0, 0],
    ![37, 43, 59, 41, 0, 0]
  ]

def fiveLevel1NoValues : List (Fin 6 → Fin 61) :=
  [
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![16, 14, 0, 0, 0, 0],
    ![17, 0, 0, 0, 0, 0],
    ![21, 20, 15, 8, 0, 0],
    ![22, 19, 10, 0, 0, 0],
    ![0, 28, 34, 31, 27, 24],
    ![38, 44, 0, 0, 0, 0],
    ![46, 0, 0, 0, 0, 0],
    ![42, 56, 52, 39, 23, 0],
    ![49, 54, 47, 0, 0, 0],
    ![55, 60, 53, 50, 40, 0]
  ]

def fiveLevel1Yes (index : Fin 12) : Fin 6 → Fin 61 :=
  fiveLevel1YesValues[index.val]'(by simpa [fiveLevel1YesValues] using index.isLt)

def fiveLevel1No (index : Fin 12) : Fin 6 → Fin 61 :=
  fiveLevel1NoValues[index.val]'(by simpa [fiveLevel1NoValues] using index.isLt)

def fiveLevel1Check (index : Fin 12) (black : Fin 11) : Fin 10 × Fin 11 :=
  match fiveResidualBlack? black with
  | some residual => fiveLevel1CheckReduced index residual
  | none => (0, 0)

def fiveLevel1Next (index : Fin 12) (black : Fin 11) (bit : Bool) : Fin 61 :=
  match fiveResidualBlack? black with
  | some residual =>
      if bit then fiveLevel1Yes index residual else fiveLevel1No index residual
  | none => 0

def fiveLevel1Guess (_index : Fin 12) : TenElevenSecret := fiveBlockGuess 1

def fiveLevel2State (index : Fin 61) : Finset TenElevenSecret :=
  let descriptor := fiveLevel2Descriptor index
  checkedBranch (fiveLevel1State descriptor.1) (fiveBlockGuess 1)
    (fiveFullBlack descriptor.2.1)
    (fiveLevel1CheckReduced descriptor.1 descriptor.2.1) descriptor.2.2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem fiveLevel1Transitions : ∀ node black bit,
    checkedBranch (fiveLevel1State node) (fiveLevel1Guess node) black
      (fiveLevel1Check node black) bit =
        fiveLevel2State (fiveLevel1Next node black bit) := by
  decide +kernel

end BlackPegExtraCheck
