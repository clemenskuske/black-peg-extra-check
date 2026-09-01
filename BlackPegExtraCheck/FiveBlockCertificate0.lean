/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.FirstAnswerFibers

namespace BlackPegExtraCheck

def fiveFullBlack (black : Fin 6) : Fin 11 := ⟨black.val + 5, by omega⟩

def fiveResidualBlack? (black : Fin 11) : Option (Fin 6) :=
  if h : 5 ≤ black.val then some ⟨black.val - 5, by omega⟩ else none

def fiveLevel0State (_index : Fin 1) : Finset TenElevenSecret :=
  fiveBlockCandidates

def fiveLevel1DescriptorValues : List (Fin 1 × Fin 6 × Bool) :=
  [
    (0, 5, false),
    (0, 5, true),
    (0, 3, true),
    (0, 4, true),
    (0, 1, true),
    (0, 2, true),
    (0, 0, true),
    (0, 3, false),
    (0, 4, false),
    (0, 1, false),
    (0, 2, false),
    (0, 0, false)
  ]

def fiveLevel1Descriptor (index : Fin 12) : Fin 1 × Fin 6 × Bool :=
  fiveLevel1DescriptorValues[index.val]'(by simpa [fiveLevel1DescriptorValues] using index.isLt)

def fiveLevel0CheckValues : List (Fin 6 → Fin 10 × Fin 11) :=
  [
    ![(0, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)]
  ]

def fiveLevel0CheckReduced (index : Fin 1) : Fin 6 → Fin 10 × Fin 11 :=
  fiveLevel0CheckValues[index.val]'(by simpa [fiveLevel0CheckValues] using index.isLt)

def fiveLevel0YesValues : List (Fin 6 → Fin 12) :=
  [
    ![6, 4, 5, 2, 3, 1]
  ]

def fiveLevel0NoValues : List (Fin 6 → Fin 12) :=
  [
    ![11, 9, 10, 7, 8, 0]
  ]

def fiveLevel0Yes (index : Fin 1) : Fin 6 → Fin 12 :=
  fiveLevel0YesValues[index.val]'(by simpa [fiveLevel0YesValues] using index.isLt)

def fiveLevel0No (index : Fin 1) : Fin 6 → Fin 12 :=
  fiveLevel0NoValues[index.val]'(by simpa [fiveLevel0NoValues] using index.isLt)

def fiveLevel0Check (index : Fin 1) (black : Fin 11) : Fin 10 × Fin 11 :=
  match fiveResidualBlack? black with
  | some residual => fiveLevel0CheckReduced index residual
  | none => (0, 0)

def fiveLevel0Next (index : Fin 1) (black : Fin 11) (bit : Bool) : Fin 12 :=
  match fiveResidualBlack? black with
  | some residual =>
      if bit then fiveLevel0Yes index residual else fiveLevel0No index residual
  | none => 0

def fiveLevel0Guess (_index : Fin 1) : TenElevenSecret := fiveBlockGuess 0

def fiveLevel1State (index : Fin 12) : Finset TenElevenSecret :=
  let descriptor := fiveLevel1Descriptor index
  checkedBranch (fiveLevel0State descriptor.1) (fiveBlockGuess 0)
    (fiveFullBlack descriptor.2.1)
    (fiveLevel0CheckReduced descriptor.1 descriptor.2.1) descriptor.2.2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem fiveLevel0Transitions : ∀ node black bit,
    checkedBranch (fiveLevel0State node) (fiveLevel0Guess node) black
      (fiveLevel0Check node black) bit =
        fiveLevel1State (fiveLevel0Next node black bit) := by
  decide +kernel

end BlackPegExtraCheck
