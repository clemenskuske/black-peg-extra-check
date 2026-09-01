/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.SeparatorTransport
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Conditional strategies after the canonical first answer

This file develops upper bounds conditional on the black count returned by the
canonical first query. The game is the ten-field, eleven-color injection game;
the equality edge is chosen after the black answer, exactly as in `Sep`.
-/

namespace BlackPegExtraCheck

/-! ## The normalized five-field residual class -/

/-- The six residual colors `0,1,2,3,4,10`. -/
def fiveBlockColorValue (color : Fin 6) : Fin 11 :=
  if h : color.val < 5 then ⟨color.val, by omega⟩ else (10 : Fin 11)

theorem fiveBlockColorValue_injective :
    Function.Injective fiveBlockColorValue := by
  intro first second equal
  apply Fin.ext
  have valuesEqual := congrArg (fun color : Fin 11 => color.val) equal
  by_cases hfirst : first.val < 5
  · by_cases hsecond : second.val < 5
    · simpa [fiveBlockColorValue, hfirst, hsecond] using valuesEqual
    · simp [fiveBlockColorValue, hfirst, hsecond] at valuesEqual
      omega
  · by_cases hsecond : second.val < 5
    · simp [fiveBlockColorValue, hfirst, hsecond] at valuesEqual
      omega
    · omega

def fiveBlockColor : Fin 6 ↪ Fin 11 :=
  ⟨fiveBlockColorValue, fiveBlockColorValue_injective⟩

theorem fiveBlockColor_range (color : Fin 6) :
    (fiveBlockColor color).val < 5 ∨ (fiveBlockColor color).val = 10 := by
  by_cases hcolor : color.val < 5
  · left
    simp [fiveBlockColor, fiveBlockColorValue, hcolor]
  · right
    simp [fiveBlockColor, fiveBlockColorValue, hcolor]

/--
Lift a permutation of the six residual colors to a legal ten-field secret,
fixing fields and colors `5,6,7,8,9` pointwise.
-/
def fiveBlockSecret (permutation : Equiv.Perm (Fin 6)) : TenElevenSecret where
  toFun position :=
    if h : position.val < 5 then
      fiveBlockColor (permutation ⟨position.val, by omega⟩)
    else
      ⟨position.val, by omega⟩
  inj' := by
    intro first second equal
    by_cases hfirst : first.val < 5
    · by_cases hsecond : second.val < 5
      · have residualEqual :
            permutation ⟨first.val, by omega⟩ =
              permutation ⟨second.val, by omega⟩ := by
          apply fiveBlockColor.injective
          simpa [hfirst, hsecond] using equal
        have positionEqual : first.val = second.val := by
          have residualPositionEqual := permutation.injective residualEqual
          exact congrArg (fun position : Fin 6 => position.val)
            residualPositionEqual
        exact Fin.ext positionEqual
      · have range := fiveBlockColor_range
          (permutation ⟨first.val, by omega⟩)
        have valuesEqual :
            (fiveBlockColor (permutation ⟨first.val, by omega⟩)).val =
              second.val := by
          exact congrArg Fin.val (by simpa [hfirst, hsecond] using equal)
        omega
    · by_cases hsecond : second.val < 5
      · have range := fiveBlockColor_range
          (permutation ⟨second.val, by omega⟩)
        have valuesEqual :
            first.val =
              (fiveBlockColor (permutation ⟨second.val, by omega⟩)).val := by
          exact congrArg Fin.val (by simpa [hfirst, hsecond] using equal)
        omega
      · apply Fin.ext
        have valuesEqual := congrArg (fun color : Fin 11 => color.val) equal
        simpa [hfirst, hsecond] using valuesEqual

@[simp] theorem fiveBlockSecret_apply_of_lt
    (permutation : Equiv.Perm (Fin 6)) (position : Fin 10)
    (hposition : position.val < 5) :
    fiveBlockSecret permutation position =
      fiveBlockColor (permutation ⟨position.val, by omega⟩) := by
  change (if h : position.val < 5 then
      fiveBlockColor (permutation ⟨position.val, by omega⟩)
    else ⟨position.val, by omega⟩) = _
  rw [dif_pos hposition]

theorem fiveBlockSecret_injective : Function.Injective fiveBlockSecret := by
  intro first second equal
  apply perm_eq_of_castSucc_eq
  intro position
  let field : Fin 10 := ⟨position.val, by omega⟩
  have hfield : field.val < 5 := by
    simp [field]
  have pointEqual := congrArg
    (fun secret : TenElevenSecret => secret field) equal
  rw [fiveBlockSecret_apply_of_lt first field hfield,
    fiveBlockSecret_apply_of_lt second field hfield] at pointEqual
  have residualEqual := fiveBlockColor.injective pointEqual
  convert residualEqual using 1 <;> apply Fin.ext <;> rfl

def fiveBlockSecretEmbedding :
    Equiv.Perm (Fin 6) ↪ TenElevenSecret :=
  ⟨fiveBlockSecret, fiveBlockSecret_injective⟩

/-- All `6! = 720` residual states supported on the first five fields. -/
def fiveBlockCandidates : Finset TenElevenSecret :=
  Finset.univ.map fiveBlockSecretEmbedding

def fiveBlockGuessValues : Fin 5 → Fin 10 → Fin 11 :=
  ![
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    ![1, 2, 3, 0, 10, 5, 6, 7, 8, 9],
    ![2, 3, 0, 10, 1, 5, 6, 7, 8, 9],
    ![0, 10, 1, 4, 2, 5, 6, 7, 8, 9],
    ![3, 2, 4, 10, 0, 5, 6, 7, 8, 9]
  ]

def fiveBlockGuess (index : Fin 5) : TenElevenSecret where
  toFun := fiveBlockGuessValues index
  inj' := by
    fin_cases index <;> decide

def fiveBlockGuesses : List TenElevenSecret :=
  [fiveBlockGuess 0, fiveBlockGuess 1, fiveBlockGuess 2,
    fiveBlockGuess 3, fiveBlockGuess 4]

/-- Only residual edges are needed by the exact search. -/
def fiveBlockEdges : List (Fin 10 × Fin 11) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 10),
   (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 10),
   (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 10),
   (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 10),
   (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 10)]

/-!
A layered certificate names every reachable state only once. The transition
premise is finite and executable; checking it plus the child layer proves the
parent layer with the exact adaptive quantifier order.
-/
theorem sep_of_layer {nodeCount childCount depth : Nat}
    (states : Fin nodeCount → Finset TenElevenSecret)
    (guess : Fin nodeCount → TenElevenSecret)
    (edge : Fin nodeCount → Fin 11 → Fin 10 × Fin 11)
    (next : Fin nodeCount → Fin 11 → Bool → Fin childCount)
    (childStates : Fin childCount → Finset TenElevenSecret)
    (transition : ∀ node black bit,
      checkedBranch (states node) (guess node) black (edge node black) bit =
        childStates (next node black bit))
    (childrenSeparate : ∀ child, Sep depth (childStates child)) :
    ∀ node, Sep (depth + 1) (states node) := by
  intro node
  rw [sep_succ_iff]
  refine ⟨guess node, ?_⟩
  intro black
  refine ⟨edge node black, ?_, ?_⟩
  · rw [transition node black true]
    exact childrenSeparate _
  · rw [transition node black false]
    exact childrenSeparate _

end BlackPegExtraCheck
