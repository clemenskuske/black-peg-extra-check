/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.FiveBlockCertificate
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# High canonical first-answer fibers

The canonical first query is followed by four probe queries. Their black
answers and the five adaptive equality bits identify the canonical match set.
If the first black answer is at least five, the remaining mismatch support has
size at most five and transports to the verified five-block certificate.
-/

namespace BlackPegExtraCheck

def canonicalFirstGuess : TenElevenSecret := Fin.castSuccEmb

@[simp] theorem canonicalFirstGuess_apply (position : Fin 10) :
    canonicalFirstGuess position = position.castSucc := rfl

def positionColorPerm (positions : Equiv.Perm (Fin 10)) :
    Equiv.Perm (Fin 11) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr positions (Equiv.refl (Fin 1))).trans finSumFinEquiv)

@[simp] theorem positionColorPerm_castSucc
    (positions : Equiv.Perm (Fin 10)) (position : Fin 10) :
    positionColorPerm positions position.castSucc =
      (positions position).castSucc := by
  unfold positionColorPerm
  simp only [Equiv.trans_apply, finSumFinEquiv_symm_apply_castSucc]
  change finSumFinEquiv (Sum.inl (positions position)) =
    (positions position).castSucc
  apply Fin.ext
  rfl

@[simp] theorem positionColorPerm_last
    (positions : Equiv.Perm (Fin 10)) :
    positionColorPerm positions (Fin.last 10) = Fin.last 10 := by
  change finSumFinEquiv
    (Sum.map positions id (finSumFinEquiv.symm (Fin.last 10))) =
      Fin.last 10
  rw [finSumFinEquiv_symm_last]
  rfl

noncomputable def supportToFirstFive
    (support : Finset (Fin 10)) (hcard : support.card = 5) :
    Equiv.Perm (Fin 10) :=
  Classical.choose <| Equiv.Perm.exists_extending_pair
    (fun position : Fin 5 => (support.orderIsoOfFin hcard position).1)
    (fun position : Fin 5 => position.castAdd 5)
    (by
      intro first second equal
      apply (support.orderIsoOfFin hcard).injective
      apply Subtype.ext
      exact equal)
    (Fin.castAdd_injective 5 5)

theorem supportToFirstFive_apply
    (support : Finset (Fin 10)) (hcard : support.card = 5)
    (position : Fin 5) :
    supportToFirstFive support hcard
        (support.orderIsoOfFin hcard position).1 =
      position.castAdd 5 := by
  exact (Classical.choose_spec <| Equiv.Perm.exists_extending_pair
    (fun position : Fin 5 => (support.orderIsoOfFin hcard position).1)
    (fun position : Fin 5 => position.castAdd 5)
    (by
      intro first second equal
      apply (support.orderIsoOfFin hcard).injective
      apply Subtype.ext
      exact equal)
    (Fin.castAdd_injective 5 5)) position

theorem supportToFirstFive_lt
    (support : Finset (Fin 10)) (hcard : support.card = 5)
    {position : Fin 10} (hposition : position ∈ support) :
    (supportToFirstFive support hcard position).val < 5 := by
  let member : support := ⟨position, hposition⟩
  obtain ⟨index, hindex⟩ :=
    (support.orderIsoOfFin hcard).surjective member
  change (supportToFirstFive support hcard member.1).val < 5
  rw [← hindex]
  rw [supportToFirstFive_apply]
  exact index.isLt

def fiveBlockColorIndex (color : Fin 11)
    (hrange : color.val < 5 ∨ color.val = 10) : Fin 6 :=
  if hsmall : color.val < 5 then
    ⟨color.val, by omega⟩
  else
    5

theorem fiveBlockColor_decode (color : Fin 11)
    (hrange : color.val < 5 ∨ color.val = 10) :
    fiveBlockColor (fiveBlockColorIndex color hrange) = color := by
  by_cases hsmall : color.val < 5
  · apply Fin.ext
    simp [fiveBlockColor, fiveBlockColorValue, fiveBlockColorIndex, hsmall]
  · have hlast : color.val = 10 := hrange.resolve_left hsmall
    apply Fin.ext
    simp [fiveBlockColor, fiveBlockColorValue, fiveBlockColorIndex, hsmall,
      hlast]

@[simp] theorem fiveBlockSecret_apply_of_ge
    (permutation : Equiv.Perm (Fin 6)) (position : Fin 10)
    (hposition : 5 ≤ position.val) :
    fiveBlockSecret permutation position = position.castSucc := by
  change (if h : position.val < 5 then
      fiveBlockColor (permutation ⟨position.val, by omega⟩)
    else ⟨position.val, by omega⟩) = _
  rw [dif_neg (by omega)]
  rfl

theorem mem_fiveBlockCandidates_of_normalized
    (secret : TenElevenSecret)
    (fixedTail : ∀ position, 5 ≤ position.val →
      secret position = position.castSucc)
    (residualRange : ∀ position, position.val < 5 →
      (secret position).val < 5 ∨ (secret position).val = 10) :
    secret ∈ fiveBlockCandidates := by
  let residual : Fin 5 → Fin 6 := fun position =>
    fiveBlockColorIndex (secret (position.castAdd 5))
      (residualRange (position.castAdd 5) (by simpa using position.isLt))
  have residualInjective : Function.Injective residual := by
    intro first second equal
    have colorsEqual := congrArg fiveBlockColor equal
    have decodedFirst := fiveBlockColor_decode
      (secret (first.castAdd 5))
      (residualRange (first.castAdd 5) (by simpa using first.isLt))
    have decodedSecond := fiveBlockColor_decode
      (secret (second.castAdd 5))
      (residualRange (second.castAdd 5) (by simpa using second.isLt))
    have secretEqual : secret (first.castAdd 5) =
        secret (second.castAdd 5) := by
      rw [← decodedFirst, ← decodedSecond]
      exact colorsEqual
    exact Fin.castAdd_injective 5 5 (secret.injective secretEqual)
  obtain ⟨permutation, extensionSpec⟩ := Equiv.Perm.exists_extending_pair
    (fun position : Fin 5 => position.castSucc)
    residual (Fin.castSucc_injective 5) residualInjective
  have secretEqual : fiveBlockSecret permutation = secret := by
    apply Function.Embedding.ext
    intro position
    by_cases hposition : position.val < 5
    · let residualPosition : Fin 5 := ⟨position.val, hposition⟩
      have positionEq : residualPosition.castAdd 5 = position := by
        apply Fin.ext
        rfl
      rw [fiveBlockSecret_apply_of_lt permutation position hposition]
      change fiveBlockColor (permutation residualPosition.castSucc) =
        secret position
      have extension := extensionSpec residualPosition
      change permutation residualPosition.castSucc =
        residual residualPosition at extension
      rw [extension]
      change fiveBlockColor
          (fiveBlockColorIndex
            (secret (residualPosition.castAdd 5))
            (residualRange (residualPosition.castAdd 5) (by omega))) =
        secret position
      rw [fiveBlockColor_decode, positionEq]
    · rw [fiveBlockSecret_apply_of_ge permutation position (by omega)]
      exact (fixedTail position (by omega)).symm
  rw [fiveBlockCandidates]
  refine Finset.mem_map.2 ⟨permutation, Finset.mem_univ _, ?_⟩
  exact secretEqual

theorem residualRange_of_fixedTail
    (secret : TenElevenSecret)
    (fixedTail : ∀ position, 5 ≤ position.val →
      secret position = position.castSucc)
    (position : Fin 10) (hposition : position.val < 5) :
    (secret position).val < 5 ∨ (secret position).val = 10 := by
  by_contra hrange
  push_neg at hrange
  have colorLtTen : (secret position).val < 10 := by
    omega
  let collisionPosition : Fin 10 :=
    ⟨(secret position).val, colorLtTen⟩
  have collisionFixed :
      secret collisionPosition = collisionPosition.castSucc :=
    fixedTail collisionPosition (by
      simp [collisionPosition]
      omega)
  have colorEqual :
      secret position = secret collisionPosition := by
    rw [collisionFixed]
    apply Fin.ext
    rfl
  have positionEqual := secret.injective colorEqual
  have valuesEqual := congrArg Fin.val positionEqual
  simp [collisionPosition] at valuesEqual
  omega

theorem sep_five_of_support
    (candidates : Finset TenElevenSecret)
    (support : Finset (Fin 10))
    (supportCard : support.card ≤ 5)
    (fixedOutside : ∀ secret ∈ candidates, ∀ position,
      position ∉ support → secret position = position.castSucc) :
    Sep 5 candidates := by
  classical
  obtain ⟨fullSupport, supportSubset, fullSupportCard⟩ :=
    Finset.exists_superset_card_eq supportCard (by norm_num)
  let positions := supportToFirstFive fullSupport fullSupportCard
  let colors := positionColorPerm positions
  have mappedSubset :
      TenElevenSymmetry.mapCandidates positions colors candidates ⊆
        fiveBlockCandidates := by
    intro mappedSecret mappedMem
    rcases Finset.mem_map.1 mappedMem with
      ⟨secret, secretMem, mappedEq⟩
    rw [← mappedEq]
    apply mem_fiveBlockCandidates_of_normalized
    · intro mappedPosition hmappedPosition
      change TenElevenSymmetry.mapSecret positions colors secret mappedPosition =
        mappedPosition.castSucc
      let originalPosition := positions.symm mappedPosition
      have originalOutsideFull : originalPosition ∉ fullSupport := by
        intro originalMem
        have mappedSmall := supportToFirstFive_lt fullSupport
          fullSupportCard originalMem
        have mappedBack : positions originalPosition = mappedPosition := by
          simp [originalPosition]
        rw [mappedBack] at mappedSmall
        omega
      have originalOutside : originalPosition ∉ support := by
        intro originalMem
        exact originalOutsideFull (supportSubset originalMem)
      rw [TenElevenSymmetry.mapSecret_apply]
      rw [fixedOutside secret secretMem originalPosition originalOutside]
      change colors originalPosition.castSucc = mappedPosition.castSucc
      rw [positionColorPerm_castSucc]
      simp [originalPosition]
    · intro mappedPosition hmappedPosition
      apply residualRange_of_fixedTail
        (TenElevenSymmetry.mapSecret positions colors secret)
      · intro tailPosition htailPosition
        let originalPosition := positions.symm tailPosition
        have originalOutsideFull : originalPosition ∉ fullSupport := by
          intro originalMem
          have mappedSmall := supportToFirstFive_lt fullSupport
            fullSupportCard originalMem
          have mappedBack : positions originalPosition = tailPosition := by
            simp [originalPosition]
          rw [mappedBack] at mappedSmall
          omega
        have originalOutside : originalPosition ∉ support := by
          intro originalMem
          exact originalOutsideFull (supportSubset originalMem)
        rw [TenElevenSymmetry.mapSecret_apply]
        rw [fixedOutside secret secretMem originalPosition originalOutside]
        change colors originalPosition.castSucc = tailPosition.castSucc
        rw [positionColorPerm_castSucc]
        simp [originalPosition]
      · exact hmappedPosition
  have mappedSep : Sep 5
      (TenElevenSymmetry.mapCandidates positions colors candidates) :=
    Sep.mono mappedSubset fiveBlockCandidates_sep_five
  exact TenElevenSymmetry.Sep.unmap positions.symm colors.symm mappedSep

theorem sep_five_of_common_matchSet
    (candidates : Finset TenElevenSecret)
    (matchPositions : Finset (Fin 10))
    (matchesCard : 5 ≤ matchPositions.card)
    (commonMatches : ∀ secret ∈ candidates,
      MatchSet canonicalFirstGuess secret = matchPositions) :
    Sep 5 candidates := by
  classical
  let support : Finset (Fin 10) := matchPositionsᶜ
  apply sep_five_of_support candidates support
  · have complementCard := Finset.card_compl matchPositions
    simp only [Fintype.card_fin] at complementCard
    simp [support]
    omega
  · intro secret secretMem position positionOutside
    have positionMatched : position ∈ matchPositions := by
      simpa [support] using positionOutside
    have positionInMatchSet :
        position ∈ MatchSet canonicalFirstGuess secret := by
      rw [commonMatches secret secretMem]
      exact positionMatched
    exact (Finset.mem_filter.1 positionInMatchSet).2


/-! ## Four canonical-match probes -/

def probeGuessValue (probePosition position : Fin 10) : Fin 11 :=
  if position = probePosition then Fin.last 10 else position.castSucc

def probeGuess (probePosition : Fin 10) : TenElevenSecret where
  toFun := probeGuessValue probePosition
  inj' := by
    intro first second equal
    by_cases hfirst : first = probePosition
    · by_cases hsecond : second = probePosition
      · exact hfirst.trans hsecond.symm
      · have values := congrArg Fin.val equal
        simp [probeGuessValue, hfirst, hsecond] at values
        omega
    · by_cases hsecond : second = probePosition
      · have values := congrArg Fin.val equal
        simp [probeGuessValue, hfirst, hsecond] at values
        omega
      · have values := congrArg Fin.val equal
        simp [probeGuessValue, hfirst, hsecond] at values
        exact Fin.ext values

@[simp] theorem probeGuess_apply_same (probePosition : Fin 10) :
    probeGuess probePosition probePosition = Fin.last 10 := by
  change probeGuessValue probePosition probePosition = Fin.last 10
  simp [probeGuessValue]

@[simp] theorem probeGuess_apply_ne (probePosition position : Fin 10)
    (hne : position ≠ probePosition) :
    probeGuess probePosition position = position.castSucc := by
  change probeGuessValue probePosition position = position.castSucc
  simp [probeGuessValue, hne]

theorem matchSet_probe_of_canonical_match
    (secret : TenElevenSecret) (position : Fin 10)
    (hmatch : secret position = position.castSucc) :
    MatchSet (probeGuess position) secret =
      (MatchSet canonicalFirstGuess secret).erase position := by
  ext other
  simp only [MatchSet, Finset.mem_erase, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_cases hother : other = position
  · subst other
    rw [probeGuess_apply_same]
    constructor
    · intro equal
      rw [hmatch] at equal
      exact (Fin.castSucc_ne_last position equal).elim
    · intro impossible
      exact (impossible.1 rfl).elim
  · rw [probeGuess_apply_ne position other hother]
    simp [hother]

theorem matchSet_probe_of_last
    (secret : TenElevenSecret) (position : Fin 10)
    (hlast : secret position = Fin.last 10) :
    MatchSet (probeGuess position) secret =
      insert position (MatchSet canonicalFirstGuess secret) := by
  ext other
  simp only [MatchSet, Finset.mem_insert, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_cases hother : other = position
  · subst other
    rw [probeGuess_apply_same, hlast]
    simp
  · rw [probeGuess_apply_ne position other hother]
    simp [hother]

theorem matchSet_probe_of_other
    (secret : TenElevenSecret) (position : Fin 10)
    (hnotCanonical : secret position ≠ position.castSucc)
    (hnotLast : secret position ≠ Fin.last 10) :
    MatchSet (probeGuess position) secret =
      MatchSet canonicalFirstGuess secret := by
  ext other
  simp only [MatchSet, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hother : other = position
  · subst other
    rw [probeGuess_apply_same]
    exact ⟨
      fun equal => (hnotLast (by simpa using equal)).elim,
      fun equal => (hnotCanonical (by simpa [canonicalFirstGuess] using equal)).elim⟩
  · rw [probeGuess_apply_ne position other hother]
    rfl

theorem probe_card_add_one_of_canonical_match
    (secret : TenElevenSecret) (position : Fin 10)
    (hmatch : secret position = position.castSucc) :
    (MatchSet (probeGuess position) secret).card + 1 =
      (MatchSet canonicalFirstGuess secret).card := by
  rw [matchSet_probe_of_canonical_match secret position hmatch]
  apply Finset.card_erase_add_one
  simp only [MatchSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hmatch

theorem canonical_card_add_one_of_last
    (secret : TenElevenSecret) (position : Fin 10)
    (hlast : secret position = Fin.last 10) :
    (MatchSet canonicalFirstGuess secret).card + 1 =
      (MatchSet (probeGuess position) secret).card := by
  rw [matchSet_probe_of_last secret position hlast]
  symm
  apply Finset.card_insert_of_notMem
  have hnotCanonical : secret position ≠ position.castSucc := by
    intro equal
    rw [hlast] at equal
    exact Fin.castSucc_ne_last position equal.symm
  simp only [MatchSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hnotCanonical

theorem probe_card_eq_of_other
    (secret : TenElevenSecret) (position : Fin 10)
    (hnotCanonical : secret position ≠ position.castSucc)
    (hnotLast : secret position ≠ Fin.last 10) :
    (MatchSet (probeGuess position) secret).card =
      (MatchSet canonicalFirstGuess secret).card := by
  rw [matchSet_probe_of_other secret position hnotCanonical hnotLast]

theorem probe_black_determines_canonical_match
    (first second : TenElevenSecret) (position : Fin 10)
    (canonicalEqual :
      tenElevenBlackAnswer canonicalFirstGuess first =
        tenElevenBlackAnswer canonicalFirstGuess second)
    (probeEqual :
      tenElevenBlackAnswer (probeGuess position) first =
        tenElevenBlackAnswer (probeGuess position) second) :
    (first position = position.castSucc) ↔
      (second position = position.castSucc) := by
  have canonicalCardEqual :
      (MatchSet canonicalFirstGuess first).card =
        (MatchSet canonicalFirstGuess second).card :=
    congrArg Fin.val canonicalEqual
  have probeCardEqual :
      (MatchSet (probeGuess position) first).card =
        (MatchSet (probeGuess position) second).card :=
    congrArg Fin.val probeEqual
  have forward : ∀ (left right : TenElevenSecret),
      (MatchSet canonicalFirstGuess left).card =
        (MatchSet canonicalFirstGuess right).card →
      (MatchSet (probeGuess position) left).card =
        (MatchSet (probeGuess position) right).card →
      left position = position.castSucc →
      right position = position.castSucc := by
    intro left right canonicalCards probeCards leftMatch
    by_contra rightMatch
    have leftCards :=
      probe_card_add_one_of_canonical_match left position leftMatch
    by_cases rightLast : right position = Fin.last 10
    · have rightCards :=
        canonical_card_add_one_of_last right position rightLast
      omega
    · have rightCards :=
        probe_card_eq_of_other right position rightMatch rightLast
      omega
  exact ⟨forward first second canonicalCardEqual probeCardEqual,
    forward second first canonicalCardEqual.symm probeCardEqual.symm⟩


/-! ## Transcript states and the ten-round conditional bound -/

theorem iff_of_decide_eq_same_bool {first second : Prop}
    [Decidable first] [Decidable second] {bit : Bool}
    (firstBit : decide first = bit) (secondBit : decide second = bit) :
    first ↔ second := by
  by_cases hfirst : first <;> by_cases hsecond : second <;>
    simp_all

theorem finset_fin_ten_eq_of_card_eq_of_agree_before_last
    (first second : Finset (Fin 10))
    (cardEqual : first.card = second.card)
    (agreeBeforeLast : ∀ position, position ≠ (9 : Fin 10) →
      (position ∈ first ↔ position ∈ second)) :
    first = second := by
  classical
  have erasedEqual :
      first.erase (9 : Fin 10) = second.erase (9 : Fin 10) := by
    ext position
    simp only [Finset.mem_erase]
    by_cases hlast : position = (9 : Fin 10)
    · subst position
      simp
    · constructor
      · intro h
        exact ⟨h.1, (agreeBeforeLast position hlast).1 h.2⟩
      · intro h
        exact ⟨h.1, (agreeBeforeLast position hlast).2 h.2⟩
  have lastAgree :
      ((9 : Fin 10) ∈ first) ↔ ((9 : Fin 10) ∈ second) := by
    constructor
    · intro firstLast
      by_contra secondLast
      have firstCard := Finset.card_erase_add_one firstLast
      have secondErase :
          second.erase (9 : Fin 10) = second :=
        Finset.erase_eq_of_notMem secondLast
      have erasedCard := congrArg Finset.card erasedEqual
      rw [secondErase] at erasedCard
      omega
    · intro secondLast
      by_contra firstLast
      have secondCard := Finset.card_erase_add_one secondLast
      have firstErase :
          first.erase (9 : Fin 10) = first :=
        Finset.erase_eq_of_notMem firstLast
      have erasedCard := congrArg Finset.card erasedEqual
      rw [firstErase] at erasedCard
      omega
  ext position
  by_cases hlast : position = (9 : Fin 10)
  · subst position
    exact lastAgree
  · exact agreeBeforeLast position hlast

noncomputable def highFiberState0 (firstBlack : Fin 11) (firstBit : Bool) :
    Finset TenElevenSecret :=
  checkedBranch (Finset.univ : Finset TenElevenSecret)
    canonicalFirstGuess firstBlack (0, 0) firstBit

noncomputable def highFiberState1 (firstBlack : Fin 11) (firstBit : Bool)
    (black1 : Fin 11) (bit1 : Bool) : Finset TenElevenSecret :=
  checkedBranch (highFiberState0 firstBlack firstBit)
    (probeGuess 1) black1 (2, 2) bit1

noncomputable def highFiberState2 (firstBlack : Fin 11) (firstBit : Bool)
    (black1 : Fin 11) (bit1 : Bool)
    (black2 : Fin 11) (bit2 : Bool) : Finset TenElevenSecret :=
  checkedBranch
    (highFiberState1 firstBlack firstBit black1 bit1)
    (probeGuess 3) black2 (4, 4) bit2

noncomputable def highFiberState3 (firstBlack : Fin 11) (firstBit : Bool)
    (black1 : Fin 11) (bit1 : Bool)
    (black2 : Fin 11) (bit2 : Bool)
    (black3 : Fin 11) (bit3 : Bool) : Finset TenElevenSecret :=
  checkedBranch
    (highFiberState2 firstBlack firstBit black1 bit1 black2 bit2)
    (probeGuess 5) black3 (6, 6) bit3

noncomputable def highFiberState4 (firstBlack : Fin 11) (firstBit : Bool)
    (black1 : Fin 11) (bit1 : Bool)
    (black2 : Fin 11) (bit2 : Bool)
    (black3 : Fin 11) (bit3 : Bool)
    (black4 : Fin 11) (bit4 : Bool) : Finset TenElevenSecret :=
  checkedBranch
    (highFiberState3 firstBlack firstBit black1 bit1 black2 bit2
      black3 bit3)
    (probeGuess 7) black4 (8, 8) bit4

@[simp] theorem mem_highFiberState4
    (firstBlack : Fin 11) (firstBit : Bool)
    (black1 : Fin 11) (bit1 : Bool)
    (black2 : Fin 11) (bit2 : Bool)
    (black3 : Fin 11) (bit3 : Bool)
    (black4 : Fin 11) (bit4 : Bool)
    (secret : TenElevenSecret) :
    secret ∈ highFiberState4 firstBlack firstBit black1 bit1
        black2 bit2 black3 bit3 black4 bit4 ↔
      tenElevenBlackAnswer canonicalFirstGuess secret = firstBlack ∧
      decide (secret 0 = (0 : Fin 11)) = firstBit ∧
      tenElevenBlackAnswer (probeGuess 1) secret = black1 ∧
      decide (secret 2 = (2 : Fin 11)) = bit1 ∧
      tenElevenBlackAnswer (probeGuess 3) secret = black2 ∧
      decide (secret 4 = (4 : Fin 11)) = bit2 ∧
      tenElevenBlackAnswer (probeGuess 5) secret = black3 ∧
      decide (secret 6 = (6 : Fin 11)) = bit3 ∧
      tenElevenBlackAnswer (probeGuess 7) secret = black4 ∧
      decide (secret 8 = (8 : Fin 11)) = bit4 := by
  simp [highFiberState4, highFiberState3, highFiberState2,
    highFiberState1, highFiberState0, and_assoc]


@[simp] theorem mem_MatchSet_iff (guess secret : TenElevenSecret)
    (position : Fin 10) :
    position ∈ MatchSet guess secret ↔ secret position = guess position := by
  simp [MatchSet]


theorem highFiberState4_common_matchSet
    (firstBlack : Fin 11) (firstBit : Bool)
    (black1 : Fin 11) (bit1 : Bool)
    (black2 : Fin 11) (bit2 : Bool)
    (black3 : Fin 11) (bit3 : Bool)
    (black4 : Fin 11) (bit4 : Bool)
    {first second : TenElevenSecret}
    (firstMem : first ∈ highFiberState4 firstBlack firstBit black1 bit1
      black2 bit2 black3 bit3 black4 bit4)
    (secondMem : second ∈ highFiberState4 firstBlack firstBit black1 bit1
      black2 bit2 black3 bit3 black4 bit4) :
    MatchSet canonicalFirstGuess first =
      MatchSet canonicalFirstGuess second := by
  rw [mem_highFiberState4] at firstMem secondMem
  rcases firstMem with
    ⟨firstCanonical, firstBit0, firstBlack1, firstBit2,
      firstBlack3, firstBit4, firstBlack5, firstBit6,
      firstBlack7, firstBit8⟩
  rcases secondMem with
    ⟨secondCanonical, secondBit0, secondBlack1, secondBit2,
      secondBlack3, secondBit4, secondBlack5, secondBit6,
      secondBlack7, secondBit8⟩
  have canonicalEqual :
      tenElevenBlackAnswer canonicalFirstGuess first =
        tenElevenBlackAnswer canonicalFirstGuess second :=
    firstCanonical.trans secondCanonical.symm
  have cardEqual :
      (MatchSet canonicalFirstGuess first).card =
        (MatchSet canonicalFirstGuess second).card :=
    congrArg Fin.val canonicalEqual
  apply finset_fin_ten_eq_of_card_eq_of_agree_before_last
    (MatchSet canonicalFirstGuess first)
    (MatchSet canonicalFirstGuess second) cardEqual
  intro position hnotLast
  rw [mem_MatchSet_iff, mem_MatchSet_iff]
  simp only [canonicalFirstGuess_apply]
  fin_cases position
  · change (first 0 = (0 : Fin 11) ↔ second 0 = (0 : Fin 11))
    exact iff_of_decide_eq_same_bool firstBit0 secondBit0
  · change (first 1 = (1 : Fin 11) ↔ second 1 = (1 : Fin 11))
    exact probe_black_determines_canonical_match first second 1
      canonicalEqual (firstBlack1.trans secondBlack1.symm)
  · change (first 2 = (2 : Fin 11) ↔ second 2 = (2 : Fin 11))
    exact iff_of_decide_eq_same_bool firstBit2 secondBit2
  · change (first 3 = (3 : Fin 11) ↔ second 3 = (3 : Fin 11))
    exact probe_black_determines_canonical_match first second 3
      canonicalEqual (firstBlack3.trans secondBlack3.symm)
  · change (first 4 = (4 : Fin 11) ↔ second 4 = (4 : Fin 11))
    exact iff_of_decide_eq_same_bool firstBit4 secondBit4
  · change (first 5 = (5 : Fin 11) ↔ second 5 = (5 : Fin 11))
    exact probe_black_determines_canonical_match first second 5
      canonicalEqual (firstBlack5.trans secondBlack5.symm)
  · change (first 6 = (6 : Fin 11) ↔ second 6 = (6 : Fin 11))
    exact iff_of_decide_eq_same_bool firstBit6 secondBit6
  · change (first 7 = (7 : Fin 11) ↔ second 7 = (7 : Fin 11))
    exact probe_black_determines_canonical_match first second 7
      canonicalEqual (firstBlack7.trans secondBlack7.symm)
  · change (first 8 = (8 : Fin 11) ↔ second 8 = (8 : Fin 11))
    exact iff_of_decide_eq_same_bool firstBit8 secondBit8
  · exact (hnotLast rfl).elim

theorem highFiberState4_sep_five
    (firstBlack : Fin 11) (firstBit : Bool)
    (black1 : Fin 11) (bit1 : Bool)
    (black2 : Fin 11) (bit2 : Bool)
    (black3 : Fin 11) (bit3 : Bool)
    (black4 : Fin 11) (bit4 : Bool)
    (highAnswer : 5 ≤ firstBlack.val) :
    Sep 5 (highFiberState4 firstBlack firstBit black1 bit1
      black2 bit2 black3 bit3 black4 bit4) := by
  classical
  let candidates := highFiberState4 firstBlack firstBit black1 bit1
    black2 bit2 black3 bit3 black4 bit4
  change Sep 5 candidates
  by_cases emptyCandidates : candidates = ∅
  · rw [emptyCandidates]
    exact Sep.empty 5
  · obtain ⟨anchor, anchorMem⟩ :=
      Finset.nonempty_iff_ne_empty.mpr emptyCandidates
    apply sep_five_of_common_matchSet candidates
      (MatchSet canonicalFirstGuess anchor)
    · have anchorCanonical :=
        (mem_highFiberState4 firstBlack firstBit black1 bit1
          black2 bit2 black3 bit3 black4 bit4 anchor).1 anchorMem |>.1
      have cardEqual := congrArg Fin.val anchorCanonical
      change (MatchSet canonicalFirstGuess anchor).card =
        firstBlack.val at cardEqual
      omega
    · intro secret secretMem
      exact highFiberState4_common_matchSet firstBlack firstBit
        black1 bit1 black2 bit2 black3 bit3 black4 bit4 secretMem anchorMem
 

theorem highFiberState3_sep_six
    (firstBlack : Fin 11) (firstBit : Bool)
    (black1 : Fin 11) (bit1 : Bool)
    (black2 : Fin 11) (bit2 : Bool)
    (black3 : Fin 11) (bit3 : Bool)
    (highAnswer : 5 ≤ firstBlack.val) :
    Sep 6 (highFiberState3 firstBlack firstBit black1 bit1
      black2 bit2 black3 bit3) := by
  rw [sep_succ_iff]
  refine ⟨probeGuess 7, ?_⟩
  intro black4
  refine ⟨(8, 8), ?_, ?_⟩
  · exact highFiberState4_sep_five firstBlack firstBit
      black1 bit1 black2 bit2 black3 bit3 black4 true highAnswer
  · exact highFiberState4_sep_five firstBlack firstBit
      black1 bit1 black2 bit2 black3 bit3 black4 false highAnswer

theorem highFiberState2_sep_seven
    (firstBlack : Fin 11) (firstBit : Bool)
    (black1 : Fin 11) (bit1 : Bool)
    (black2 : Fin 11) (bit2 : Bool)
    (highAnswer : 5 ≤ firstBlack.val) :
    Sep 7 (highFiberState2 firstBlack firstBit black1 bit1
      black2 bit2) := by
  rw [sep_succ_iff]
  refine ⟨probeGuess 5, ?_⟩
  intro black3
  refine ⟨(6, 6), ?_, ?_⟩
  · exact highFiberState3_sep_six firstBlack firstBit
      black1 bit1 black2 bit2 black3 true highAnswer
  · exact highFiberState3_sep_six firstBlack firstBit
      black1 bit1 black2 bit2 black3 false highAnswer

theorem highFiberState1_sep_eight
    (firstBlack : Fin 11) (firstBit : Bool)
    (black1 : Fin 11) (bit1 : Bool)
    (highAnswer : 5 ≤ firstBlack.val) :
    Sep 8 (highFiberState1 firstBlack firstBit black1 bit1) := by
  rw [sep_succ_iff]
  refine ⟨probeGuess 3, ?_⟩
  intro black2
  refine ⟨(4, 4), ?_, ?_⟩
  · exact highFiberState2_sep_seven firstBlack firstBit
      black1 bit1 black2 true highAnswer
  · exact highFiberState2_sep_seven firstBlack firstBit
      black1 bit1 black2 false highAnswer

theorem highFiberState0_sep_nine
    (firstBlack : Fin 11) (firstBit : Bool)
    (highAnswer : 5 ≤ firstBlack.val) :
    Sep 9 (highFiberState0 firstBlack firstBit) := by
  rw [sep_succ_iff]
  refine ⟨probeGuess 1, ?_⟩
  intro black1
  refine ⟨(2, 2), ?_, ?_⟩
  · exact highFiberState1_sep_eight firstBlack firstBit
      black1 true highAnswer
  · exact highFiberState1_sep_eight firstBlack firstBit
      black1 false highAnswer

/--
After the canonical first black answer is at least five, one adaptive equality
check after that answer and nine further legal rounds suffice. Thus the round
count, including the canonical first query, is at most ten.
-/
theorem canonical_first_answer_ge_five_total_ten
    (firstBlack : Fin 11) (highAnswer : 5 ≤ firstBlack.val) :
    ∃ edge : Fin 10 × Fin 11,
      Sep 9 (checkedBranch (Finset.univ : Finset TenElevenSecret)
        canonicalFirstGuess firstBlack edge true) ∧
      Sep 9 (checkedBranch (Finset.univ : Finset TenElevenSecret)
        canonicalFirstGuess firstBlack edge false) := by
  refine ⟨(0, 0), ?_, ?_⟩
  · exact highFiberState0_sep_nine firstBlack true highAnswer
  · exact highFiberState0_sep_nine firstBlack false highAnswer

end BlackPegExtraCheck
