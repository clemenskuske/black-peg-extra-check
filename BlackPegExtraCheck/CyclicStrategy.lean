/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.Separator
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin

/-!
# The ten-round cyclic transcript

This file formalizes the part of the proposed fifteen-round protocol that is
independent of the open eight-rook endgame.  The ten legal cyclic guesses are
the restrictions of the eleven translations of `Fin 11`.  Their black counts
sum to ten, so the ten queried counts determine the unqueried eleventh count.
The ten accompanying equality questions test the first field against colors
`0, ..., 9`; their Boolean transcript determines that field even when all ten
answers are false.

The definitions at the end isolate the exact remaining claim as `Sep 3` on
every cylindrical fiber with two fixed fields.  No separator witness is
assumed or constructed in this file.
-/

namespace BlackPegExtraCheck

open scoped BigOperators

/-! ## Cyclic guesses and their complete profile -/

/-- The cyclic query `i ↦ i + shift (mod 11)`, restricted to ten fields. -/
def tenElevenCyclicGuess (shift : Fin 11) : TenElevenSecret where
  toFun i := finCycle shift i.castSucc
  inj' := (finCycle shift).injective.comp (Fin.castSucc_injective 10)

@[simp] theorem tenElevenCyclicGuess_apply (shift : Fin 11) (i : Fin 10) :
    tenElevenCyclicGuess shift i = finCycle shift i.castSucc := rfl

/-- Every field matches exactly one of the eleven cyclic queries. -/
theorem unique_cyclic_shift_sum (i : Fin 10) (color : Fin 11) :
    (∑ shift : Fin 11,
      if tenElevenCyclicGuess shift i = color then (1 : Nat) else 0) = 1 := by
  let target : Fin 11 := (finCycle i.castSucc).symm color
  rw [Finset.sum_eq_single target]
  · change (if finCycle target i.castSucc = color then 1 else 0) = 1
    have commute : finCycle target i.castSucc = finCycle i.castSucc target := by
      simp [finCycle_apply, add_comm]
    rw [commute]
    simp [target]
  · intro shift _ shift_ne
    by_cases hmatch : tenElevenCyclicGuess shift i = color
    · exfalso
      apply shift_ne
      apply (finCycle i.castSucc).injective
      have left : finCycle i.castSucc shift = color := by
        simp only [finCycle_apply]
        change finCycle shift i.castSucc = color at hmatch
        simpa only [finCycle_apply, add_comm] using hmatch
      exact left.trans (by simp [target])
    · exact if_neg hmatch
  · simp

/-- The eleven cyclic black counts have total mass ten. -/
theorem sum_tenElevenCyclicBlackAnswer (secret : TenElevenSecret) :
    (∑ shift : Fin 11,
      (tenElevenBlackAnswer (tenElevenCyclicGuess shift) secret).val) = 10 := by
  change (∑ shift : Fin 11,
    (MatchSet (tenElevenCyclicGuess shift) secret).card) = 10
  calc
    (∑ shift : Fin 11, (MatchSet (tenElevenCyclicGuess shift) secret).card) =
        ∑ shift : Fin 11, ∑ i : Fin 10,
          if secret i = tenElevenCyclicGuess shift i then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro shift _
            simp [MatchSet]
    _ = ∑ i : Fin 10, ∑ shift : Fin 11,
          if secret i = tenElevenCyclicGuess shift i then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ _i : Fin 10, 1 := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [eq_comm] using unique_cyclic_shift_sum i (secret i)
    _ = 10 := by simp

/-- Equality of the first ten cyclic counts forces equality of the last one. -/
theorem cyclicProfile_eq_of_first_ten
    {first second : TenElevenSecret}
    (equal_first_ten : ∀ shift : Fin 10,
      tenElevenBlackAnswer (tenElevenCyclicGuess shift.castSucc) first =
        tenElevenBlackAnswer (tenElevenCyclicGuess shift.castSucc) second) :
    ∀ shift : Fin 11,
      tenElevenBlackAnswer (tenElevenCyclicGuess shift) first =
        tenElevenBlackAnswer (tenElevenCyclicGuess shift) second := by
  have prefix_equal :
      (∑ shift : Fin 10,
        (tenElevenBlackAnswer (tenElevenCyclicGuess shift.castSucc) first).val) =
      ∑ shift : Fin 10,
        (tenElevenBlackAnswer (tenElevenCyclicGuess shift.castSucc) second).val := by
    apply Finset.sum_congr rfl
    intro shift _
    exact congrArg Fin.val (equal_first_ten shift)
  have first_sum := sum_tenElevenCyclicBlackAnswer first
  have second_sum := sum_tenElevenCyclicBlackAnswer second
  rw [Fin.sum_univ_castSucc] at first_sum second_sum
  intro shift
  induction shift using Fin.lastCases with
  | last =>
      apply Fin.ext
      omega
  | cast shift => exact equal_first_ten shift

/-! ## The ten equality bits -/

/-- Tests against colors `0, ..., 9` determine a value in `Fin 11`. -/
theorem value_eq_of_first_ten_checks
    {first second : Fin 11}
    (checks : ∀ color : Fin 10,
      decide (first = color.castSucc) = decide (second = color.castSucc)) :
    first = second := by
  induction first using Fin.lastCases with
  | cast color =>
      have same := checks color
      have second_true : decide (second = color.castSucc) = true := by
        calc
          decide (second = color.castSucc) =
              decide (color.castSucc = color.castSucc) := same.symm
          _ = true := by simp
      exact (of_decide_eq_true second_true).symm
  | last =>
      induction second using Fin.lastCases with
      | last => rfl
      | cast color =>
          have same := checks color
          have last_ne : (Fin.last 10 : Fin 11) ≠ color.castSucc := by
            intro equal
            have values := congrArg Fin.val equal
            change 10 = color.val at values
            omega
          have left_false :
              decide ((Fin.last 10 : Fin 11) = color.castSucc) = false := by
            exact decide_eq_false_iff_not.mpr last_ne
          have right_true : decide (color.castSucc = color.castSucc) = true := by
            simp
          rw [left_false, right_true] at same
          exact Bool.noConfusion same

/-- Two secrets have the same complete ten-round cyclic setup transcript. -/
def CyclicSetupEquivalent (first second : TenElevenSecret) : Prop :=
  (∀ shift : Fin 10,
    tenElevenBlackAnswer (tenElevenCyclicGuess shift.castSucc) first =
      tenElevenBlackAnswer (tenElevenCyclicGuess shift.castSucc) second) ∧
  ∀ color : Fin 10,
    decide (first 0 = color.castSucc) = decide (second 0 = color.castSucc)

/-- A complete setup transcript fixes field zero and the full cyclic X-ray. -/
theorem CyclicSetupEquivalent.fixed_zero_and_profile
    {first second : TenElevenSecret}
    (equivalent : CyclicSetupEquivalent first second) :
    first 0 = second 0 ∧
      ∀ shift : Fin 11,
        tenElevenBlackAnswer (tenElevenCyclicGuess shift) first =
          tenElevenBlackAnswer (tenElevenCyclicGuess shift) second := by
  exact ⟨value_eq_of_first_ten_checks equivalent.2,
    cyclicProfile_eq_of_first_ten equivalent.1⟩

/-- The exact candidate fiber associated with one cyclic setup transcript. -/
noncomputable def CyclicSetupFiber (anchor : TenElevenSecret) :
    Finset TenElevenSecret := by
  classical
  exact Finset.univ.filter fun secret => CyclicSetupEquivalent anchor secret

@[simp] theorem mem_cyclicSetupFiber (anchor secret : TenElevenSecret) :
    secret ∈ CyclicSetupFiber anchor ↔ CyclicSetupEquivalent anchor secret := by
  simp [CyclicSetupFiber]

/-! ## Exact composition of the ten fixed setup rounds -/

/-- Pairwise agreement on the first `tested` setup responses. -/
def CyclicSetupConsistent (tested : Nat)
    (candidates : Finset TenElevenSecret) : Prop :=
  ∀ first ∈ candidates, ∀ second ∈ candidates, ∀ index : Fin 10,
    index.val < tested →
      tenElevenBlackAnswer (tenElevenCyclicGuess index.castSucc) first =
          tenElevenBlackAnswer (tenElevenCyclicGuess index.castSucc) second ∧
        decide (first 0 = index.castSucc) =
          decide (second 0 = index.castSucc)

theorem cyclicSetupConsistent_zero (candidates : Finset TenElevenSecret) :
    CyclicSetupConsistent 0 candidates := by
  intro _ _ _ _ index index_lt
  omega

theorem cyclicSetupConsistent_succ_branch
    {tested : Nat} (tested_lt : tested < 10)
    {candidates : Finset TenElevenSecret}
    (consistent : CyclicSetupConsistent tested candidates)
    (black : Fin 11) (bit : Bool) :
    CyclicSetupConsistent (tested + 1)
      (checkedBranch candidates
        (tenElevenCyclicGuess (⟨tested, by omega⟩ : Fin 10).castSucc)
        black (0, (⟨tested, by omega⟩ : Fin 10).castSucc) bit) := by
  let current : Fin 10 := ⟨tested, tested_lt⟩
  intro first first_mem second second_mem index index_lt
  rw [mem_checkedBranch] at first_mem second_mem
  by_cases before : index.val < tested
  · exact consistent first first_mem.1 second second_mem.1 index before
  · have at_current : index = current := by
      apply Fin.ext
      dsimp [current]
      omega
    subst index
    exact ⟨first_mem.2.1.trans second_mem.2.1.symm,
      first_mem.2.2.trans second_mem.2.2.symm⟩

set_option maxHeartbeats 800000 in
-- The ten nested `Sep` constructors otherwise exceed the default elaboration budget.
/--
Ten fixed cyclic rounds compose with any five-round solver for every exact
setup fiber.  This is a genuine strategy-composition theorem; its premise is
about the residual candidate states, not a numerical upper bound.
-/
theorem sep_fifteen_of_setupFibers_sep_five
    (finish : ∀ anchor : TenElevenSecret, Sep 5 (CyclicSetupFiber anchor)) :
    Sep 15 (Finset.univ : Finset TenElevenSecret) := by
  have auxiliary : ∀ remaining tested : Nat,
      tested + remaining = 10 →
      ∀ candidates : Finset TenElevenSecret,
        CyclicSetupConsistent tested candidates →
          Sep (remaining + 5) candidates := by
    intro remaining
    induction remaining with
    | zero =>
        intro tested total candidates consistent
        have tested_eq : tested = 10 := by omega
        subst tested
        by_cases nonempty : candidates.Nonempty
        · obtain ⟨anchor, anchor_mem⟩ := nonempty
          apply Sep.mono (larger := CyclicSetupFiber anchor) ?_ (finish anchor)
          intro secret secret_mem
          rw [mem_cyclicSetupFiber]
          constructor
          · intro index
            exact (consistent anchor anchor_mem secret secret_mem index (by omega)).1
          · intro index
            exact (consistent anchor anchor_mem secret secret_mem index (by omega)).2
        · have empty : candidates = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
          subst candidates
          exact Sep.mono (Finset.empty_subset _) (finish (tenElevenCyclicGuess 0))
    | succ remaining induction_hypothesis =>
        intro tested total candidates consistent
        have tested_lt : tested < 10 := by omega
        have next_total : tested + 1 + remaining = 10 := by omega
        have depth_eq : Nat.succ remaining + 5 = (remaining + 5) + 1 := by omega
        rw [depth_eq, sep_succ_iff]
        let current : Fin 10 := ⟨tested, tested_lt⟩
        refine ⟨tenElevenCyclicGuess current.castSucc, ?_⟩
        intro black
        refine ⟨(0, current.castSucc), ?_, ?_⟩
        · exact induction_hypothesis (tested + 1) next_total _
            (cyclicSetupConsistent_succ_branch tested_lt consistent black true)
        · exact induction_hypothesis (tested + 1) next_total _
            (cyclicSetupConsistent_succ_branch tested_lt consistent black false)
  have result := auxiliary 10 0 (by omega)
    (Finset.univ : Finset TenElevenSecret) (cyclicSetupConsistent_zero _)
  exact result

/-! ## Exact cylindrical endgame statement -/

/--
Secrets agreeing with `anchor` on `fixed` fields and having the same complete
cyclic diagonal profile.  When `fixed.card = 2`, the unfixed part is the
eight-rook cylindrical X-ray state needed by the proposed endgame.
-/
noncomputable def CylindricalFiber (anchor : TenElevenSecret)
    (fixed : Finset (Fin 10)) : Finset TenElevenSecret :=
  Finset.univ.filter fun secret =>
    (∀ position ∈ fixed, secret position = anchor position) ∧
      ∀ shift : Fin 11,
        tenElevenBlackAnswer (tenElevenCyclicGuess shift) secret =
          tenElevenBlackAnswer (tenElevenCyclicGuess shift) anchor

@[simp] theorem mem_cylindricalFiber (anchor secret : TenElevenSecret)
    (fixed : Finset (Fin 10)) :
    secret ∈ CylindricalFiber anchor fixed ↔
      (∀ position ∈ fixed, secret position = anchor position) ∧
        ∀ shift : Fin 11,
          tenElevenBlackAnswer (tenElevenCyclicGuess shift) secret =
            tenElevenBlackAnswer (tenElevenCyclicGuess shift) anchor := by
  simp [CylindricalFiber]

/-- The precise universal statement still required for the three-round endgame. -/
def EightRookCylindricalSepThree : Prop :=
  ∀ (anchor : TenElevenSecret) (fixed : Finset (Fin 10)),
    fixed.card = 2 → Sep 3 (CylindricalFiber anchor fixed)

/-- Every exact setup fiber lies in its one-fixed-field cylindrical fiber. -/
theorem cyclicSetupFiber_subset_cylindricalFiber_zero
    (anchor : TenElevenSecret) :
    CyclicSetupFiber anchor ⊆ CylindricalFiber anchor {0} := by
  intro secret secret_mem
  rw [mem_cyclicSetupFiber] at secret_mem
  rw [mem_cylindricalFiber]
  have reconstructed := secret_mem.fixed_zero_and_profile
  constructor
  · intro position position_mem
    have position_eq : position = 0 := by simpa using position_mem
    subst position
    exact reconstructed.1.symm
  · intro shift
    exact (reconstructed.2 shift).symm

/-! ## Structural inputs for the equality-accelerated search -/

/-- Matches of one cyclic query outside the setup-fixed field zero. -/
def OpenCyclicMatchSet (shift : Fin 11) (secret : TenElevenSecret) :
    Finset (Fin 10) :=
  (Finset.univ.erase 0).filter fun position =>
    secret position = tenElevenCyclicGuess shift position

@[simp] theorem mem_openCyclicMatchSet (shift : Fin 11)
    (secret : TenElevenSecret) (position : Fin 10) :
    position ∈ OpenCyclicMatchSet shift secret ↔
      position ≠ 0 ∧
        secret position = tenElevenCyclicGuess shift position := by
  simp [OpenCyclicMatchSet]

/-- The residual cyclic profile has total mass nine after fixing field zero. -/
theorem sum_card_openCyclicMatchSet (secret : TenElevenSecret) :
    (∑ shift : Fin 11, (OpenCyclicMatchSet shift secret).card) = 9 := by
  calc
    (∑ shift : Fin 11, (OpenCyclicMatchSet shift secret).card) =
        ∑ shift : Fin 11, ∑ position ∈ (Finset.univ.erase (0 : Fin 10)),
          if secret position = tenElevenCyclicGuess shift position then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro shift _
            rw [OpenCyclicMatchSet, Finset.card_filter]
    _ = ∑ position ∈ (Finset.univ.erase (0 : Fin 10)), ∑ shift : Fin 11,
          if secret position = tenElevenCyclicGuess shift position then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _position ∈ (Finset.univ.erase (0 : Fin 10)), 1 := by
      apply Finset.sum_congr rfl
      intro position _
      simpa only [eq_comm] using unique_cyclic_shift_sum position (secret position)
    _ = 9 := by simp

/-- A nonempty proper subset of the eleven-cycle has a directed boundary. -/
theorem finEleven_cycle_boundary :
    ∀ support : Finset (Fin 11), support.Nonempty → support ≠ Finset.univ →
      ∃ shift ∈ support, finRotate 11 shift ∉ support := by
  intro support support_nonempty support_proper
  by_contra no_boundary
  push Not at no_boundary
  obtain ⟨start, start_mem⟩ := support_nonempty
  have orbit_mem : ∀ n : Nat, (finRotate 11)^[n] start ∈ support := by
    intro n
    induction n with
    | zero => simpa using start_mem
    | succ n ih =>
        simpa [Function.iterate_succ_apply'] using
          no_boundary ((finRotate 11)^[n] start) ih
  apply support_proper
  apply Finset.eq_univ_of_forall
  intro target
  let delta : Fin 11 := target - start
  have reached : finCycle delta start ∈ support := by
    rw [finCycle_eq_finRotate_iterate]
    exact orbit_mem delta.val
  simpa [delta, finCycle_apply] using reached

/--
Some residual cyclic class is nonempty and is followed by an empty class.
This is the exact active-index fact used by `findNext`; it follows from total
mass nine rather than from an unformalized appeal to averaging.
-/
theorem exists_active_cyclic_shift (secret : TenElevenSecret) :
    ∃ active : Fin 11,
      (OpenCyclicMatchSet active secret).Nonempty ∧
        OpenCyclicMatchSet (finRotate 11 active) secret = ∅ := by
  let support : Finset (Fin 11) :=
    Finset.univ.filter fun shift => (OpenCyclicMatchSet shift secret).Nonempty
  have support_nonempty : support.Nonempty := by
    by_contra empty_support
    have support_eq : support = ∅ := Finset.not_nonempty_iff_eq_empty.mp empty_support
    have every_empty : ∀ shift : Fin 11,
        OpenCyclicMatchSet shift secret = ∅ := by
      intro shift
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro nonempty
      have : shift ∈ support := by simp [support, nonempty]
      rw [support_eq] at this
      simp at this
    have total := sum_card_openCyclicMatchSet secret
    simp [every_empty] at total
  have support_proper : support ≠ Finset.univ := by
    intro support_eq
    have every_positive : ∀ shift : Fin 11,
        1 ≤ (OpenCyclicMatchSet shift secret).card := by
      intro shift
      have shift_mem : shift ∈ support := by rw [support_eq]; simp
      have nonempty : (OpenCyclicMatchSet shift secret).Nonempty := by
        simpa [support] using shift_mem
      exact Finset.one_le_card.mpr nonempty
    have eleven_le : 11 ≤ ∑ shift : Fin 11,
        (OpenCyclicMatchSet shift secret).card := by
      calc
        11 = ∑ _shift : Fin 11, 1 := by simp
        _ ≤ ∑ shift : Fin 11, (OpenCyclicMatchSet shift secret).card := by
          exact Finset.sum_le_sum fun shift _ => every_positive shift
    rw [sum_card_openCyclicMatchSet] at eleven_le
    omega
  obtain ⟨active, active_mem, next_not_mem⟩ :=
    finEleven_cycle_boundary support support_nonempty support_proper
  refine ⟨active, ?_, ?_⟩
  · simpa [support] using active_mem
  · apply Finset.not_nonempty_iff_eq_empty.mp
    intro next_nonempty
    apply next_not_mem
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, next_nonempty⟩

/-- The legal mixed query used at a cut in the accelerated cyclic search. -/
def mixedCyclicGuess (active cut : Fin 11) : TenElevenSecret :=
  cut.succAboveEmb.trans (finCycle active).toEmbedding

@[simp] theorem mixedCyclicGuess_apply (active cut : Fin 11)
    (position : Fin 10) :
    mixedCyclicGuess active cut position =
      finCycle active (cut.succAbove position) := rfl

theorem mixedCyclicGuess_apply_left (active cut : Fin 11)
    (position : Fin 10) (left : position.castSucc < cut) :
    mixedCyclicGuess active cut position =
      tenElevenCyclicGuess active position := by
  simp [mixedCyclicGuess, Fin.succAbove_of_castSucc_lt cut position left]

theorem mixedCyclicGuess_apply_right (active cut : Fin 11)
    (position : Fin 10) (right : cut ≤ position.castSucc) :
    mixedCyclicGuess active cut position =
      tenElevenCyclicGuess (finRotate 11 active) position := by
  rw [mixedCyclicGuess_apply, Fin.succAbove_of_le_castSucc cut position right]
  simp only [tenElevenCyclicGuess_apply, finRotate_apply, finCycle_apply]
  have value_lt : position.val + 1 < 11 := by omega
  have succ_eq : (position.succ : Fin 11) = position.castSucc + 1 := by
    apply Fin.ext
    simp [Fin.add_def, Nat.mod_eq_of_lt value_lt]
  rw [succ_eq]
  ac_rfl

/-- Matches of an arbitrary legal query outside field zero. -/
def OpenGuessMatchSet (guess secret : TenElevenSecret) : Finset (Fin 10) :=
  (Finset.univ.erase 0).filter fun position => secret position = guess position

@[simp] theorem mem_openGuessMatchSet (guess secret : TenElevenSecret)
    (position : Fin 10) :
    position ∈ OpenGuessMatchSet guess secret ↔
      position ≠ 0 ∧ secret position = guess position := by
  simp [OpenGuessMatchSet]

theorem openGuessMatchSet_eq_erase_matchSet (guess secret : TenElevenSecret) :
    OpenGuessMatchSet guess secret = (MatchSet guess secret).erase 0 := by
  ext position
  simp [OpenGuessMatchSet, MatchSet]

theorem openCyclicMatchSet_eq_openGuessMatchSet (shift : Fin 11)
    (secret : TenElevenSecret) :
    OpenCyclicMatchSet shift secret =
      OpenGuessMatchSet (tenElevenCyclicGuess shift) secret := rfl

/-- Equal black responses and an equal value at field zero give equal open counts. -/
theorem card_openGuessMatchSet_eq_of_black_eq_of_zero_eq
    (guess first second : TenElevenSecret)
    (black_eq : tenElevenBlackAnswer guess first =
      tenElevenBlackAnswer guess second)
    (zero_eq : first 0 = second 0) :
    (OpenGuessMatchSet guess first).card =
      (OpenGuessMatchSet guess second).card := by
  rw [openGuessMatchSet_eq_erase_matchSet,
    openGuessMatchSet_eq_erase_matchSet]
  have card_eq : (MatchSet guess first).card = (MatchSet guess second).card :=
    congrArg Fin.val black_eq
  have zero_mem_eq : 0 ∈ MatchSet guess first ↔ 0 ∈ MatchSet guess second := by
    simp [MatchSet, zero_eq]
  by_cases first_matches : 0 ∈ MatchSet guess first
  · have second_matches := zero_mem_eq.mp first_matches
    rw [Finset.card_erase_of_mem first_matches,
      Finset.card_erase_of_mem second_matches, card_eq]
  · have second_misses : 0 ∉ MatchSet guess second := by
      simpa [zero_mem_eq] using first_matches
    rw [Finset.erase_eq_of_notMem first_matches,
      Finset.erase_eq_of_notMem second_misses, card_eq]

/-- Cylindrical-fiber membership preserves every residual cyclic count. -/
theorem card_openCyclicMatchSet_eq_of_mem_cylindricalFiber_zero
    {anchor secret : TenElevenSecret}
    (member : secret ∈ CylindricalFiber anchor {0}) (shift : Fin 11) :
    (OpenCyclicMatchSet shift secret).card =
      (OpenCyclicMatchSet shift anchor).card := by
  rw [mem_cylindricalFiber] at member
  rw [openCyclicMatchSet_eq_openGuessMatchSet,
    openCyclicMatchSet_eq_openGuessMatchSet]
  apply card_openGuessMatchSet_eq_of_black_eq_of_zero_eq
  · exact member.2 shift
  · exact member.1 0 (by simp)

/-- The mixed query sees exactly the active matches to the left of its cut. -/
theorem openGuessMatchSet_mixed_eq_left
    (active cut : Fin 11) (secret : TenElevenSecret)
    (next_empty : OpenCyclicMatchSet (finRotate 11 active) secret = ∅) :
    OpenGuessMatchSet (mixedCyclicGuess active cut) secret =
      (OpenCyclicMatchSet active secret).filter fun position =>
        position.castSucc < cut := by
  ext position
  by_cases left : position.castSucc < cut
  · simp [left, mixedCyclicGuess_apply_left active cut position left]
  · have right : cut ≤ position.castSucc := by omega
    rw [mem_openGuessMatchSet]
    simp only [Finset.mem_filter, mem_openCyclicMatchSet, left, and_false,
      iff_false]
    intro properties
    have next_match :
        secret position = tenElevenCyclicGuess (finRotate 11 active) position := by
      rw [← mixedCyclicGuess_apply_right active cut position right]
      exact properties.2
    have member : position ∈ OpenCyclicMatchSet (finRotate 11 active) secret :=
      (mem_openCyclicMatchSet _ _ _).2 ⟨properties.1, next_match⟩
    rw [next_empty] at member
    simp at member

/-- The median of a nonempty field set gives exact left and right cardinalities. -/
theorem finTen_median_partition (possible : Finset (Fin 10))
    (possible_nonempty : possible.Nonempty) :
    ∃ pivot ∈ possible,
      (possible.filter fun position => position < pivot).card =
          possible.card / 2 ∧
        (possible.filter fun position => pivot ≤ position).card =
          possible.card - possible.card / 2 := by
  have card_pos : 0 < possible.card := Finset.card_pos.mpr possible_nonempty
  let middle : Fin possible.card :=
    ⟨possible.card / 2, Nat.div_lt_self card_pos (by omega)⟩
  let enumeration : Fin possible.card ↪o Fin 10 :=
    possible.orderEmbOfFin rfl
  let pivot : Fin 10 := enumeration middle
  have pivot_mem : pivot ∈ possible := by
    exact Finset.orderEmbOfFin_mem possible rfl middle
  refine ⟨pivot, pivot_mem, ?_, ?_⟩
  · have set_eq :
        possible.filter (fun position => position < pivot) =
          (Finset.Iio middle).map enumeration.toEmbedding := by
      ext position
      constructor
      · intro position_mem
        have properties := Finset.mem_filter.mp position_mem
        let index : Fin possible.card :=
          (possible.orderIsoOfFin rfl).symm ⟨position, properties.1⟩
        have index_value : enumeration index = position := by
          dsimp [enumeration]
          change ↑(possible.orderIsoOfFin rfl index) = position
          simp [index]
        apply Finset.mem_map.mpr
        refine ⟨index, ?_, index_value⟩
        simp only [Finset.mem_Iio]
        apply enumeration.lt_iff_lt.mp
        simpa [index_value, pivot] using properties.2
      · intro position_mem
        obtain ⟨index, index_lt, index_eq⟩ := Finset.mem_map.mp position_mem
        have index_lt_middle : index < middle := by simpa using index_lt
        apply Finset.mem_filter.mpr
        refine ⟨?_, ?_⟩
        · rw [← index_eq]
          exact Finset.orderEmbOfFin_mem possible rfl index
        · rw [← index_eq]
          exact enumeration.strictMono index_lt_middle
    rw [set_eq, Finset.card_map, Fin.card_Iio]
  · have set_eq :
        possible.filter (fun position => pivot ≤ position) =
          (Finset.Ici middle).map enumeration.toEmbedding := by
      ext position
      constructor
      · intro position_mem
        have properties := Finset.mem_filter.mp position_mem
        let index : Fin possible.card :=
          (possible.orderIsoOfFin rfl).symm ⟨position, properties.1⟩
        have index_value : enumeration index = position := by
          dsimp [enumeration]
          change ↑(possible.orderIsoOfFin rfl index) = position
          simp [index]
        apply Finset.mem_map.mpr
        refine ⟨index, ?_, index_value⟩
        simp only [Finset.mem_Ici]
        apply enumeration.le_iff_le.mp
        simpa [index_value, pivot] using properties.2
      · intro position_mem
        obtain ⟨index, middle_le, index_eq⟩ := Finset.mem_map.mp position_mem
        have middle_le_index : middle ≤ index := by simpa using middle_le
        apply Finset.mem_filter.mpr
        refine ⟨?_, ?_⟩
        · rw [← index_eq]
          exact Finset.orderEmbOfFin_mem possible rfl index
        · rw [← index_eq]
          exact enumeration.monotone middle_le_index
    rw [set_eq, Finset.card_map, Fin.card_Ici]

/-- A median cut can be chosen inside any current search window. -/
theorem finTen_balanced_window_cut :
    ∀ (possible : Finset (Fin 10)) (low high : Fin 11),
      (low ≤ high ∧ ∀ position ∈ possible,
        low ≤ position.castSucc ∧ position.castSucc < high) →
      ∃ cut : Fin 11,
        low ≤ cut ∧ cut ≤ high ∧
          (possible.filter fun position => position.castSucc < cut).card ≤
              (possible.card + 1) / 2 ∧
            (possible.filter fun position => cut ≤ position.castSucc).card ≤
              (possible.card + 1) / 2 := by
  intro possible low high window
  by_cases possible_nonempty : possible.Nonempty
  · obtain ⟨pivot, pivot_mem, left_card, right_card⟩ :=
      finTen_median_partition possible possible_nonempty
    let cut : Fin 11 := pivot.castSucc
    have pivot_window := window.2 pivot pivot_mem
    refine ⟨cut, pivot_window.1, pivot_window.2.le, ?_, ?_⟩
    · have filter_eq :
          possible.filter (fun position => position.castSucc < cut) =
            possible.filter fun position => position < pivot := by
        ext position
        simp [cut]
      rw [filter_eq, left_card]
      omega
    · have filter_eq :
          possible.filter (fun position => cut ≤ position.castSucc) =
            possible.filter fun position => pivot ≤ position := by
        ext position
        simp [cut]
      rw [filter_eq, right_card]
      omega
  · have possible_empty : possible = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp possible_nonempty
    refine ⟨low, le_rfl, window.1, ?_, ?_⟩ <;> simp [possible_empty]

/--
Invariant for a binary search for an open match of `active`.  There are no
active matches below `low`; every active match in `[low, high)` is still in
`possible`; and at least one such match exists.  Active matches above `high`
are harmless because the mixed query uses the zero-response cyclic query
there.
-/
def CyclicSearchInvariant (anchor : TenElevenSecret) (active : Fin 11)
    (low high : Fin 11) (possible : Finset (Fin 10))
    (candidates : Finset TenElevenSecret) : Prop :=
  candidates ⊆ CylindricalFiber anchor {0} ∧
    (∀ position ∈ possible,
      low ≤ position.castSucc ∧ position.castSucc < high) ∧
    ∀ secret ∈ candidates,
      (∀ position ∈ OpenCyclicMatchSet active secret,
        position.castSucc < low → False) ∧
      (∀ position ∈ OpenCyclicMatchSet active secret,
        low ≤ position.castSucc → position.castSucc < high →
          position ∈ possible) ∧
      ∃ position ∈ OpenCyclicMatchSet active secret,
        low ≤ position.castSucc ∧ position.castSucc < high

theorem initial_cyclicSearchInvariant (anchor : TenElevenSecret)
    (active : Fin 11)
    (active_nonempty : (OpenCyclicMatchSet active anchor).Nonempty) :
    CyclicSearchInvariant anchor active 0 10
      (Finset.univ.erase 0) (CylindricalFiber anchor {0}) := by
  refine ⟨Finset.Subset.rfl, ?_, ?_⟩
  · intro position position_mem
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at position_mem
    constructor
    · exact Fin.zero_le _
    · exact position.isLt
  · intro secret secret_mem
    have equal_card := card_openCyclicMatchSet_eq_of_mem_cylindricalFiber_zero
      secret_mem active
    have secret_nonempty : (OpenCyclicMatchSet active secret).Nonempty := by
      rw [← Finset.card_pos, equal_card, Finset.card_pos]
      exact active_nonempty
    refine ⟨?_, ?_, ?_⟩
    · intro position position_mem below
      simp at below
    · intro position position_mem _ _
      exact Finset.mem_erase.mpr
        ⟨(mem_openCyclicMatchSet _ _ _).1 position_mem |>.1, Finset.mem_univ _⟩
    · obtain ⟨position, position_mem⟩ := secret_nonempty
      exact ⟨position, position_mem, Fin.zero_le _, position.isLt⟩

theorem next_open_empty_of_mem_cylindricalFiber_zero
    {anchor secret : TenElevenSecret} {active : Fin 11}
    (anchor_empty : OpenCyclicMatchSet (finRotate 11 active) anchor = ∅)
    (member : secret ∈ CylindricalFiber anchor {0}) :
    OpenCyclicMatchSet (finRotate 11 active) secret = ∅ := by
  apply Finset.card_eq_zero.mp
  calc
    (OpenCyclicMatchSet (finRotate 11 active) secret).card =
        (OpenCyclicMatchSet (finRotate 11 active) anchor).card :=
      card_openCyclicMatchSet_eq_of_mem_cylindricalFiber_zero member _
    _ = 0 := congrArg Finset.card anchor_empty

/-- A true active-edge check fixes a second field and enters the open endgame. -/
theorem checkedBranch_true_sep_three_of_eightRook
    (endgame : EightRookCylindricalSepThree)
    {anchor : TenElevenSecret} {active : Fin 11}
    {candidates : Finset TenElevenSecret}
    (contained : candidates ⊆ CylindricalFiber anchor {0})
    (guess : TenElevenSecret) (black : Fin 11) (position : Fin 10)
    (position_ne : position ≠ 0) :
    Sep 3 (checkedBranch candidates guess black
      (position, tenElevenCyclicGuess active position) true) := by
  let branch := checkedBranch candidates guess black
    (position, tenElevenCyclicGuess active position) true
  by_cases nonempty : branch.Nonempty
  · obtain ⟨reference, reference_mem⟩ := nonempty
    have reference_properties := (mem_checkedBranch _ _ _ _ _ _).1 reference_mem
    have zero_not_mem : (0 : Fin 10) ∉ ({position} : Finset (Fin 10)) := by
      simp [Ne.symm position_ne]
    have fixed_card : ({0, position} : Finset (Fin 10)).card = 2 := by
      rw [Finset.card_insert_of_notMem zero_not_mem]
      simp
    apply Sep.mono (larger := CylindricalFiber reference {0, position}) ?_
      (endgame reference {0, position} fixed_card)
    intro secret secret_mem
    have secret_properties := (mem_checkedBranch _ _ _ _ _ _).1 secret_mem
    have reference_cylindrical := (mem_cylindricalFiber _ _ _).1
      (contained reference_properties.1)
    have secret_cylindrical := (mem_cylindricalFiber _ _ _).1
      (contained secret_properties.1)
    rw [mem_cylindricalFiber]
    constructor
    · intro fixed fixed_mem
      simp only [Finset.mem_insert, Finset.mem_singleton] at fixed_mem
      rcases fixed_mem with fixed_zero | fixed_position
      · subst fixed
        exact secret_cylindrical.1 0 (by simp) |>.trans
          (reference_cylindrical.1 0 (by simp)).symm
      · subst fixed
        have secret_fixed :
            secret position = tenElevenCyclicGuess active position := by
          simpa using secret_properties.2.2
        have reference_fixed :
            reference position = tenElevenCyclicGuess active position := by
          simpa using reference_properties.2.2
        exact secret_fixed.trans reference_fixed.symm
    · intro shift
      exact (secret_cylindrical.2 shift).trans
        (reference_cylindrical.2 shift).symm
  · have empty : branch = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    change Sep 3 branch
    rw [empty]
    exact Sep.empty 3

theorem card_active_left_eq_of_mixed_black_eq
    {anchor : TenElevenSecret} {active cut : Fin 11}
    {first second : TenElevenSecret}
    (first_mem : first ∈ CylindricalFiber anchor {0})
    (second_mem : second ∈ CylindricalFiber anchor {0})
    (anchor_next_empty :
      OpenCyclicMatchSet (finRotate 11 active) anchor = ∅)
    (black_eq : tenElevenBlackAnswer (mixedCyclicGuess active cut) first =
      tenElevenBlackAnswer (mixedCyclicGuess active cut) second) :
    ((OpenCyclicMatchSet active first).filter fun position =>
      position.castSucc < cut).card =
    ((OpenCyclicMatchSet active second).filter fun position =>
      position.castSucc < cut).card := by
  have first_cylindrical := (mem_cylindricalFiber _ _ _).1 first_mem
  have second_cylindrical := (mem_cylindricalFiber _ _ _).1 second_mem
  have zero_eq : first 0 = second 0 :=
    (first_cylindrical.1 0 (by simp)).trans
      (second_cylindrical.1 0 (by simp)).symm
  have open_card := card_openGuessMatchSet_eq_of_black_eq_of_zero_eq
    (mixedCyclicGuess active cut) first second black_eq zero_eq
  rw [openGuessMatchSet_mixed_eq_left active cut first
      (next_open_empty_of_mem_cylindricalFiber_zero anchor_next_empty first_mem),
    openGuessMatchSet_mixed_eq_left active cut second
      (next_open_empty_of_mem_cylindricalFiber_zero anchor_next_empty second_mem)]
    at open_card
  exact open_card

theorem cyclicSearchInvariant_left_false
    {anchor : TenElevenSecret} {active cut low high : Fin 11}
    {candidates : Finset TenElevenSecret}
    {possibleFields : Finset (Fin 10)}
    (anchor_next_empty :
      OpenCyclicMatchSet (finRotate 11 active) anchor = ∅)
    (invariant : CyclicSearchInvariant anchor active low high
      possibleFields candidates)
    (cut_le_high : cut ≤ high)
    (black : Fin 11) (witness : TenElevenSecret)
    (witness_mem : witness ∈ candidates)
    (witness_black :
      tenElevenBlackAnswer (mixedCyclicGuess active cut) witness = black)
    (witness_left : ((OpenCyclicMatchSet active witness).filter fun position =>
      position.castSucc < cut).Nonempty)
    (tested : Fin 10) :
    CyclicSearchInvariant anchor active low cut
      ((possibleFields.filter fun position => position.castSucc < cut).erase tested)
      (checkedBranch candidates (mixedCyclicGuess active cut) black
        (tested, tenElevenCyclicGuess active tested) false) := by
  rcases invariant with ⟨contained, possible_window, state_invariant⟩
  have witness_cylindrical := contained witness_mem
  refine ⟨?_, ?_, ?_⟩
  · intro secret secret_mem
    exact contained ((mem_checkedBranch _ _ _ _ _ _).1 secret_mem |>.1)
  · intro position position_mem
    have selected_mem := (Finset.mem_erase.mp position_mem).2
    have properties := Finset.mem_filter.mp selected_mem
    exact ⟨(possible_window position properties.1).1, properties.2⟩
  · intro secret secret_mem
    have branch_properties := (mem_checkedBranch _ _ _ _ _ _).1 secret_mem
    have secret_mem_candidates := branch_properties.1
    have secret_cylindrical := contained secret_mem_candidates
    have original := state_invariant secret secret_mem_candidates
    have same_left_card := card_active_left_eq_of_mixed_black_eq
      secret_cylindrical witness_cylindrical anchor_next_empty
      (branch_properties.2.1.trans witness_black.symm)
    have secret_left : ((OpenCyclicMatchSet active secret).filter fun position =>
        position.castSucc < cut).Nonempty := by
      rw [← Finset.card_pos, same_left_card, Finset.card_pos]
      exact witness_left
    have tested_false :
        secret tested ≠ tenElevenCyclicGuess active tested := by
      simpa using branch_properties.2.2
    refine ⟨original.1, ?_, ?_⟩
    · intro position active_mem low_le below_cut
      have old_high : position.castSucc < high := below_cut.trans_le cut_le_high
      have old_possible := original.2.1 position active_mem low_le old_high
      have position_ne_tested : position ≠ tested := by
        intro equal
        subst position
        exact tested_false ((mem_openCyclicMatchSet _ _ _).1 active_mem |>.2)
      apply Finset.mem_erase.mpr
      exact ⟨position_ne_tested,
        Finset.mem_filter.mpr ⟨old_possible, below_cut⟩⟩
    · obtain ⟨position, position_mem⟩ := secret_left
      have properties := Finset.mem_filter.mp position_mem
      have low_le : low ≤ position.castSucc := by
        by_contra not_le
        have below_low : position.castSucc < low := by omega
        exact original.1 position properties.1 below_low
      exact ⟨position, properties.1, low_le, properties.2⟩

theorem cyclicSearchInvariant_right_false
    {anchor : TenElevenSecret} {active cut low high : Fin 11}
    {candidates : Finset TenElevenSecret}
    {possibleFields : Finset (Fin 10)}
    (anchor_next_empty :
      OpenCyclicMatchSet (finRotate 11 active) anchor = ∅)
    (invariant : CyclicSearchInvariant anchor active low high
      possibleFields candidates)
    (low_le_cut : low ≤ cut)
    (black : Fin 11) (witness : TenElevenSecret)
    (witness_mem : witness ∈ candidates)
    (witness_black :
      tenElevenBlackAnswer (mixedCyclicGuess active cut) witness = black)
    (witness_left_empty :
      (OpenCyclicMatchSet active witness).filter
        (fun position => position.castSucc < cut) = ∅)
    (tested : Fin 10) :
    CyclicSearchInvariant anchor active cut high
      ((possibleFields.filter fun position => cut ≤ position.castSucc).erase tested)
      (checkedBranch candidates (mixedCyclicGuess active cut) black
        (tested, tenElevenCyclicGuess active tested) false) := by
  rcases invariant with ⟨contained, possible_window, state_invariant⟩
  have witness_cylindrical := contained witness_mem
  refine ⟨?_, ?_, ?_⟩
  · intro secret secret_mem
    exact contained ((mem_checkedBranch _ _ _ _ _ _).1 secret_mem |>.1)
  · intro position position_mem
    have selected_mem := (Finset.mem_erase.mp position_mem).2
    have properties := Finset.mem_filter.mp selected_mem
    exact ⟨properties.2, (possible_window position properties.1).2⟩
  · intro secret secret_mem
    have branch_properties := (mem_checkedBranch _ _ _ _ _ _).1 secret_mem
    have secret_mem_candidates := branch_properties.1
    have secret_cylindrical := contained secret_mem_candidates
    have original := state_invariant secret secret_mem_candidates
    have same_left_card := card_active_left_eq_of_mixed_black_eq
      secret_cylindrical witness_cylindrical anchor_next_empty
      (branch_properties.2.1.trans witness_black.symm)
    have secret_left_empty :
        (OpenCyclicMatchSet active secret).filter
          (fun position => position.castSucc < cut) = ∅ := by
      apply Finset.card_eq_zero.mp
      rw [same_left_card, witness_left_empty]
      simp
    have tested_false :
        secret tested ≠ tenElevenCyclicGuess active tested := by
      simpa using branch_properties.2.2
    refine ⟨?_, ?_, ?_⟩
    · intro position active_mem below_cut
      have member : position ∈
          (OpenCyclicMatchSet active secret).filter fun position =>
            position.castSucc < cut := Finset.mem_filter.mpr ⟨active_mem, below_cut⟩
      rw [secret_left_empty] at member
      simp at member
    · intro position active_mem cut_le below_high
      have old_low : low ≤ position.castSucc := low_le_cut.trans cut_le
      have old_possible := original.2.1 position active_mem old_low below_high
      have position_ne_tested : position ≠ tested := by
        intro equal
        subst position
        exact tested_false ((mem_openCyclicMatchSet _ _ _).1 active_mem |>.2)
      apply Finset.mem_erase.mpr
      exact ⟨position_ne_tested,
        Finset.mem_filter.mpr ⟨old_possible, cut_le⟩⟩
    · obtain ⟨position, active_mem, old_low, below_high⟩ := original.2.2
      have cut_le : cut ≤ position.castSucc := by
        by_contra not_le
        have below_cut : position.castSucc < cut := by omega
        have member : position ∈
            (OpenCyclicMatchSet active secret).filter fun position =>
              position.castSucc < cut :=
          Finset.mem_filter.mpr ⟨active_mem, below_cut⟩
        rw [secret_left_empty] at member
        simp at member
      exact ⟨position, active_mem, cut_le, below_high⟩

set_option maxHeartbeats 800000 in
-- The branch-local invariant transport is large enough to need a raised budget.
/--
One equality-accelerated `findNext` round.  A balanced legal mixed query is
followed by an active-edge check.  The true child is an eight-rook endgame;
the false child preserves the search invariant and has at most
`ceil(|possible|/2) - 1` possible target fields.
-/
theorem cyclicSearchStep
    (endgame : EightRookCylindricalSepThree)
    {anchor : TenElevenSecret} {active low high : Fin 11}
    {possibleFields : Finset (Fin 10)}
    {candidates : Finset TenElevenSecret}
    (anchor_next_empty :
      OpenCyclicMatchSet (finRotate 11 active) anchor = ∅)
    (invariant : CyclicSearchInvariant anchor active low high
      possibleFields candidates)
    (candidates_nonempty : candidates.Nonempty)
    (zero_not_possible : (0 : Fin 10) ∉ possibleFields) :
    ∃ guess : TenElevenSecret, ∀ black : Fin 11,
      ∃ (tested : Fin 10) (newLow newHigh : Fin 11)
        (newPossible : Finset (Fin 10)),
        tested ≠ 0 ∧ (0 : Fin 10) ∉ newPossible ∧
          newPossible.card ≤ (possibleFields.card + 1) / 2 - 1 ∧
          Sep 3 (checkedBranch candidates guess black
            (tested, tenElevenCyclicGuess active tested) true) ∧
          CyclicSearchInvariant anchor active newLow newHigh newPossible
            (checkedBranch candidates guess black
              (tested, tenElevenCyclicGuess active tested) false) := by
  obtain ⟨reference, reference_mem⟩ := candidates_nonempty
  have reference_state := invariant.2.2 reference reference_mem
  obtain ⟨target, target_active, target_low, target_high⟩ := reference_state.2.2
  have low_le_high : low ≤ high := target_low.trans target_high.le
  obtain ⟨cut, low_le_cut, cut_le_high, left_balanced, right_balanced⟩ :=
    finTen_balanced_window_cut possibleFields low high
      ⟨low_le_high, invariant.2.1⟩
  let guess := mixedCyclicGuess active cut
  refine ⟨guess, ?_⟩
  intro black
  let blackState := candidates.filter fun secret =>
    tenElevenBlackAnswer guess secret = black
  by_cases black_nonempty : blackState.Nonempty
  · obtain ⟨witness, witness_mem_black⟩ := black_nonempty
    have witness_properties := Finset.mem_filter.mp witness_mem_black
    have witness_mem := witness_properties.1
    have witness_black : tenElevenBlackAnswer guess witness = black :=
      witness_properties.2
    have witness_state := invariant.2.2 witness witness_mem
    let leftPossible := possibleFields.filter fun position =>
      position.castSucc < cut
    let rightPossible := possibleFields.filter fun position =>
      cut ≤ position.castSucc
    let witnessLeft := (OpenCyclicMatchSet active witness).filter fun position =>
      position.castSucc < cut
    by_cases goes_left : witnessLeft.Nonempty
    · have selected_nonempty : leftPossible.Nonempty := by
        obtain ⟨position, position_mem⟩ := goes_left
        have properties := Finset.mem_filter.mp position_mem
        have position_low : low ≤ position.castSucc := by
          by_contra not_le
          have below_low : position.castSucc < low := by omega
          exact witness_state.1 position properties.1 below_low
        have position_high : position.castSucc < high :=
          properties.2.trans_le cut_le_high
        have possible_mem := witness_state.2.1 position properties.1
          position_low position_high
        exact ⟨position, Finset.mem_filter.mpr ⟨possible_mem, properties.2⟩⟩
      obtain ⟨tested, tested_mem⟩ := selected_nonempty
      have tested_possible : tested ∈ possibleFields :=
        (Finset.mem_filter.mp tested_mem).1
      have tested_ne : tested ≠ 0 := by
        intro tested_zero
        subst tested
        exact zero_not_possible tested_possible
      let newPossible := leftPossible.erase tested
      have zero_not_new : (0 : Fin 10) ∉ newPossible := by
        intro zero_mem
        exact zero_not_possible
          ((Finset.mem_filter.mp (Finset.mem_erase.mp zero_mem).2).1)
      have erase_card : newPossible.card + 1 = leftPossible.card := by
        dsimp [newPossible]
        rw [Finset.card_erase_of_mem tested_mem]
        have positive := Finset.one_le_card.mpr ⟨tested, tested_mem⟩
        omega
      have selected_bound :
          leftPossible.card ≤ (possibleFields.card + 1) / 2 := by
        simpa [leftPossible] using left_balanced
      have size_bound :
          newPossible.card ≤ (possibleFields.card + 1) / 2 - 1 := by
        omega
      refine ⟨tested, low, cut, newPossible, tested_ne, zero_not_new,
        size_bound, ?_, ?_⟩
      · exact checkedBranch_true_sep_three_of_eightRook endgame invariant.1
          guess black tested tested_ne
      · dsimp [guess]
        exact cyclicSearchInvariant_left_false anchor_next_empty invariant
          cut_le_high black witness witness_mem (by simpa [guess] using witness_black)
          (by simpa [witnessLeft] using goes_left) tested
    · have witness_left_empty : witnessLeft = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp goes_left
      have selected_nonempty : rightPossible.Nonempty := by
        obtain ⟨position, active_mem, position_low, position_high⟩ :=
          witness_state.2.2
        have cut_le_position : cut ≤ position.castSucc := by
          by_contra not_le
          have below_cut : position.castSucc < cut := by omega
          have member : position ∈ witnessLeft := by
            exact Finset.mem_filter.mpr ⟨active_mem, below_cut⟩
          rw [witness_left_empty] at member
          simp at member
        have possible_mem := witness_state.2.1 position active_mem
          position_low position_high
        exact ⟨position, Finset.mem_filter.mpr
          ⟨possible_mem, cut_le_position⟩⟩
      obtain ⟨tested, tested_mem⟩ := selected_nonempty
      have tested_possible : tested ∈ possibleFields :=
        (Finset.mem_filter.mp tested_mem).1
      have tested_ne : tested ≠ 0 := by
        intro tested_zero
        subst tested
        exact zero_not_possible tested_possible
      let newPossible := rightPossible.erase tested
      have zero_not_new : (0 : Fin 10) ∉ newPossible := by
        intro zero_mem
        exact zero_not_possible
          ((Finset.mem_filter.mp (Finset.mem_erase.mp zero_mem).2).1)
      have erase_card : newPossible.card + 1 = rightPossible.card := by
        dsimp [newPossible]
        rw [Finset.card_erase_of_mem tested_mem]
        have positive := Finset.one_le_card.mpr ⟨tested, tested_mem⟩
        omega
      have selected_bound :
          rightPossible.card ≤ (possibleFields.card + 1) / 2 := by
        simpa [rightPossible] using right_balanced
      have size_bound :
          newPossible.card ≤ (possibleFields.card + 1) / 2 - 1 := by
        omega
      refine ⟨tested, cut, high, newPossible, tested_ne, zero_not_new,
        size_bound, ?_, ?_⟩
      · exact checkedBranch_true_sep_three_of_eightRook endgame invariant.1
          guess black tested tested_ne
      · dsimp [guess]
        exact cyclicSearchInvariant_right_false anchor_next_empty invariant
          low_le_cut black witness witness_mem (by simpa [guess] using witness_black)
          (by simpa [witnessLeft] using witness_left_empty) tested
  · have black_empty : blackState = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp black_nonempty
    let tested : Fin 10 := 1
    have tested_ne : tested ≠ 0 := by decide
    have possible_nonempty : possibleFields.Nonempty := by
      have possible_mem := reference_state.2.1 target target_active
        target_low target_high
      exact ⟨target, possible_mem⟩
    have half_positive : 1 ≤ (possibleFields.card + 1) / 2 := by
      have card_positive := Finset.one_le_card.mpr possible_nonempty
      omega
    have checked_empty : ∀ bit : Bool,
        checkedBranch candidates guess black
          (tested, tenElevenCyclicGuess active tested) bit = ∅ := by
      intro bit
      apply Finset.eq_empty_of_forall_notMem
      intro secret secret_mem
      have properties := (mem_checkedBranch _ _ _ _ _ _).1 secret_mem
      have member_black : secret ∈ blackState :=
        Finset.mem_filter.mpr ⟨properties.1, properties.2.1⟩
      rw [black_empty] at member_black
      simp at member_black
    refine ⟨tested, low, high, ∅, tested_ne, by simp, Nat.zero_le _, ?_, ?_⟩
    · rw [checked_empty true]
      exact Sep.empty 3
    · rw [checked_empty false]
      refine ⟨Finset.empty_subset _, ?_, ?_⟩
      · simp
      · intro secret secret_mem
        simp at secret_mem

/-- A nonempty search window with at most one possible field fixes that field. -/
theorem sep_three_of_cyclicSearchInvariant_card_le_one
    (endgame : EightRookCylindricalSepThree)
    {anchor : TenElevenSecret} {active low high : Fin 11}
    {possibleFields : Finset (Fin 10)}
    {candidates : Finset TenElevenSecret}
    (invariant : CyclicSearchInvariant anchor active low high
      possibleFields candidates)
    (small : possibleFields.card ≤ 1)
    (zero_not_possible : (0 : Fin 10) ∉ possibleFields) :
    Sep 3 candidates := by
  by_cases nonempty : candidates.Nonempty
  · obtain ⟨reference, reference_mem⟩ := nonempty
    have reference_state := invariant.2.2 reference reference_mem
    obtain ⟨target, target_active, target_low, target_high⟩ := reference_state.2.2
    have target_possible := reference_state.2.1 target target_active
      target_low target_high
    have target_ne : target ≠ 0 := by
      intro target_zero
      subst target
      exact zero_not_possible target_possible
    have zero_not_mem : (0 : Fin 10) ∉ ({target} : Finset (Fin 10)) := by
      simp [Ne.symm target_ne]
    have fixed_card : ({0, target} : Finset (Fin 10)).card = 2 := by
      rw [Finset.card_insert_of_notMem zero_not_mem]
      simp
    apply Sep.mono (larger := CylindricalFiber reference {0, target}) ?_
      (endgame reference {0, target} fixed_card)
    intro secret secret_mem
    have secret_state := invariant.2.2 secret secret_mem
    obtain ⟨position, position_active, position_low, position_high⟩ :=
      secret_state.2.2
    have position_possible := secret_state.2.1 position position_active
      position_low position_high
    have position_eq : position = target := by
      exact (Finset.card_le_one.mp small) position position_possible target target_possible
    subst position
    have reference_cylindrical := (mem_cylindricalFiber _ _ _).1
      (invariant.1 reference_mem)
    have secret_cylindrical := (mem_cylindricalFiber _ _ _).1
      (invariant.1 secret_mem)
    rw [mem_cylindricalFiber]
    constructor
    · intro fixed fixed_mem
      simp only [Finset.mem_insert, Finset.mem_singleton] at fixed_mem
      rcases fixed_mem with fixed_zero | fixed_target
      · subst fixed
        exact (secret_cylindrical.1 0 (by simp)).trans
          (reference_cylindrical.1 0 (by simp)).symm
      · subst fixed
        exact ((mem_openCyclicMatchSet _ _ _).1 position_active).2.trans
          ((mem_openCyclicMatchSet _ _ _).1 target_active).2.symm
    · intro shift
      exact (secret_cylindrical.2 shift).trans
        (reference_cylindrical.2 shift).symm
  · have empty : candidates = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    rw [empty]
    exact Sep.empty 3

set_option maxHeartbeats 1200000 in
-- Two adaptive `Sep` layers duplicate the large search-step proof terms.
/--
The equality-accelerated `findNext` phase is genuinely two rounds.  Starting
from one fixed field and a common cylindrical profile, it reaches a two-fixed
eight-rook fiber after the recurrence `9 → 4 → 1`.  The only premise is the
universal legal three-round separator for those eight-rook fibers.
-/
theorem oneFixedCylindricalFiber_sep_five_of_eightRook
    (endgame : EightRookCylindricalSepThree)
    (anchor : TenElevenSecret) :
    Sep 5 (CylindricalFiber anchor {0}) := by
  obtain ⟨active, active_nonempty, next_empty⟩ :=
    exists_active_cyclic_shift anchor
  have initial_invariant := initial_cyclicSearchInvariant anchor active active_nonempty
  have anchor_mem : anchor ∈ CylindricalFiber anchor {0} := by
    rw [mem_cylindricalFiber]
    exact ⟨by simp, by simp⟩
  have initial_nonempty : (CylindricalFiber anchor {0}).Nonempty :=
    ⟨anchor, anchor_mem⟩
  have zero_not_initial : (0 : Fin 10) ∉
      ((Finset.univ : Finset (Fin 10)).erase 0) := by simp
  obtain ⟨firstGuess, firstOutcome⟩ := cyclicSearchStep endgame next_empty
    initial_invariant initial_nonempty zero_not_initial
  rw [show 5 = 4 + 1 by omega, sep_succ_iff]
  refine ⟨firstGuess, ?_⟩
  intro firstBlack
  obtain ⟨firstTest, firstLow, firstHigh, firstPossible,
    firstTest_ne, firstZero_not, firstSize, firstTrue, firstFalseInvariant⟩ :=
    firstOutcome firstBlack
  refine ⟨(firstTest, tenElevenCyclicGuess active firstTest),
    Sep.pad firstTrue, ?_⟩
  let firstFalse := checkedBranch (CylindricalFiber anchor {0}) firstGuess
    firstBlack (firstTest, tenElevenCyclicGuess active firstTest) false
  have firstSize_four : firstPossible.card ≤ 4 := by
    have initial_card :
        ((Finset.univ : Finset (Fin 10)).erase 0).card = 9 := by simp
    rw [initial_card] at firstSize
    norm_num at firstSize
    exact firstSize
  by_cases firstFalse_nonempty : firstFalse.Nonempty
  · obtain ⟨secondGuess, secondOutcome⟩ := cyclicSearchStep endgame next_empty
      firstFalseInvariant firstFalse_nonempty firstZero_not
    rw [show 4 = 3 + 1 by omega, sep_succ_iff]
    refine ⟨secondGuess, ?_⟩
    intro secondBlack
    obtain ⟨secondTest, secondLow, secondHigh, secondPossible,
      secondTest_ne, secondZero_not, secondSize, secondTrue,
      secondFalseInvariant⟩ := secondOutcome secondBlack
    refine ⟨(secondTest, tenElevenCyclicGuess active secondTest), secondTrue, ?_⟩
    have secondSize_one : secondPossible.card ≤ 1 := by
      omega
    exact sep_three_of_cyclicSearchInvariant_card_le_one endgame
      secondFalseInvariant secondSize_one secondZero_not
  · have firstFalse_empty : firstFalse = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp firstFalse_nonempty
    change Sep 4 firstFalse
    rw [firstFalse_empty]
    exact Sep.empty 4

/--
All closed stages of the proposed fifteen-round composition.  A proof of the
single proposition `EightRookCylindricalSepThree` would now produce an actual
`TenElevenStrategy 15` solving every secret.
-/
theorem exists_fifteenRoundStrategy_of_eightRookCylindricalSep
    (endgame : EightRookCylindricalSepThree) :
    ∃ tree : TenElevenStrategy 15, tree.Solves Finset.univ := by
  apply exists_strategy_of_sep
  apply sep_fifteen_of_setupFibers_sep_five
  intro anchor
  apply Sep.mono (cyclicSetupFiber_subset_cylindricalFiber_zero anchor)
  exact oneFixedCylindricalFiber_sep_five_of_eightRook endgame anchor

end BlackPegExtraCheck
