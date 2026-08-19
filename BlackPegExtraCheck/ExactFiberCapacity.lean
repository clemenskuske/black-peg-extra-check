/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.FiveZeroBridge

/-!
# Exact black-fiber capacities

Completing a ten-row injection to a permutation turns an exact match set into
a derangement problem.  If `b` of the ten query rows are fixed, the omitted
eleventh row is either fixed or moved, so an exact match set has at most
`D(10-b) + D(11-b)` members.  This replaces the earlier factorial union bound
for every black response, not only responses eight and nine.

The resulting four-round relaxed capacity is `89,036` rather than `92,206`.
The file carries that sharper capacity through the existing four-zero/four-
false adversary and completed-permanent bridges.
-/

namespace BlackPegExtraCheck

open Equiv Function

noncomputable def relativePermutation (guess secret : TenElevenSecret) : Equiv.Perm (Fin 11) :=
  (guessRelabeling secret).trans (guessRelabeling guess).symm

theorem relativePermutation_fixed_castSucc_iff
    (guess secret : TenElevenSecret) (i : Fin 10) :
    relativePermutation guess secret i.castSucc = i.castSucc ↔ secret i = guess i := by
  change (guessRelabeling guess).symm
      (guessRelabeling secret i.castSucc) = i.castSucc ↔ _
  rw [Equiv.symm_apply_eq]
  simp

theorem relativePermutation_injective (guess : TenElevenSecret) :
    Function.Injective (relativePermutation guess) := by
  intro secret other equal
  apply Function.Embedding.ext
  intro i
  apply (guessRelabeling guess).symm.injective
  simpa [relativePermutation] using
    congrArg (fun ρ : Equiv.Perm (Fin 11) => ρ i.castSucc) equal

def fixedRows (S : Finset (Fin 10)) : Finset (Fin 11) :=
  S.image Fin.castSuccEmb

abbrev exactRemainingLastFixed (S : Finset (Fin 10)) (x : Fin 11) : Prop :=
  x ≠ Fin.last 10 ∧ x ∉ fixedRows S

abbrev exactRemainingLastFree (S : Finset (Fin 10)) (x : Fin 11) : Prop :=
  x ∉ fixedRows S

noncomputable instance exactRemainingLastFixedFintype (S : Finset (Fin 10)) :
    Fintype {x : Fin 11 // exactRemainingLastFixed S x} := Fintype.ofFinite _

noncomputable instance exactRemainingLastFreeFintype (S : Finset (Fin 10)) :
    Fintype {x : Fin 11 // exactRemainingLastFree S x} := Fintype.ofFinite _

theorem card_exactRemainingLastFixed (S : Finset (Fin 10)) :
    Fintype.card {x : Fin 11 // exactRemainingLastFixed S x} = 10 - S.card := by
  classical
  rw [Fintype.card_subtype]
  simp only [exactRemainingLastFixed]
  have last_not_mem : Fin.last 10 ∉ fixedRows S := by
    intro membership
    obtain ⟨i, _hi, equal⟩ := Finset.mem_image.1 membership
    exact Fin.castSucc_ne_last i equal
  change (Finset.univ.filter fun x : Fin 11 =>
    x ≠ Fin.last 10 ∧ x ∉ fixedRows S).card = _
  rw [show (Finset.univ.filter fun x : Fin 11 =>
      x ≠ Fin.last 10 ∧ x ∉ fixedRows S) =
      (Finset.univ.erase (Fin.last 10)) \ fixedRows S by
    ext x
    simp [and_comm]]
  rw [Finset.card_sdiff_of_subset]
  · rw [show (fixedRows S).card = S.card by
      exact Finset.card_image_of_injective _ (Fin.castSucc_injective 10)]
    simp
  · intro x hx
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact fun equal => last_not_mem (equal ▸ hx)

theorem card_exactRemainingLastFree (S : Finset (Fin 10)) :
    Fintype.card {x : Fin 11 // exactRemainingLastFree S x} = 11 - S.card := by
  classical
  rw [Fintype.card_subtype]
  simp only [exactRemainingLastFree]
  rw [show (Finset.univ.filter fun x : Fin 11 => x ∉ fixedRows S) =
      Finset.univ \ fixedRows S by
    ext x
    simp]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  rw [show (fixedRows S).card = S.card by
    exact Finset.card_image_of_injective _ (Fin.castSucc_injective 10)]
  simp

theorem relativePermutation_lastFixedCondition
    (guess : TenElevenSecret) (S : Finset (Fin 10))
    (secret : ↥(ExactMatchSetFinset guess S))
    (last_fixed : relativePermutation guess secret.1 (Fin.last 10) = Fin.last 10) :
    ∀ x, ¬ exactRemainingLastFixed S x ↔
      x ∈ fixedPoints (relativePermutation guess secret.1) := by
  classical
  let ρ := relativePermutation guess secret.1
  have exact : MatchSet guess secret.1 = S :=
    (Finset.mem_filter.1 secret.2).2
  have fixed_cast (i : Fin 10) :
      ρ i.castSucc = i.castSucc ↔ i ∈ S := by
    rw [relativePermutation_fixed_castSucc_iff]
    have membership : i ∈ MatchSet guess secret.1 ↔ i ∈ S := by rw [exact]
    simpa [MatchSet] using membership
  intro x
  induction x using Fin.lastCases with
  | last =>
      constructor
      · intro _
        simpa only [mem_fixedPoints, IsFixedPt] using last_fixed
      · intro _ not_remaining
        exact not_remaining.1 rfl
  | cast i =>
      have cast_ne_last : i.castSucc ≠ Fin.last 10 := Fin.castSucc_ne_last i
      constructor
      · intro not_remaining
        have memS : i ∈ S := by
          by_contra not_mem
          apply not_remaining
          exact ⟨cast_ne_last, by simpa [fixedRows] using not_mem⟩
        simpa only [mem_fixedPoints, IsFixedPt] using (fixed_cast i).2 memS
      · intro is_fixed not_remaining
        have fixed_eq : ρ i.castSucc = i.castSucc := by
          simpa only [mem_fixedPoints, IsFixedPt] using is_fixed
        have memS : i ∈ S := (fixed_cast i).1 fixed_eq
        exact not_remaining.2 (by simpa [fixedRows] using memS)

theorem relativePermutation_lastFreeCondition
    (guess : TenElevenSecret) (S : Finset (Fin 10))
    (secret : ↥(ExactMatchSetFinset guess S))
    (last_free : ¬ relativePermutation guess secret.1 (Fin.last 10) = Fin.last 10) :
    ∀ x, ¬ exactRemainingLastFree S x ↔
      x ∈ fixedPoints (relativePermutation guess secret.1) := by
  classical
  let ρ := relativePermutation guess secret.1
  have exact : MatchSet guess secret.1 = S :=
    (Finset.mem_filter.1 secret.2).2
  have fixed_cast (i : Fin 10) :
      ρ i.castSucc = i.castSucc ↔ i ∈ S := by
    rw [relativePermutation_fixed_castSucc_iff]
    have membership : i ∈ MatchSet guess secret.1 ↔ i ∈ S := by rw [exact]
    simpa [MatchSet] using membership
  intro x
  induction x using Fin.lastCases with
  | last =>
      constructor
      · intro not_not_member
        have member : Fin.last 10 ∈ fixedRows S := by
          by_contra not_member
          exact not_not_member not_member
        obtain ⟨i, _hi, equal⟩ := Finset.mem_image.1 member
        exact (Fin.castSucc_ne_last i equal).elim
      · intro is_fixed
        have fixed_eq : ρ (Fin.last 10) = Fin.last 10 := by
          simpa only [mem_fixedPoints, IsFixedPt] using is_fixed
        exact (last_free fixed_eq).elim
  | cast i =>
      constructor
      · intro mem_fixed
        have memS : i ∈ S := by simpa [fixedRows] using mem_fixed
        simpa only [mem_fixedPoints, IsFixedPt] using (fixed_cast i).2 memS
      · intro is_fixed
        have fixed_eq : ρ i.castSucc = i.castSucc := by
          simpa only [mem_fixedPoints, IsFixedPt] using is_fixed
        have memS : i ∈ S := (fixed_cast i).1 fixed_eq
        simpa [fixedRows] using memS

noncomputable def exactMatchSetToDerangements
    (guess : TenElevenSecret) (S : Finset (Fin 10))
    (secret : ↥(ExactMatchSetFinset guess S)) :
      derangements {x : Fin 11 // exactRemainingLastFixed S x} ⊕
        derangements {x : Fin 11 // exactRemainingLastFree S x} := by
  classical
  let ρ := relativePermutation guess secret.1
  by_cases last_fixed : ρ (Fin.last 10) = Fin.last 10
  · exact Sum.inl ((derangements.subtypeEquiv
      (exactRemainingLastFixed S)).symm
        ⟨ρ, relativePermutation_lastFixedCondition guess S secret last_fixed⟩)
  · exact Sum.inr ((derangements.subtypeEquiv
      (exactRemainingLastFree S)).symm
        ⟨ρ, relativePermutation_lastFreeCondition guess S secret last_fixed⟩)

noncomputable def derangementSumPermutation (S : Finset (Fin 10)) :
    derangements {x : Fin 11 // exactRemainingLastFixed S x} ⊕
        derangements {x : Fin 11 // exactRemainingLastFree S x} →
      Equiv.Perm (Fin 11) := by
    classical
    exact fun
      | Sum.inl d => ((derangements.subtypeEquiv (exactRemainingLastFixed S)) d).1
      | Sum.inr d => ((derangements.subtypeEquiv (exactRemainingLastFree S)) d).1

theorem derangementSumPermutation_exactMatchSetToDerangements
    (guess : TenElevenSecret) (S : Finset (Fin 10))
    (secret : ↥(ExactMatchSetFinset guess S)) :
    derangementSumPermutation S (exactMatchSetToDerangements guess S secret) =
      relativePermutation guess secret.1 := by
  classical
  by_cases last_fixed :
      relativePermutation guess secret.1 (Fin.last 10) = Fin.last 10
  · unfold exactMatchSetToDerangements
    simp only [dif_pos last_fixed, derangementSumPermutation]
    exact congrArg Subtype.val ((derangements.subtypeEquiv
      (exactRemainingLastFixed S)).apply_symm_apply _)
  · unfold exactMatchSetToDerangements
    simp only [dif_neg last_fixed, derangementSumPermutation]
    exact congrArg Subtype.val ((derangements.subtypeEquiv
      (exactRemainingLastFree S)).apply_symm_apply _)

theorem exactMatchSetToDerangements_injective
    (guess : TenElevenSecret) (S : Finset (Fin 10)) :
    Function.Injective (exactMatchSetToDerangements guess S) := by
  classical
  intro secret other equal
  apply Subtype.ext
  apply relativePermutation_injective guess
  have decoded := congrArg (derangementSumPermutation S) equal
  simpa [derangementSumPermutation_exactMatchSetToDerangements] using decoded

theorem card_exactMatchSetFinset_derangement_upper
    (guess : TenElevenSecret) (S : Finset (Fin 10)) :
    (ExactMatchSetFinset guess S).card ≤
      numDerangements (10 - S.card) + numDerangements (11 - S.card) := by
  rw [← Fintype.card_coe]
  have bound := Fintype.card_le_of_injective
    (exactMatchSetToDerangements guess S)
    (exactMatchSetToDerangements_injective guess S)
  rw [Fintype.card_sum] at bound
  simpa only [card_derangements_eq_numDerangements,
    card_exactRemainingLastFixed, card_exactRemainingLastFree] using bound

theorem card_blackFiberFinset_derangement_upper
    (guess : TenElevenSecret) (b : Nat) :
    (BlackFiberFinset guess b).card ≤ Nat.choose 10 b *
      (numDerangements (10 - b) + numDerangements (11 - b)) := by
  classical
  have subset : BlackFiberFinset guess b ⊆
      ((Finset.univ : Finset (Fin 10)).powersetCard b).biUnion
        (ExactMatchSetFinset guess) := by
    intro secret hsecret
    have match_card : (MatchSet guess secret).card = b :=
      (Finset.mem_filter.1 hsecret).2
    exact Finset.mem_biUnion.mpr ⟨MatchSet guess secret,
      Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, match_card⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
  calc
    (BlackFiberFinset guess b).card ≤
        (((Finset.univ : Finset (Fin 10)).powersetCard b).biUnion
          (ExactMatchSetFinset guess)).card := Finset.card_le_card subset
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin 10)).powersetCard b,
        (ExactMatchSetFinset guess S).card := Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ (Finset.univ : Finset (Fin 10)).powersetCard b,
        (numDerangements (10 - b) + numDerangements (11 - b)) := by
      apply Finset.sum_le_sum
      intro S hS
      have cardS : S.card = b := (Finset.mem_powersetCard.1 hS).2
      simpa [cardS] using card_exactMatchSetFinset_derangement_upper guess S
    _ = Nat.choose 10 b *
        (numDerangements (10 - b) + numDerangements (11 - b)) := by simp

def tenElevenExactBlackFiberCap (b : Fin 11) : Nat :=
  Nat.choose 10 b.1 *
    (numDerangements (10 - b.1) + numDerangements (11 - b.1))

theorem card_tenElevenExactBlackFiber_upper (guess : TenElevenSecret) (b : Fin 11) :
    (Finset.univ.filter fun secret => tenElevenBlackAnswer guess secret = b).card ≤
      tenElevenExactBlackFiberCap b := by
  have subset :
      (Finset.univ.filter fun secret => tenElevenBlackAnswer guess secret = b) ⊆
        BlackFiberFinset guess b.1 := by
    intro secret hsecret
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      congrArg Fin.val (Finset.mem_filter.1 hsecret).2⟩
  exact (Finset.card_le_card subset).trans
    (card_blackFiberFinset_derangement_upper guess b.1)

def tenElevenDerangementCapacity : Nat → Nat
  | 0 => 1
  | rounds + 1 => ∑ b : Fin 11,
      min (tenElevenExactBlackFiberCap b) (2 * tenElevenDerangementCapacity rounds)

@[simp] theorem tenElevenDerangementCapacity_three :
    tenElevenDerangementCapacity 3 = 6370 := by decide

@[simp] theorem tenElevenDerangementCapacity_four :
    tenElevenDerangementCapacity 4 = 89036 := by decide

theorem TenElevenRelaxedStrategy.card_le_derangementCapacity {rounds : Nat}
    (tree : TenElevenRelaxedStrategy rounds) (candidates : Finset TenElevenSecret)
    (solves : tree.Solves candidates) :
    candidates.card ≤ tenElevenDerangementCapacity rounds := by
  induction tree generalizing candidates with
  | leaf => exact solves
  | @node rounds guess extra next ih =>
      rw [tenElevenDerangementCapacity]
      rw [Finset.card_eq_sum_card_fiberwise
        (s := candidates) (t := Finset.univ)
        (f := tenElevenBlackAnswer guess) (by simp)]
      apply Finset.sum_le_sum
      intro b _hb
      apply le_min
      · apply (Finset.card_le_card ?_).trans
          (card_tenElevenExactBlackFiber_upper guess b)
        intro secret hsecret
        exact Finset.mem_filter.2
          ⟨Finset.mem_univ _, (Finset.mem_filter.1 hsecret).2⟩
      · change (TenElevenRelaxedStrategy.blackBranch candidates guess b).card ≤ _
        rw [Finset.card_eq_sum_card_fiberwise
          (s := TenElevenRelaxedStrategy.blackBranch candidates guess b)
          (t := Finset.univ) (f := extra b) (by
            intro _secret _hsecret
            exact Finset.mem_univ _)]
        change (∑ bit : Bool,
          (TenElevenRelaxedStrategy.answerBranch candidates guess extra b bit).card) ≤ _
        calc
          ∑ bit : Bool,
              (TenElevenRelaxedStrategy.answerBranch candidates guess extra b bit).card
              ≤ ∑ _bit : Bool, tenElevenDerangementCapacity rounds := by
            apply Finset.sum_le_sum
            intro bit _hbit
            exact ih b bit
              (TenElevenRelaxedStrategy.answerBranch candidates guess extra b bit)
              (solves b bit)
          _ = 2 * tenElevenDerangementCapacity rounds := by simp

/-- No relaxed four-round continuation can distinguish 89,037 candidates. -/
theorem no_four_round_continuation_of_derangement_large
    (tree : TenElevenRelaxedStrategy 4) (candidates : Finset TenElevenSecret)
    (large : 89036 < candidates.card) : ¬ tree.Solves candidates := by
  intro solves
  have upper := tree.card_le_derangementCapacity candidates solves
  rw [tenElevenDerangementCapacity_four] at upper
  omega

/--
Sharper four-response adversary reduction for the ninth round.  Its only
premise is the concrete survivor inequality above the exact derangement
capacity `89,036`.
-/
theorem tenElevenLowerBoundNine_of_fourZeroFalse_derangement_large
    (fourZeroFalseLarge :
      ∀ (guess₀ guess₁ guess₂ guess₃ : TenElevenSecret)
        (edge₀ edge₁ edge₂ edge₃ : Fin 10 × Fin 11),
        89036 < (FourZeroFalseFinset guess₀ guess₁ guess₂ guess₃
          edge₀ edge₁ edge₂ edge₃).card)
    (tree : TenElevenStrategy 8) (solves : tree.Solves Finset.univ) : False := by
  cases tree with
  | node guess₀ check₀ next₀ =>
      have solves₁ := solves (0 : Fin 11) false
      cases tree₁ : next₀ 0 false with
      | node guess₁ check₁ next₁ =>
          change (next₀ 0 false).toRelaxed.Solves _ at solves₁
          rw [tree₁] at solves₁
          have solves₂ := solves₁ (0 : Fin 11) false
          cases tree₂ : next₁ 0 false with
          | node guess₂ check₂ next₂ =>
              change (next₁ 0 false).toRelaxed.Solves _ at solves₂
              rw [tree₂] at solves₂
              have solves₃ := solves₂ (0 : Fin 11) false
              cases tree₃ : next₂ 0 false with
              | node guess₃ check₃ next₃ =>
                  change (next₂ 0 false).toRelaxed.Solves _ at solves₃
                  rw [tree₃] at solves₃
                  have solves₄ := solves₃ (0 : Fin 11) false
                  have large := fourZeroFalseLarge guess₀ guess₁ guess₂ guess₃
                    (check₀ 0) (check₁ 0) (check₂ 0) (check₃ 0)
                  apply no_four_round_continuation_of_derangement_large
                    ((next₃ 0 false).toRelaxed)
                    (FourZeroFalseFinset guess₀ guess₁ guess₂ guess₃
                      (check₀ 0) (check₁ 0) (check₂ 0) (check₃ 0))
                    large
                  simpa [FourZeroFalseFinset, zeroFalseStep,
                    TenElevenRelaxedStrategy.answerBranch,
                    TenElevenRelaxedStrategy.blackBranch,
                    tree₁, tree₂, tree₃]
                    using solves₄

/-- The sharper four-response theorem stated as a completed-permanent bridge. -/
theorem tenElevenLowerBoundNine_of_completedFourPermanent_derangement_large
    (completedPermanentLarge :
      ∀ (guesses : Fin 4 → TenElevenSecret)
        (edges : Fin 4 → Fin 10 × Fin 11),
        89036 <
          (PerfectMatchingFinset
            (completedFourPathAllowed guesses edges)).card)
    (tree : TenElevenStrategy 8) (solves : tree.Solves Finset.univ) : False := by
  apply tenElevenLowerBoundNine_of_fourZeroFalse_derangement_large ?_ tree solves
  intro guess₀ guess₁ guess₂ guess₃ edge₀ edge₁ edge₂ edge₃
  let guesses : Fin 4 → TenElevenSecret := ![guess₀, guess₁, guess₂, guess₃]
  let edges : Fin 4 → Fin 10 × Fin 11 := ![edge₀, edge₁, edge₂, edge₃]
  have permanentLarge := completedPermanentLarge guesses edges
  have permanentLe := card_completedFourPathPerfectMatchings_le_fourZeroFalse
    guess₀ guess₁ guess₂ guess₃ edge₀ edge₁ edge₂ edge₃
  exact permanentLarge.trans_le permanentLe

end BlackPegExtraCheck
