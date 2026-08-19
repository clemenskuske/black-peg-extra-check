/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.ExactFiberCapacity

/-!
# Exact aggregate four-check bridge

The individual one-sixth edge marginal is stronger than the four-round
argument needs, and it is false when completed queries overlap.  The exact
loss is instead the union of the four checked-edge events.  This file proves
that the query-only perfect matchings partition into the completed-path
matchings and that union, then carries the weakest resulting strict inequality
through the kernel-checked `89,036` continuation threshold.
-/

namespace BlackPegExtraCheck

/-- Query-only perfect matchings lost by at least one of the four checks. -/
noncomputable def FourPathAnyCheckedEdgeUseFinset
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11) :
    Finset (Equiv.Perm (Fin 11)) := by
  classical
  exact Finset.univ.biUnion (FourPathCheckedEdgeUseFinset guesses edges)

@[simp] theorem mem_FourPathAnyCheckedEdgeUseFinset
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11)
    (σ : Equiv.Perm (Fin 11)) :
    σ ∈ FourPathAnyCheckedEdgeUseFinset guesses edges ↔
      (∀ row, completedFourQueriesAllowed guesses row (σ row)) ∧
        ∃ t, σ (edges t).1.castSucc = (edges t).2 := by
  classical
  simp only [FourPathAnyCheckedEdgeUseFinset, Finset.mem_biUnion,
    Finset.mem_univ, true_and, mem_FourPathCheckedEdgeUseFinset]
  constructor
  · rintro ⟨t, queryAllowed, uses⟩
    exact ⟨queryAllowed, t, uses⟩
  · rintro ⟨queryAllowed, t, uses⟩
    exact ⟨t, queryAllowed, uses⟩

theorem fourPathAnyCheckedEdgeUse_subset_queryPerfectMatchings
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11) :
    FourPathAnyCheckedEdgeUseFinset guesses edges ⊆
      PerfectMatchingFinset (completedFourQueriesAllowed guesses) := by
  intro σ membership
  rw [mem_FourPathAnyCheckedEdgeUseFinset] at membership
  rw [mem_PerfectMatchingFinset]
  exact membership.1

/-- Surviving matchings are exactly the query matchings outside the loss union. -/
theorem completedFourPathPerfectMatchings_eq_query_sdiff_aggregateLoss
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11) :
    PerfectMatchingFinset (completedFourPathAllowed guesses edges) =
      PerfectMatchingFinset (completedFourQueriesAllowed guesses) \
        FourPathAnyCheckedEdgeUseFinset guesses edges := by
  classical
  ext σ
  rw [mem_PerfectMatchingFinset, Finset.mem_sdiff,
    mem_PerfectMatchingFinset, mem_FourPathAnyCheckedEdgeUseFinset]
  simp only [completedFourPathAllowed, completedFourQueriesAllowed]
  constructor
  · intro allowed
    constructor
    · intro row
      exact (allowed row).1
    · rintro ⟨_queryAllowed, t, uses⟩
      exact (allowed (edges t).1.castSucc).2 t rfl uses
  · rintro ⟨queryAllowed, notLost⟩ row
    constructor
    · exact queryAllowed row
    · intro t rowEq colorEq
      apply notLost
      refine ⟨queryAllowed, t, ?_⟩
      simpa [rowEq] using colorEq

/-- Exact cardinal partition, automatically accounting for repeated checks. -/
theorem card_completedFourPath_add_aggregateLoss_eq_query
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11) :
    (PerfectMatchingFinset (completedFourPathAllowed guesses edges)).card +
        (FourPathAnyCheckedEdgeUseFinset guesses edges).card =
      (PerfectMatchingFinset (completedFourQueriesAllowed guesses)).card := by
  rw [completedFourPathPerfectMatchings_eq_query_sdiff_aggregateLoss]
  rw [Finset.card_sdiff_add_card]
  rw [Finset.union_eq_left.mpr
    (fourPathAnyCheckedEdgeUse_subset_queryPerfectMatchings guesses edges)]

/-- The weakest exact aggregate inequality needed by the four-round bridge. -/
theorem card_completedFourPath_derangement_large_of_aggregateLoss
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11)
    (aggregate :
      89036 + (FourPathAnyCheckedEdgeUseFinset guesses edges).card <
        (PerfectMatchingFinset
          (completedFourQueriesAllowed guesses)).card) :
    89036 <
      (PerfectMatchingFinset (completedFourPathAllowed guesses edges)).card := by
  have partition :=
    card_completedFourPath_add_aggregateLoss_eq_query guesses edges
  omega

/--
A concrete relaxed aggregate target.  Compared with the old requirement that
the sum of four marginals be at most `2/3` of the query permanent, the exact
loss union may exceed `2/3` by `3,176` matchings at the minimum query count.
-/
theorem card_completedFourPath_derangement_large_of_relaxedAggregate
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11)
    (queryLarge : 276640 ≤
      (PerfectMatchingFinset (completedFourQueriesAllowed guesses)).card)
    (aggregate :
      3 * (FourPathAnyCheckedEdgeUseFinset guesses edges).card ≤
        2 * (PerfectMatchingFinset
          (completedFourQueriesAllowed guesses)).card + 9529) :
    89036 <
      (PerfectMatchingFinset (completedFourPathAllowed guesses edges)).card := by
  have partition :=
    card_completedFourPath_add_aggregateLoss_eq_query guesses edges
  omega

/-- End-to-end lower-nine reduction through the exact four-check loss union. -/
theorem tenElevenLowerBoundNine_of_aggregateFourCheckLoss
    (aggregate : ∀ (guesses : Fin 4 → TenElevenSecret)
        (edges : Fin 4 → Fin 10 × Fin 11),
      89036 + (FourPathAnyCheckedEdgeUseFinset guesses edges).card <
        (PerfectMatchingFinset
          (completedFourQueriesAllowed guesses)).card)
    (tree : TenElevenStrategy 8) (solves : tree.Solves Finset.univ) : False := by
  apply tenElevenLowerBoundNine_of_completedFourPermanent_derangement_large
    ?_ tree solves
  intro guesses edges
  exact card_completedFourPath_derangement_large_of_aggregateLoss
    guesses edges (aggregate guesses edges)

/-- End-to-end bridge through the relaxed aggregate target and query bound. -/
theorem tenElevenLowerBoundNine_of_relaxedAggregateFourCheckLoss
    (queryLarge : ∀ guesses : Fin 4 → TenElevenSecret,
      276640 ≤
        (PerfectMatchingFinset (completedFourQueriesAllowed guesses)).card)
    (aggregate : ∀ (guesses : Fin 4 → TenElevenSecret)
        (edges : Fin 4 → Fin 10 × Fin 11),
      3 * (FourPathAnyCheckedEdgeUseFinset guesses edges).card ≤
        2 * (PerfectMatchingFinset
          (completedFourQueriesAllowed guesses)).card + 9529)
    (tree : TenElevenStrategy 8) (solves : tree.Solves Finset.univ) : False := by
  apply tenElevenLowerBoundNine_of_completedFourPermanent_derangement_large
    ?_ tree solves
  intro guesses edges
  exact card_completedFourPath_derangement_large_of_relaxedAggregate
    guesses edges (queryLarge guesses) (aggregate guesses edges)

end BlackPegExtraCheck
