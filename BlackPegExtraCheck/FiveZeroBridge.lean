/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.TenFieldsElevenColors
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Perfect-matching bridge for five zero/false answers

This file isolates the graph-theoretic part of the prospective ninth-round
lower bound.  A ten-row injection extends uniquely to a permutation of the
eleven colors.  Conversely, restricting a permutation to the first ten rows
is injective.  Therefore perfect matchings avoiding five *completed* guesses
and five checked edges inject into the actual five-zero/five-false survivor
state.

The file also records two exact downstream reductions.

* A five-regular spanning subrelation, together with the displayed permanent
  inequality, already forces more than the short three-round capacity `6370`.
* If a cut of a six-regular graph violates the five-factor cut inequality
  after at most five edge deletions, its excess
  `s = |X| + |Y| - 11` lies in `{1,2,3,4}` and at least `s+1` deleted edges
  lie in the cut.
* Likewise, failure of the six-factor cut inequality after at most four
  deletions from a seven-regular graph has excess `s` in `{1,2,3}`.
  A concrete four-query/four-check state shows that the `s = 1` exception is
  real: one color can have degree three, so a universal six-factor shortcut
  is false even though the state is nonempty.

No converse to the five-factor cut criterion and no permanent inequality are
assumed globally here.  The same applies to the six-factor cut criterion.  The
theorem using the permanent bound takes that inequality as an explicit premise.
-/

namespace BlackPegExtraCheck

open scoped BigOperators

/-! ## Completing and restricting eleven-color permutations -/

/-- Restrict an eleven-color permutation to the ten game rows. -/
def restrictElevenPermutation (σ : Equiv.Perm (Fin 11)) : TenElevenSecret :=
  Fin.castSuccEmb.trans σ.toEmbedding

@[simp] theorem restrictElevenPermutation_apply (σ : Equiv.Perm (Fin 11))
    (i : Fin 10) :
    restrictElevenPermutation σ i = σ i.castSucc := rfl

/-- Restriction to the first ten rows loses no information about a permutation. -/
theorem restrictElevenPermutation_injective :
    Function.Injective restrictElevenPermutation := by
  intro σ τ restricted
  apply perm_eq_of_castSucc_eq
  intro i
  exact congrArg (fun secret : TenElevenSecret => secret i) restricted

/-- Complete a legal ten-row secret to its unique eleven-color permutation. -/
noncomputable def completeTenElevenSecret (secret : TenElevenSecret) :
    Equiv.Perm (Fin 11) :=
  guessRelabeling secret

@[simp] theorem completeTenElevenSecret_apply_castSucc
    (secret : TenElevenSecret) (i : Fin 10) :
    completeTenElevenSecret secret i.castSucc = secret i := by
  exact guessRelabeling_apply secret i

@[simp] theorem restrict_completeTenElevenSecret (secret : TenElevenSecret) :
    restrictElevenPermutation (completeTenElevenSecret secret) = secret := by
  apply Function.Embedding.ext
  intro i
  exact completeTenElevenSecret_apply_castSucc secret i

@[simp] theorem complete_restrictElevenPermutation (σ : Equiv.Perm (Fin 11)) :
    completeTenElevenSecret (restrictElevenPermutation σ) = σ := by
  apply perm_eq_of_castSucc_eq
  intro i
  simp

/-- Ten-row injections into eleven colors are equivalent to permutations of eleven colors. -/
noncomputable def tenElevenSecretEquivPermutation :
    TenElevenSecret ≃ Equiv.Perm (Fin 11) where
  toFun := completeTenElevenSecret
  invFun := restrictElevenPermutation
  left_inv := restrict_completeTenElevenSecret
  right_inv := complete_restrictElevenPermutation

/-! ## Perfect matchings contained in a five-zero/five-false state -/

/-- Permutations all of whose edges satisfy `allowed`. -/
noncomputable def PerfectMatchingFinset
    (allowed : Fin 11 → Fin 11 → Prop) : Finset (Equiv.Perm (Fin 11)) := by
  classical
  exact Finset.univ.filter fun σ => ∀ row, allowed row (σ row)

@[simp] theorem mem_PerfectMatchingFinset
    (allowed : Fin 11 → Fin 11 → Prop) (σ : Equiv.Perm (Fin 11)) :
    σ ∈ PerfectMatchingFinset allowed ↔ ∀ row, allowed row (σ row) := by
  classical
  simp [PerfectMatchingFinset]

/-- The relation left after five completed queries and five ten-row edge checks. -/
def completedFivePathAllowed
    (guesses : Fin 5 → TenElevenSecret)
    (edges : Fin 5 → Fin 10 × Fin 11)
    (row color : Fin 11) : Prop :=
  (∀ t, color ≠ completeTenElevenSecret (guesses t) row) ∧
    ∀ t, row = (edges t).1.castSucc → color ≠ (edges t).2

/-- The same five zero/false constraints expressed directly on ten-row secrets. -/
noncomputable def FiveZeroFalseVectorFinset
    (guesses : Fin 5 → TenElevenSecret)
    (edges : Fin 5 → Fin 10 × Fin 11) : Finset TenElevenSecret := by
  classical
  exact Finset.univ.filter fun secret =>
    ∀ t, (∀ i, secret i ≠ guesses t i) ∧ secret (edges t).1 ≠ (edges t).2

@[simp] theorem mem_FiveZeroFalseVectorFinset
    (guesses : Fin 5 → TenElevenSecret)
    (edges : Fin 5 → Fin 10 × Fin 11) (secret : TenElevenSecret) :
    secret ∈ FiveZeroFalseVectorFinset guesses edges ↔
      ∀ t, (∀ i, secret i ≠ guesses t i) ∧
        secret (edges t).1 ≠ (edges t).2 := by
  classical
  simp [FiveZeroFalseVectorFinset]

/-- Restrict a completed-path perfect matching to an actual surviving secret. -/
noncomputable def restrictCompletedPathMatching
    (guesses : Fin 5 → TenElevenSecret)
    (edges : Fin 5 → Fin 10 × Fin 11) :
    ↥(PerfectMatchingFinset (completedFivePathAllowed guesses edges)) →
      ↥(FiveZeroFalseVectorFinset guesses edges) := by
  intro matching
  refine ⟨restrictElevenPermutation matching.1, ?_⟩
  rw [mem_FiveZeroFalseVectorFinset]
  intro t
  have allowed := (mem_PerfectMatchingFinset
    (completedFivePathAllowed guesses edges) matching.1).1 matching.2
  constructor
  · intro i
    have avoids := (allowed i.castSucc).1 t
    simpa [restrictElevenPermutation_apply] using avoids
  · have avoids := (allowed (edges t).1.castSucc).2 t rfl
    simpa [restrictElevenPermutation_apply] using avoids

theorem restrictCompletedPathMatching_injective
    (guesses : Fin 5 → TenElevenSecret)
    (edges : Fin 5 → Fin 10 × Fin 11) :
    Function.Injective (restrictCompletedPathMatching guesses edges) := by
  intro σ τ restricted
  apply Subtype.ext
  apply restrictElevenPermutation_injective
  exact congrArg Subtype.val restricted

/--
The permanent of the completed eleven-by-eleven avoidance graph is a lower
bound for the genuine five-zero/five-false survivor state.
-/
theorem card_completedPathPerfectMatchings_le_survivors
    (guesses : Fin 5 → TenElevenSecret)
    (edges : Fin 5 → Fin 10 × Fin 11) :
    (PerfectMatchingFinset (completedFivePathAllowed guesses edges)).card ≤
      (FiveZeroFalseVectorFinset guesses edges).card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_le_of_injective
    (restrictCompletedPathMatching guesses edges)
    (restrictCompletedPathMatching_injective guesses edges)

/-- The vector presentation maps into the five-step state used by the game tree. -/
theorem fiveZeroFalseVectorFinset_tuple_subset
    (guess₀ guess₁ guess₂ guess₃ guess₄ : TenElevenSecret)
    (edge₀ edge₁ edge₂ edge₃ edge₄ : Fin 10 × Fin 11) :
    FiveZeroFalseVectorFinset
        (![guess₀, guess₁, guess₂, guess₃, guess₄] : Fin 5 → TenElevenSecret)
        (![edge₀, edge₁, edge₂, edge₃, edge₄] : Fin 5 → Fin 10 × Fin 11) ⊆
      FiveZeroFalseFinset guess₀ guess₁ guess₂ guess₃ guess₄
        edge₀ edge₁ edge₂ edge₃ edge₄ := by
  classical
  intro secret hsecret
  rw [mem_FiveZeroFalseVectorFinset] at hsecret
  have h₀ := hsecret (0 : Fin 5)
  have h₁ := hsecret (1 : Fin 5)
  have h₂ := hsecret (2 : Fin 5)
  have h₃ := hsecret (3 : Fin 5)
  have h₄ := hsecret (4 : Fin 5)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₀ h₁ h₂ h₃ h₄
  simpa [FiveZeroFalseFinset, and_assoc] using
    And.intro (And.intro (And.intro (And.intro h₀ h₁) h₂) h₃) h₄

/-- The completed-permanent lower bound stated for the existing five-step game state. -/
theorem card_completedFivePathPerfectMatchings_le_fiveZeroFalse
    (guess₀ guess₁ guess₂ guess₃ guess₄ : TenElevenSecret)
    (edge₀ edge₁ edge₂ edge₃ edge₄ : Fin 10 × Fin 11) :
    (PerfectMatchingFinset (completedFivePathAllowed
      (![guess₀, guess₁, guess₂, guess₃, guess₄] : Fin 5 → TenElevenSecret)
      (![edge₀, edge₁, edge₂, edge₃, edge₄] : Fin 5 → Fin 10 × Fin 11))).card ≤
      (FiveZeroFalseFinset guess₀ guess₁ guess₂ guess₃ guess₄
        edge₀ edge₁ edge₂ edge₃ edge₄).card := by
  exact (card_completedPathPerfectMatchings_le_survivors _ _).trans
    (Finset.card_le_card (fiveZeroFalseVectorFinset_tuple_subset
      guess₀ guess₁ guess₂ guess₃ guess₄ edge₀ edge₁ edge₂ edge₃ edge₄))

/--
Safe lower-nine bridge stated purely as a completed-permanent inequality.  It
is stronger as a hypothesis than the survivor inequality, so the injection
above is exactly what makes the implication sound.
-/
theorem tenElevenLowerBoundNine_of_completedPermanent_large
    (completedPermanentLarge :
      ∀ (guesses : Fin 5 → TenElevenSecret)
        (edges : Fin 5 → Fin 10 × Fin 11),
        6370 <
          (PerfectMatchingFinset
            (completedFivePathAllowed guesses edges)).card)
    (tree : TenElevenStrategy 8) (solves : tree.Solves Finset.univ) : False := by
  apply tenElevenLowerBoundNine_of_fiveZeroFalse_large ?_ tree solves
  intro guess₀ guess₁ guess₂ guess₃ guess₄ edge₀ edge₁ edge₂ edge₃ edge₄
  let guesses : Fin 5 → TenElevenSecret :=
    ![guess₀, guess₁, guess₂, guess₃, guess₄]
  let edges : Fin 5 → Fin 10 × Fin 11 :=
    ![edge₀, edge₁, edge₂, edge₃, edge₄]
  have permanentLarge := completedPermanentLarge guesses edges
  have permanentLe := card_completedFivePathPerfectMatchings_le_fiveZeroFalse
    guess₀ guess₁ guess₂ guess₃ guess₄ edge₀ edge₁ edge₂ edge₃ edge₄
  exact permanentLarge.trans_le permanentLe

/-! ## Perfect-matching bridge for the four-response reduction -/

/-- The relation left after four completed queries and four ten-row edge checks. -/
def completedFourPathAllowed
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11)
    (row color : Fin 11) : Prop :=
  (∀ t, color ≠ completeTenElevenSecret (guesses t) row) ∧
    ∀ t, row = (edges t).1.castSucc → color ≠ (edges t).2

/-- The four zero/false constraints expressed directly on ten-row secrets. -/
noncomputable def FourZeroFalseVectorFinset
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11) : Finset TenElevenSecret := by
  classical
  exact Finset.univ.filter fun secret =>
    ∀ t, (∀ i, secret i ≠ guesses t i) ∧ secret (edges t).1 ≠ (edges t).2

@[simp] theorem mem_FourZeroFalseVectorFinset
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11) (secret : TenElevenSecret) :
    secret ∈ FourZeroFalseVectorFinset guesses edges ↔
      ∀ t, (∀ i, secret i ≠ guesses t i) ∧
        secret (edges t).1 ≠ (edges t).2 := by
  classical
  simp [FourZeroFalseVectorFinset]

/-- Restrict a four-path perfect matching to an actual surviving secret. -/
noncomputable def restrictCompletedFourPathMatching
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11) :
    ↥(PerfectMatchingFinset (completedFourPathAllowed guesses edges)) →
      ↥(FourZeroFalseVectorFinset guesses edges) := by
  intro matching
  refine ⟨restrictElevenPermutation matching.1, ?_⟩
  rw [mem_FourZeroFalseVectorFinset]
  intro t
  have allowed := (mem_PerfectMatchingFinset
    (completedFourPathAllowed guesses edges) matching.1).1 matching.2
  constructor
  · intro i
    have avoids := (allowed i.castSucc).1 t
    simpa [restrictElevenPermutation_apply] using avoids
  · have avoids := (allowed (edges t).1.castSucc).2 t rfl
    simpa [restrictElevenPermutation_apply] using avoids

theorem restrictCompletedFourPathMatching_injective
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11) :
    Function.Injective (restrictCompletedFourPathMatching guesses edges) := by
  intro σ τ restricted
  apply Subtype.ext
  apply restrictElevenPermutation_injective
  exact congrArg Subtype.val restricted

/-- The completed four-path permanent is a lower bound for its survivor state. -/
theorem card_completedFourPathPerfectMatchings_le_survivors
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11) :
    (PerfectMatchingFinset (completedFourPathAllowed guesses edges)).card ≤
      (FourZeroFalseVectorFinset guesses edges).card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_le_of_injective
    (restrictCompletedFourPathMatching guesses edges)
    (restrictCompletedFourPathMatching_injective guesses edges)

/-- The vector presentation maps into the four-step state used by the game tree. -/
theorem fourZeroFalseVectorFinset_tuple_subset
    (guess₀ guess₁ guess₂ guess₃ : TenElevenSecret)
    (edge₀ edge₁ edge₂ edge₃ : Fin 10 × Fin 11) :
    FourZeroFalseVectorFinset
        (![guess₀, guess₁, guess₂, guess₃] : Fin 4 → TenElevenSecret)
        (![edge₀, edge₁, edge₂, edge₃] : Fin 4 → Fin 10 × Fin 11) ⊆
      FourZeroFalseFinset guess₀ guess₁ guess₂ guess₃ edge₀ edge₁ edge₂ edge₃ := by
  classical
  intro secret hsecret
  rw [mem_FourZeroFalseVectorFinset] at hsecret
  have h₀ := hsecret (0 : Fin 4)
  have h₁ := hsecret (1 : Fin 4)
  have h₂ := hsecret (2 : Fin 4)
  have h₃ := hsecret (3 : Fin 4)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₀ h₁ h₂ h₃
  simpa [FourZeroFalseFinset, and_assoc] using
    And.intro (And.intro (And.intro h₀ h₁) h₂) h₃

/-- The completed-permanent lower bound for the four-step game state. -/
theorem card_completedFourPathPerfectMatchings_le_fourZeroFalse
    (guess₀ guess₁ guess₂ guess₃ : TenElevenSecret)
    (edge₀ edge₁ edge₂ edge₃ : Fin 10 × Fin 11) :
    (PerfectMatchingFinset (completedFourPathAllowed
      (![guess₀, guess₁, guess₂, guess₃] : Fin 4 → TenElevenSecret)
      (![edge₀, edge₁, edge₂, edge₃] : Fin 4 → Fin 10 × Fin 11))).card ≤
      (FourZeroFalseFinset guess₀ guess₁ guess₂ guess₃
        edge₀ edge₁ edge₂ edge₃).card := by
  exact (card_completedFourPathPerfectMatchings_le_survivors _ _).trans
    (Finset.card_le_card (fourZeroFalseVectorFinset_tuple_subset
      guess₀ guess₁ guess₂ guess₃ edge₀ edge₁ edge₂ edge₃))

/-- Safe lower-nine bridge stated as a universal four-path permanent inequality. -/
theorem tenElevenLowerBoundNine_of_completedFourPermanent_large
    (completedPermanentLarge :
      ∀ (guesses : Fin 4 → TenElevenSecret)
        (edges : Fin 4 → Fin 10 × Fin 11),
        92206 <
          (PerfectMatchingFinset
            (completedFourPathAllowed guesses edges)).card)
    (tree : TenElevenStrategy 8) (solves : tree.Solves Finset.univ) : False := by
  apply tenElevenLowerBoundNine_of_fourZeroFalse_large ?_ tree solves
  intro guess₀ guess₁ guess₂ guess₃ edge₀ edge₁ edge₂ edge₃
  let guesses : Fin 4 → TenElevenSecret :=
    ![guess₀, guess₁, guess₂, guess₃]
  let edges : Fin 4 → Fin 10 × Fin 11 :=
    ![edge₀, edge₁, edge₂, edge₃]
  have permanentLarge := completedPermanentLarge guesses edges
  have permanentLe := card_completedFourPathPerfectMatchings_le_fourZeroFalse
    guess₀ guess₁ guess₂ guess₃ edge₀ edge₁ edge₂ edge₃
  exact permanentLarge.trans_le permanentLe

/-! ## A four-edge marginal reduction -/

/-- The completed graph after four zero answers, before the four checks. -/
def completedFourQueriesAllowed
    (guesses : Fin 4 → TenElevenSecret) (row color : Fin 11) : Prop :=
  ∀ t, color ≠ completeTenElevenSecret (guesses t) row

/-- Query-only perfect matchings that use the edge tested in round `t`. -/
noncomputable def FourPathCheckedEdgeUseFinset
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11) (t : Fin 4) :
    Finset (Equiv.Perm (Fin 11)) := by
  classical
  exact (PerfectMatchingFinset (completedFourQueriesAllowed guesses)).filter
    fun σ => σ (edges t).1.castSucc = (edges t).2

@[simp] theorem mem_FourPathCheckedEdgeUseFinset
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11) (t : Fin 4)
    (σ : Equiv.Perm (Fin 11)) :
    σ ∈ FourPathCheckedEdgeUseFinset guesses edges t ↔
      (∀ row, completedFourQueriesAllowed guesses row (σ row)) ∧
        σ (edges t).1.castSucc = (edges t).2 := by
  classical
  simp [FourPathCheckedEdgeUseFinset]

/--
Every query-only perfect matching either survives all four false checks or
uses at least one of the four checked edges.
-/
theorem queryPerfectMatchings_subset_path_union_checkedEdgeUses
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11) :
    PerfectMatchingFinset (completedFourQueriesAllowed guesses) ⊆
      PerfectMatchingFinset (completedFourPathAllowed guesses edges) ∪
        Finset.univ.biUnion (FourPathCheckedEdgeUseFinset guesses edges) := by
  classical
  intro σ queryMem
  by_cases pathMem : σ ∈
      PerfectMatchingFinset (completedFourPathAllowed guesses edges)
  · exact Finset.mem_union_left _ pathMem
  · apply Finset.mem_union_right
    rw [mem_PerfectMatchingFinset] at queryMem pathMem
    push Not at pathMem
    obtain ⟨row, pathFailure⟩ := pathMem
    have queryAllowed : completedFourQueriesAllowed guesses row (σ row) :=
      queryMem row
    have checkFailure : ¬∀ t,
        row = (edges t).1.castSucc → σ row ≠ (edges t).2 := by
      intro checksAllowed
      exact pathFailure ⟨queryAllowed, checksAllowed⟩
    push Not at checkFailure
    obtain ⟨t, rowEq, colorEq⟩ := checkFailure
    rw [Finset.mem_biUnion]
    refine ⟨t, Finset.mem_univ t, ?_⟩
    rw [mem_FourPathCheckedEdgeUseFinset]
    refine ⟨queryMem, ?_⟩
    simpa [← rowEq] using colorEq

/-- Cardinality union bound for the four checked-edge losses. -/
theorem card_queryPerfectMatchings_le_path_add_checkedEdgeUses
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11) :
    (PerfectMatchingFinset (completedFourQueriesAllowed guesses)).card ≤
      (PerfectMatchingFinset (completedFourPathAllowed guesses edges)).card +
        ∑ t, (FourPathCheckedEdgeUseFinset guesses edges t).card := by
  classical
  let survivors := PerfectMatchingFinset (completedFourPathAllowed guesses edges)
  let losses := Finset.univ.biUnion (FourPathCheckedEdgeUseFinset guesses edges)
  calc
    (PerfectMatchingFinset (completedFourQueriesAllowed guesses)).card ≤
        (survivors ∪ losses).card :=
      Finset.card_le_card
        (queryPerfectMatchings_subset_path_union_checkedEdgeUses guesses edges)
    _ ≤ survivors.card + losses.card := Finset.card_union_le _ _
    _ ≤ survivors.card +
        ∑ t, (FourPathCheckedEdgeUseFinset guesses edges t).card := by
      exact Nat.add_le_add_left Finset.card_biUnion_le survivors.card

/--
If each checked edge occurs in at most one sixth of the query-only perfect
matchings, the four false answers retain more than the four-round capacity.
The numerical margin is seven matchings.
-/
theorem card_completedFourPath_large_of_queryLarge_and_edgeMarginals
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11)
    (queryLarge : 276640 ≤
      (PerfectMatchingFinset (completedFourQueriesAllowed guesses)).card)
    (edgeMarginal : ∀ t,
      6 * (FourPathCheckedEdgeUseFinset guesses edges t).card ≤
        (PerfectMatchingFinset (completedFourQueriesAllowed guesses)).card) :
    92206 <
      (PerfectMatchingFinset (completedFourPathAllowed guesses edges)).card := by
  have cover := card_queryPerfectMatchings_le_path_add_checkedEdgeUses guesses edges
  have sumEdges :
      6 * ∑ t, (FourPathCheckedEdgeUseFinset guesses edges t).card ≤
        4 * (PerfectMatchingFinset
          (completedFourQueriesAllowed guesses)).card := by
    calc
      6 * ∑ t, (FourPathCheckedEdgeUseFinset guesses edges t).card =
          ∑ t, 6 * (FourPathCheckedEdgeUseFinset guesses edges t).card := by
        rw [Finset.mul_sum]
      _ ≤ ∑ _t : Fin 4,
          (PerfectMatchingFinset (completedFourQueriesAllowed guesses)).card :=
        Finset.sum_le_sum fun t _ht => edgeMarginal t
      _ = 4 * (PerfectMatchingFinset
          (completedFourQueriesAllowed guesses)).card := by simp
  omega

/-- End-to-end lower-nine reduction through the query permanent and edge marginals. -/
theorem tenElevenLowerBoundNine_of_queryLarge_and_edgeMarginals
    (queryLarge : ∀ guesses : Fin 4 → TenElevenSecret,
      276640 ≤
        (PerfectMatchingFinset (completedFourQueriesAllowed guesses)).card)
    (edgeMarginal : ∀ (guesses : Fin 4 → TenElevenSecret)
        (edges : Fin 4 → Fin 10 × Fin 11) (t : Fin 4),
      6 * (FourPathCheckedEdgeUseFinset guesses edges t).card ≤
        (PerfectMatchingFinset (completedFourQueriesAllowed guesses)).card)
    (tree : TenElevenStrategy 8) (solves : tree.Solves Finset.univ) : False := by
  apply tenElevenLowerBoundNine_of_completedFourPermanent_large ?_ tree solves
  intro guesses edges
  exact card_completedFourPath_large_of_queryLarge_and_edgeMarginals
    guesses edges (queryLarge guesses) (edgeMarginal guesses edges)

/-! ## Five-regular subrelations and the numerical threshold -/

/-- The number of allowed edges from `rows` to `colors`. -/
noncomputable def bipartiteEdgeCount (allowed : Fin 11 → Fin 11 → Prop)
    (rows colors : Finset (Fin 11)) : Nat := by
  classical
  exact ∑ row ∈ rows, ∑ color ∈ colors, if allowed row color then 1 else 0

/-- Every row and every color has exactly `degree` incident allowed edges. -/
def IsSpanningRegular (degree : Nat) (allowed : Fin 11 → Fin 11 → Prop) : Prop :=
  (∀ row, bipartiteEdgeCount allowed {row} Finset.univ = degree) ∧
    ∀ color, bipartiteEdgeCount allowed Finset.univ {color} = degree

/-- Relation inclusion for bipartite edge relations. -/
def IsSubrelation (smaller larger : Fin 11 → Fin 11 → Prop) : Prop :=
  ∀ ⦃row color⦄, smaller row color → larger row color

/-! ## A collision-free four-cycle switching bound -/

/-- Swap the two rows of a permutation while leaving its colors fixed. -/
noncomputable def swapPermutationRows (σ : Equiv.Perm (Fin 11))
    (row other : Fin 11) : Equiv.Perm (Fin 11) :=
  (Equiv.swap row other).trans σ

@[simp] theorem swapPermutationRows_apply_left
    (σ : Equiv.Perm (Fin 11)) (row other : Fin 11) :
    swapPermutationRows σ row other row = σ other := by
  simp [swapPermutationRows]

@[simp] theorem swapPermutationRows_apply_right
    (σ : Equiv.Perm (Fin 11)) (row other : Fin 11) :
    swapPermutationRows σ row other other = σ row := by
  simp [swapPermutationRows]

@[simp] theorem swapPermutationRows_involutive
    (σ : Equiv.Perm (Fin 11)) (row other : Fin 11) :
    swapPermutationRows (swapPermutationRows σ row other) row other = σ := by
  ext current
  simp [swapPermutationRows]

/-- Colors allowed at one row. -/
noncomputable def rowNeighborFinset (allowed : Fin 11 → Fin 11 → Prop)
    (row : Fin 11) : Finset (Fin 11) := by
  classical
  exact Finset.univ.filter (allowed row)

/-- Rows allowing one color. -/
noncomputable def colorNeighborFinset (allowed : Fin 11 → Fin 11 → Prop)
    (color : Fin 11) : Finset (Fin 11) := by
  classical
  exact Finset.univ.filter fun row => allowed row color

theorem bipartiteEdgeCount_singleton_row
    (allowed : Fin 11 → Fin 11 → Prop) (row : Fin 11) :
    bipartiteEdgeCount allowed {row} Finset.univ =
      (rowNeighborFinset allowed row).card := by
  classical
  simp [bipartiteEdgeCount, rowNeighborFinset]

theorem bipartiteEdgeCount_singleton_color
    (allowed : Fin 11 → Fin 11 → Prop) (color : Fin 11) :
    bipartiteEdgeCount allowed Finset.univ {color} =
      (colorNeighborFinset allowed color).card := by
  classical
  simp only [bipartiteEdgeCount, Finset.sum_singleton]
  rw [Finset.card_eq_sum_ones]
  change (∑ row, if allowed row color then 1 else 0) =
    ∑ row ∈ Finset.univ.filter (fun row => allowed row color), 1
  rw [Finset.sum_filter]

/-- Pull the colors allowed at `row` back through a permutation. -/
noncomputable def permutedRowNeighborFinset
    (allowed : Fin 11 → Fin 11 → Prop) (row : Fin 11)
    (σ : Equiv.Perm (Fin 11)) : Finset (Fin 11) := by
  classical
  exact Finset.univ.filter fun other => allowed row (σ other)

theorem card_permutedRowNeighborFinset
    (allowed : Fin 11 → Fin 11 → Prop) (row : Fin 11)
    (σ : Equiv.Perm (Fin 11)) :
    (permutedRowNeighborFinset allowed row σ).card =
      (rowNeighborFinset allowed row).card := by
  classical
  apply Finset.card_bij (fun other _ => σ other)
  · intro other membership
    simpa [permutedRowNeighborFinset, rowNeighborFinset] using membership
  · intro first _ second _ equal
    exact σ.injective equal
  · intro color membership
    refine ⟨σ.symm color, ?_, by simp⟩
    simpa [permutedRowNeighborFinset, rowNeighborFinset] using membership

/-- Rows at which swapping a matching edge with `row-color` is legal. -/
noncomputable def goodSwitchRowFinset
    (allowed : Fin 11 → Fin 11 → Prop) (row color : Fin 11)
    (σ : Equiv.Perm (Fin 11)) : Finset (Fin 11) := by
  classical
  exact ((colorNeighborFinset allowed color) ∩
    (permutedRowNeighborFinset allowed row σ)).erase row

/--
A matching using an edge of a seven-regular graph has at least two legal
four-cycle switches away from that edge.  The two size-seven neighbor sets
meet in at least three of the eleven rows, one of which is `row` itself.
-/
theorem card_goodSwitchRowFinset_at_least_two
    (allowed : Fin 11 → Fin 11 → Prop)
    (regular : IsSpanningRegular 7 allowed)
    (row color : Fin 11) (σ : Equiv.Perm (Fin 11))
    (edge : allowed row color) (uses : σ row = color) :
    2 ≤ (goodSwitchRowFinset allowed row color σ).card := by
  classical
  have rowCard : (rowNeighborFinset allowed row).card = 7 := by
    rw [← bipartiteEdgeCount_singleton_row]
    exact regular.1 row
  have colorCard : (colorNeighborFinset allowed color).card = 7 := by
    rw [← bipartiteEdgeCount_singleton_color]
    exact regular.2 color
  have permutedCard :
      (permutedRowNeighborFinset allowed row σ).card = 7 := by
    rw [card_permutedRowNeighborFinset, rowCard]
  let both := (colorNeighborFinset allowed color) ∩
    (permutedRowNeighborFinset allowed row σ)
  have unionCard : ((colorNeighborFinset allowed color) ∪
      (permutedRowNeighborFinset allowed row σ)).card ≤ 11 := by
    calc
      _ ≤ (Finset.univ : Finset (Fin 11)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = 11 := by decide
  have bothCard : 3 ≤ both.card := by
    have identity := Finset.card_inter_add_card_union
      (colorNeighborFinset allowed color)
      (permutedRowNeighborFinset allowed row σ)
    dsimp [both]
    omega
  have rowMem : row ∈ both := by
    simp [both, colorNeighborFinset, permutedRowNeighborFinset, edge, uses]
  simp only [goodSwitchRowFinset]
  rw [Finset.card_erase_of_mem rowMem]
  omega

/-- Perfect matchings using a specified allowed edge. -/
noncomputable def regularEdgeUseFinset (allowed : Fin 11 → Fin 11 → Prop)
    (row color : Fin 11) : Finset (Equiv.Perm (Fin 11)) := by
  classical
  exact (PerfectMatchingFinset allowed).filter fun σ => σ row = color

/-- Perfect matchings avoiding a specified edge. -/
noncomputable def regularEdgeAvoidFinset (allowed : Fin 11 → Fin 11 → Prop)
    (row color : Fin 11) : Finset (Equiv.Perm (Fin 11)) := by
  classical
  exact (PerfectMatchingFinset allowed).filter fun σ => σ row ≠ color

@[simp] theorem mem_regularEdgeUseFinset
    (allowed : Fin 11 → Fin 11 → Prop) (row color : Fin 11)
    (σ : Equiv.Perm (Fin 11)) :
    σ ∈ regularEdgeUseFinset allowed row color ↔
      (∀ current, allowed current (σ current)) ∧ σ row = color := by
  classical
  simp [regularEdgeUseFinset]

@[simp] theorem mem_regularEdgeAvoidFinset
    (allowed : Fin 11 → Fin 11 → Prop) (row color : Fin 11)
    (σ : Equiv.Perm (Fin 11)) :
    σ ∈ regularEdgeAvoidFinset allowed row color ↔
      (∀ current, allowed current (σ current)) ∧ σ row ≠ color := by
  classical
  simp [regularEdgeAvoidFinset]

noncomputable def chooseGoodSwitchRows
    (allowed : Fin 11 → Fin 11 → Prop)
    (regular : IsSpanningRegular 7 allowed) (row color : Fin 11)
    (edge : allowed row color)
    (σ : ↥(regularEdgeUseFinset allowed row color)) : Fin 2 ↪
      ↥(goodSwitchRowFinset allowed row color σ.1) := by
  classical
  exact Classical.choice (Function.Embedding.nonempty_of_card_le (by
    simpa using card_goodSwitchRowFinset_at_least_two allowed regular
      row color σ.1 edge
        ((mem_regularEdgeUseFinset allowed row color σ.1).mp σ.2).2))

/-- Switch one of two selected four-cycles away from the specified edge. -/
noncomputable def fourCycleSwitchMap
    (allowed : Fin 11 → Fin 11 → Prop)
    (regular : IsSpanningRegular 7 allowed) (row color : Fin 11)
    (edge : allowed row color) :
    (↥(regularEdgeUseFinset allowed row color) × Fin 2) →
      ↥(regularEdgeAvoidFinset allowed row color) := by
  classical
  intro source
  let σ := source.1.1
  let other :=
    (chooseGoodSwitchRows allowed regular row color edge source.1 source.2).1
  have σMem := (mem_regularEdgeUseFinset allowed row color σ).mp source.1.2
  have otherMem :=
    (chooseGoodSwitchRows allowed regular row color edge source.1 source.2).2
  have otherFacts :
      other ≠ row ∧ allowed other color ∧ allowed row (σ other) := by
    change other ∈ goodSwitchRowFinset allowed row color σ at otherMem
    simpa only [goodSwitchRowFinset, Finset.mem_erase, Finset.mem_inter,
      colorNeighborFinset, permutedRowNeighborFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] using otherMem
  refine ⟨swapPermutationRows σ row other, ?_⟩
  rw [mem_regularEdgeAvoidFinset]
  constructor
  · intro current
    by_cases currentRow : current = row
    · subst current
      simpa [swapPermutationRows] using otherFacts.2.2
    · by_cases currentOther : current = other
      · subst current
        simpa [swapPermutationRows, σMem.2] using otherFacts.2.1
      · simpa [swapPermutationRows,
          Equiv.swap_apply_of_ne_of_ne currentRow currentOther] using σMem.1 current
  · rw [swapPermutationRows_apply_left]
    intro equal
    apply otherFacts.1
    apply σ.injective
    simpa [σMem.2] using equal

/-- The four-cycle switch remembers its unique original matching and row. -/
theorem fourCycleSwitchMap_injective
    (allowed : Fin 11 → Fin 11 → Prop)
    (regular : IsSpanningRegular 7 allowed) (row color : Fin 11)
    (edge : allowed row color) :
    Function.Injective (fourCycleSwitchMap allowed regular row color edge) := by
  classical
  rintro ⟨σ, first⟩ ⟨τ, second⟩ switchedEqual
  let other := (chooseGoodSwitchRows allowed regular row color edge σ first).1
  let another := (chooseGoodSwitchRows allowed regular row color edge τ second).1
  have σMem := (mem_regularEdgeUseFinset allowed row color σ.1).mp σ.2
  have τMem := (mem_regularEdgeUseFinset allowed row color τ.1).mp τ.2
  have switchedValEqual :
      swapPermutationRows σ.1 row other =
        swapPermutationRows τ.1 row another :=
    congrArg Subtype.val switchedEqual
  have otherMaps : swapPermutationRows σ.1 row other other = color := by
    simp [swapPermutationRows, σMem.2]
  have anotherMaps :
      swapPermutationRows τ.1 row another another = color := by
    simp [swapPermutationRows, τMem.2]
  have otherEqual : other = another := by
    apply (swapPermutationRows σ.1 row other).injective
    calc
      swapPermutationRows σ.1 row other other = color := otherMaps
      _ = swapPermutationRows τ.1 row another another := anotherMaps.symm
      _ = swapPermutationRows σ.1 row other another := by rw [switchedValEqual]
  have σEqualsτ : σ.1 = τ.1 := by
    have switchedAgain := congrArg
      (fun permutation => swapPermutationRows permutation row other)
      switchedValEqual
    simpa [otherEqual] using switchedAgain
  have σSubtype : σ = τ := Subtype.ext σEqualsτ
  subst τ
  have indicesEqual : first = second := by
    apply (chooseGoodSwitchRows allowed regular row color edge σ).injective
    apply Subtype.ext
    exact otherEqual
  exact Prod.ext rfl indicesEqual

/-- Every matching using the edge produces two distinct avoiding matchings. -/
theorem twice_card_regularEdgeUse_le_avoid
    (allowed : Fin 11 → Fin 11 → Prop)
    (regular : IsSpanningRegular 7 allowed) (row color : Fin 11)
    (edge : allowed row color) :
    2 * (regularEdgeUseFinset allowed row color).card ≤
      (regularEdgeAvoidFinset allowed row color).card := by
  have cardLe := Fintype.card_le_of_injective
    (fourCycleSwitchMap allowed regular row color edge)
    (fourCycleSwitchMap_injective allowed regular row color edge)
  simpa [Fintype.card_prod, Nat.mul_comm] using cardLe

/-- A fixed edge occurs in at most one third of all perfect matchings. -/
theorem three_mul_card_regularEdgeUse_le_all
    (allowed : Fin 11 → Fin 11 → Prop)
    (regular : IsSpanningRegular 7 allowed) (row color : Fin 11)
    (edge : allowed row color) :
    3 * (regularEdgeUseFinset allowed row color).card ≤
      (PerfectMatchingFinset allowed).card := by
  have switches := twice_card_regularEdgeUse_le_avoid allowed regular row color edge
  have partition := Finset.card_filter_add_card_filter_not
    (s := PerfectMatchingFinset allowed) (fun σ => σ row = color)
  change (regularEdgeUseFinset allowed row color).card +
      (regularEdgeAvoidFinset allowed row color).card =
      (PerfectMatchingFinset allowed).card at partition
  omega

/-- The generic one-third switching theorem at the four-query interface. -/
theorem three_mul_card_fourPathCheckedEdgeUse_le_query
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11)
    (regular : IsSpanningRegular 7 (completedFourQueriesAllowed guesses))
    (t : Fin 4) :
    3 * (FourPathCheckedEdgeUseFinset guesses edges t).card ≤
      (PerfectMatchingFinset (completedFourQueriesAllowed guesses)).card := by
  let row := (edges t).1.castSucc
  let color := (edges t).2
  have useEq : FourPathCheckedEdgeUseFinset guesses edges t =
      regularEdgeUseFinset (completedFourQueriesAllowed guesses) row color := by
    ext σ
    simp [row, color, regularEdgeUseFinset]
  rw [useEq]
  by_cases edgeAllowed : completedFourQueriesAllowed guesses row color
  · exact three_mul_card_regularEdgeUse_le_all
      (completedFourQueriesAllowed guesses) regular row color edgeAllowed
  · have noUse :
        regularEdgeUseFinset (completedFourQueriesAllowed guesses) row color = ∅ := by
      ext σ
      rw [mem_regularEdgeUseFinset]
      constructor
      · rintro ⟨matchingAllowed, uses⟩
        exfalso
        apply edgeAllowed
        simpa [uses] using matchingAllowed row
      · intro impossible
        simp at impossible
    simp [noUse]

/-- A five-factor is a five-regular spanning subrelation. -/
def HasFiveFactor (allowed : Fin 11 → Fin 11 → Prop) : Prop :=
  ∃ regular : Fin 11 → Fin 11 → Prop,
    IsSpanningRegular 5 regular ∧ IsSubrelation regular allowed

/-- A six-factor is a six-regular spanning subrelation. -/
def HasSixFactor (allowed : Fin 11 → Fin 11 → Prop) : Prop :=
  ∃ regular : Fin 11 → Fin 11 → Prop,
    IsSpanningRegular 6 regular ∧ IsSubrelation regular allowed

theorem perfectMatchingFinset_mono {smaller larger : Fin 11 → Fin 11 → Prop}
    (subset : IsSubrelation smaller larger) :
    PerfectMatchingFinset smaller ⊆ PerfectMatchingFinset larger := by
  classical
  intro σ hσ
  rw [mem_PerfectMatchingFinset] at hσ ⊢
  intro row
  exact subset (hσ row)

theorem bipartiteEdgeCount_mono_relation
    {smaller larger : Fin 11 → Fin 11 → Prop}
    (subset : IsSubrelation smaller larger)
    (rows colors : Finset (Fin 11)) :
    bipartiteEdgeCount smaller rows colors ≤
      bipartiteEdgeCount larger rows colors := by
  classical
  simp only [bipartiteEdgeCount]
  apply Finset.sum_le_sum
  intro row _hrow
  apply Finset.sum_le_sum
  intro color _hcolor
  by_cases hsmall : smaller row color
  · simp [hsmall, subset hsmall]
  · simp [hsmall]

theorem no_regular_subrelation_of_color_degree_lt
    (degree : Nat) (allowed : Fin 11 → Fin 11 → Prop) (color : Fin 11)
    (smallDegree :
      bipartiteEdgeCount allowed Finset.univ {color} < degree) :
    ¬∃ regular : Fin 11 → Fin 11 → Prop,
      IsSpanningRegular degree regular ∧ IsSubrelation regular allowed := by
  rintro ⟨regular, spanningRegular, contained⟩
  have monotone := bipartiteEdgeCount_mono_relation contained
    Finset.univ {color}
  rw [spanningRegular.2 color] at monotone
  omega

theorem no_fiveRegular_subrelation_of_color_degree_lt_five
    (allowed : Fin 11 → Fin 11 → Prop) (color : Fin 11)
    (smallDegree :
      bipartiteEdgeCount allowed Finset.univ {color} < 5) :
    ¬∃ regular : Fin 11 → Fin 11 → Prop,
      IsSpanningRegular 5 regular ∧ IsSubrelation regular allowed := by
  rintro ⟨regular, fiveRegular, contained⟩
  have monotone := bipartiteEdgeCount_mono_relation contained
    Finset.univ {color}
  rw [fiveRegular.2 color] at monotone
  omega

/-- The van-der-Waerden arithmetic at degree five forces an integer permanent of 6,832. -/
theorem permanent_five_regular_threshold {permanent : Nat}
    (bound : 5 ^ 11 * Nat.factorial 11 ≤ permanent * 11 ^ 11) :
    6832 ≤ permanent := by
  norm_num [Nat.factorial] at bound ⊢
  omega

/-- The degree-six permanent inequality only forces 50,758 matchings. -/
theorem permanent_six_regular_threshold {permanent : Nat}
    (bound : 6 ^ 11 * Nat.factorial 11 ≤ permanent * 11 ^ 11) :
    50758 ≤ permanent := by
  norm_num [Nat.factorial] at bound ⊢
  omega

/-- The degree-seven permanent inequality forces 276,640 matchings. -/
theorem permanent_seven_regular_threshold {permanent : Nat}
    (bound : 7 ^ 11 * Nat.factorial 11 ≤ permanent * 11 ^ 11) :
    276640 ≤ permanent := by
  norm_num [Nat.factorial] at bound ⊢
  omega

/--
A seven-regular spanning subrelation of a four-path graph proves the desired
survivor inequality once its standard permanent inequality is supplied.
-/
theorem card_fourZeroFalseVector_large_of_sevenRegular
    (guesses : Fin 4 → TenElevenSecret)
    (edges : Fin 4 → Fin 10 × Fin 11)
    (regular : Fin 11 → Fin 11 → Prop)
    (_sevenRegular : IsSpanningRegular 7 regular)
    (contained : IsSubrelation regular (completedFourPathAllowed guesses edges))
    (permanentBound :
      7 ^ 11 * Nat.factorial 11 ≤
        (PerfectMatchingFinset regular).card * 11 ^ 11) :
    92206 < (FourZeroFalseVectorFinset guesses edges).card := by
  have regularLarge : 276640 ≤ (PerfectMatchingFinset regular).card :=
    permanent_seven_regular_threshold permanentBound
  have completedLe : (PerfectMatchingFinset regular).card ≤
      (PerfectMatchingFinset (completedFourPathAllowed guesses edges)).card :=
    Finset.card_le_card (perfectMatchingFinset_mono contained)
  have survivorLe := card_completedFourPathPerfectMatchings_le_survivors guesses edges
  omega

/--
A five-regular spanning subrelation proves the desired survivor inequality
once its standard permanent inequality is supplied.  The permanent theorem is
an explicit premise because it is not currently in Mathlib.
-/
theorem card_fiveZeroFalseVector_large_of_fiveRegular
    (guesses : Fin 5 → TenElevenSecret)
    (edges : Fin 5 → Fin 10 × Fin 11)
    (regular : Fin 11 → Fin 11 → Prop)
    (_fiveRegular : IsSpanningRegular 5 regular)
    (contained : IsSubrelation regular (completedFivePathAllowed guesses edges))
    (permanentBound :
      5 ^ 11 * Nat.factorial 11 ≤
        (PerfectMatchingFinset regular).card * 11 ^ 11) :
    6370 < (FiveZeroFalseVectorFinset guesses edges).card := by
  have regularLarge : 6832 ≤ (PerfectMatchingFinset regular).card :=
    permanent_five_regular_threshold permanentBound
  have completedLe : (PerfectMatchingFinset regular).card ≤
      (PerfectMatchingFinset (completedFivePathAllowed guesses edges)).card :=
    Finset.card_le_card (perfectMatchingFinset_mono contained)
  have survivorLe := card_completedPathPerfectMatchings_le_survivors guesses edges
  omega

/-- The five-regular implication specialized to the survivor state in the lower-nine theorem. -/
theorem card_fiveZeroFalse_large_of_fiveRegular
    (guess₀ guess₁ guess₂ guess₃ guess₄ : TenElevenSecret)
    (edge₀ edge₁ edge₂ edge₃ edge₄ : Fin 10 × Fin 11)
    (regular : Fin 11 → Fin 11 → Prop)
    (fiveRegular : IsSpanningRegular 5 regular)
    (contained : IsSubrelation regular (completedFivePathAllowed
      (![guess₀, guess₁, guess₂, guess₃, guess₄] : Fin 5 → TenElevenSecret)
      (![edge₀, edge₁, edge₂, edge₃, edge₄] : Fin 5 → Fin 10 × Fin 11)))
    (permanentBound :
      5 ^ 11 * Nat.factorial 11 ≤
        (PerfectMatchingFinset regular).card * 11 ^ 11) :
    6370 < (FiveZeroFalseFinset guess₀ guess₁ guess₂ guess₃ guess₄
      edge₀ edge₁ edge₂ edge₃ edge₄).card := by
  have vectorLarge := card_fiveZeroFalseVector_large_of_fiveRegular _ _ regular
    fiveRegular contained permanentBound
  have vectorLe := Finset.card_le_card (fiveZeroFalseVectorFinset_tuple_subset
    guess₀ guess₁ guess₂ guess₃ guess₄ edge₀ edge₁ edge₂ edge₃ edge₄)
  omega

/-! ### A legal degree-one obstruction to the universal five-factor shortcut -/

noncomputable def fiveFactorObstructionPermutation₀ : Equiv.Perm (Fin 11) :=
  Equiv.ofBijective
    (![8, 4, 1, 0, 7, 3, 9, 2, 6, 10, 5] : Fin 11 → Fin 11) (by decide)

noncomputable def fiveFactorObstructionPermutation₁ : Equiv.Perm (Fin 11) :=
  Equiv.ofBijective
    (![3, 6, 10, 1, 2, 9, 0, 4, 7, 8, 5] : Fin 11 → Fin 11) (by decide)

noncomputable def fiveFactorObstructionPermutation₂ : Equiv.Perm (Fin 11) :=
  Equiv.ofBijective
    (![10, 1, 0, 9, 3, 7, 4, 6, 8, 2, 5] : Fin 11 → Fin 11) (by decide)

noncomputable def fiveFactorObstructionPermutation₃ : Equiv.Perm (Fin 11) :=
  Equiv.ofBijective
    (![0, 8, 9, 4, 10, 1, 6, 3, 2, 7, 5] : Fin 11 → Fin 11) (by decide)

noncomputable def fiveFactorObstructionPermutation₄ : Equiv.Perm (Fin 11) :=
  Equiv.ofBijective
    (![7, 3, 4, 6, 1, 8, 2, 0, 10, 9, 5] : Fin 11 → Fin 11) (by decide)

noncomputable def fiveFactorObstructionPermutations :
    Fin 5 → Equiv.Perm (Fin 11) :=
  ![fiveFactorObstructionPermutation₀, fiveFactorObstructionPermutation₁,
    fiveFactorObstructionPermutation₂, fiveFactorObstructionPermutation₃,
    fiveFactorObstructionPermutation₄]

noncomputable def fiveFactorObstructionGuesses : Fin 5 → TenElevenSecret :=
  fun t => restrictElevenPermutation (fiveFactorObstructionPermutations t)

def fiveFactorObstructionEdges : Fin 5 → Fin 10 × Fin 11 :=
  ![(4, 4), (0, 4), (5, 4), (9, 4), (8, 4)]

noncomputable def fiveFactorObstructionSurvivor : Equiv.Perm (Fin 11) :=
  Equiv.ofBijective
    (![1, 0, 2, 3, 5, 10, 7, 8, 9, 6, 4] : Fin 11 → Fin 11) (by decide)

@[simp] theorem complete_fiveFactorObstructionGuess (t : Fin 5) :
    completeTenElevenSecret (fiveFactorObstructionGuesses t) =
      fiveFactorObstructionPermutations t := by
  exact complete_restrictElevenPermutation _

theorem fiveFactorObstruction_color_four_iff (row : Fin 11) :
    completedFivePathAllowed fiveFactorObstructionGuesses
      fiveFactorObstructionEdges row 4 ↔ row = Fin.last 10 := by
  simp only [completedFivePathAllowed, complete_fiveFactorObstructionGuess]
  fin_cases row <;>
    norm_num [fiveFactorObstructionEdges, fiveFactorObstructionPermutations,
      fiveFactorObstructionPermutation₀, fiveFactorObstructionPermutation₁,
      fiveFactorObstructionPermutation₂, fiveFactorObstructionPermutation₃,
      fiveFactorObstructionPermutation₄, Fin.forall_fin_succ] <;>
    decide

theorem fiveFactorObstruction_color_degree_one :
    bipartiteEdgeCount
      (completedFivePathAllowed fiveFactorObstructionGuesses
        fiveFactorObstructionEdges) Finset.univ {4} = 1 := by
  simp only [bipartiteEdgeCount, Finset.sum_singleton]
  simp_rw [fiveFactorObstruction_color_four_iff]
  simp

theorem fiveFactorObstructionSurvivor_mem :
    fiveFactorObstructionSurvivor ∈
      PerfectMatchingFinset
        (completedFivePathAllowed fiveFactorObstructionGuesses
          fiveFactorObstructionEdges) := by
  rw [mem_PerfectMatchingFinset]
  intro row
  simp only [completedFivePathAllowed, complete_fiveFactorObstructionGuess]
  fin_cases row <;>
    norm_num [fiveFactorObstructionSurvivor, fiveFactorObstructionEdges,
      fiveFactorObstructionPermutations, fiveFactorObstructionPermutation₀,
      fiveFactorObstructionPermutation₁, fiveFactorObstructionPermutation₂,
      fiveFactorObstructionPermutation₃, fiveFactorObstructionPermutation₄,
      Fin.forall_fin_succ] <;>
    decide

/-- The degree-one obstruction is a consistent nonempty zero/false state. -/
theorem fiveFactorObstruction_survivors_nonempty :
    (FiveZeroFalseVectorFinset fiveFactorObstructionGuesses
      fiveFactorObstructionEdges).Nonempty := by
  let matching :
      ↥(PerfectMatchingFinset
        (completedFivePathAllowed fiveFactorObstructionGuesses
          fiveFactorObstructionEdges)) :=
    ⟨fiveFactorObstructionSurvivor, fiveFactorObstructionSurvivor_mem⟩
  exact ⟨(restrictCompletedPathMatching _ _ matching).1,
    (restrictCompletedPathMatching _ _ matching).2⟩

/--
Five legal checks can leave a degree-one color in the completed avoidance
graph.  Hence a five-factor does not exist for every five-zero/five-false path.
This is not a counterexample to the survivor inequality.
-/
theorem fiveFactorObstruction_no_fiveRegular :
    ¬∃ regular : Fin 11 → Fin 11 → Prop,
      IsSpanningRegular 5 regular ∧
        IsSubrelation regular
          (completedFivePathAllowed fiveFactorObstructionGuesses
            fiveFactorObstructionEdges) := by
  apply no_fiveRegular_subrelation_of_color_degree_lt_five _ 4
  rw [fiveFactorObstruction_color_degree_one]
  norm_num

/-! ### A legal degree-three obstruction to the universal six-factor shortcut -/

noncomputable def sixFactorObstructionGuesses : Fin 4 → TenElevenSecret :=
  fun t => fiveFactorObstructionGuesses t.castSucc

def sixFactorObstructionEdges : Fin 4 → Fin 10 × Fin 11 :=
  fun t => fiveFactorObstructionEdges t.castSucc

@[simp] theorem complete_sixFactorObstructionGuess (t : Fin 4) :
    completeTenElevenSecret (sixFactorObstructionGuesses t) =
      fiveFactorObstructionPermutations t.castSucc := by
  exact complete_fiveFactorObstructionGuess t.castSucc

theorem sixFactorObstruction_color_four_iff (row : Fin 11) :
    completedFourPathAllowed sixFactorObstructionGuesses
      sixFactorObstructionEdges row 4 ↔
        row = 2 ∨ row = 8 ∨ row = Fin.last 10 := by
  simp only [completedFourPathAllowed, complete_sixFactorObstructionGuess]
  fin_cases row <;>
    norm_num [sixFactorObstructionEdges, fiveFactorObstructionEdges,
      fiveFactorObstructionPermutations, fiveFactorObstructionPermutation₀,
      fiveFactorObstructionPermutation₁, fiveFactorObstructionPermutation₂,
      fiveFactorObstructionPermutation₃, Fin.forall_fin_succ] <;>
    decide

theorem sixFactorObstruction_color_degree_three :
    bipartiteEdgeCount
      (completedFourPathAllowed sixFactorObstructionGuesses
        sixFactorObstructionEdges) Finset.univ {4} = 3 := by
  simp only [bipartiteEdgeCount, Finset.sum_singleton]
  simp_rw [sixFactorObstruction_color_four_iff]
  decide

theorem completedFiveObstruction_sub_completedFourObstruction :
    IsSubrelation
      (completedFivePathAllowed fiveFactorObstructionGuesses
        fiveFactorObstructionEdges)
      (completedFourPathAllowed sixFactorObstructionGuesses
        sixFactorObstructionEdges) := by
  intro row color allowed
  constructor
  · intro t
    exact allowed.1 t.castSucc
  · intro t equalRow
    exact allowed.2 t.castSucc equalRow

/-- The degree-three four-path obstruction is nevertheless a nonempty state. -/
theorem sixFactorObstruction_survivors_nonempty :
    (FourZeroFalseVectorFinset sixFactorObstructionGuesses
      sixFactorObstructionEdges).Nonempty := by
  have matchingMem : fiveFactorObstructionSurvivor ∈
      PerfectMatchingFinset
        (completedFourPathAllowed sixFactorObstructionGuesses
          sixFactorObstructionEdges) :=
    perfectMatchingFinset_mono
      completedFiveObstruction_sub_completedFourObstruction
      fiveFactorObstructionSurvivor_mem
  let matching :
      ↥(PerfectMatchingFinset
        (completedFourPathAllowed sixFactorObstructionGuesses
          sixFactorObstructionEdges)) :=
    ⟨fiveFactorObstructionSurvivor, matchingMem⟩
  exact ⟨(restrictCompletedFourPathMatching _ _ matching).1,
    (restrictCompletedFourPathMatching _ _ matching).2⟩

/-- Four legal checks can destroy every six-factor by concentrating on one color. -/
theorem sixFactorObstruction_no_sixRegular :
    ¬HasSixFactor
      (completedFourPathAllowed sixFactorObstructionGuesses
        sixFactorObstructionEdges) := by
  apply no_regular_subrelation_of_color_degree_lt 6 _ 4
  rw [sixFactorObstruction_color_degree_three]
  norm_num

/-! ## Six-regular defect-cut reduction -/

theorem bipartiteEdgeCount_univ_right
    (allowed : Fin 11 → Fin 11 → Prop)
    (degree : Nat) (regularRows :
      ∀ row, bipartiteEdgeCount allowed {row} Finset.univ = degree)
    (rows : Finset (Fin 11)) :
    bipartiteEdgeCount allowed rows Finset.univ = degree * rows.card := by
  classical
  simp only [bipartiteEdgeCount]
  calc
    (∑ row ∈ rows, ∑ color ∈ Finset.univ,
        if allowed row color then 1 else 0) =
        ∑ row ∈ rows, degree := by
          apply Finset.sum_congr rfl
          intro row _hrow
          simpa [bipartiteEdgeCount] using regularRows row
    _ = degree * rows.card := by simp [Nat.mul_comm]

theorem bipartiteEdgeCount_univ_left
    (allowed : Fin 11 → Fin 11 → Prop)
    (degree : Nat) (regularColors :
      ∀ color, bipartiteEdgeCount allowed Finset.univ {color} = degree)
    (colors : Finset (Fin 11)) :
    bipartiteEdgeCount allowed Finset.univ colors = degree * colors.card := by
  classical
  simp only [bipartiteEdgeCount]
  rw [Finset.sum_comm]
  calc
    (∑ color ∈ colors, ∑ row ∈ Finset.univ,
        if allowed row color then 1 else 0) =
        ∑ color ∈ colors, degree := by
          apply Finset.sum_congr rfl
          intro color _hcolor
          simpa only [bipartiteEdgeCount, Finset.sum_singleton]
            using regularColors color
    _ = degree * colors.card := by simp [Nat.mul_comm]

theorem bipartiteEdgeCount_partition_right
    (allowed : Fin 11 → Fin 11 → Prop)
    (rows colors : Finset (Fin 11)) :
    bipartiteEdgeCount allowed rows Finset.univ =
      bipartiteEdgeCount allowed rows colors +
        bipartiteEdgeCount allowed rows (Finset.univ \ colors) := by
  classical
  simp only [bipartiteEdgeCount]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro row _hrow
  rw [← Finset.sum_sdiff (Finset.subset_univ colors), Nat.add_comm]

theorem bipartiteEdgeCount_mono_rows
    (allowed : Fin 11 → Fin 11 → Prop)
    {small large colors : Finset (Fin 11)} (subset : small ⊆ large) :
    bipartiteEdgeCount allowed small colors ≤
      bipartiteEdgeCount allowed large colors := by
  classical
  simp only [bipartiteEdgeCount]
  exact Finset.sum_le_sum_of_subset_of_nonneg subset (by simp)

/-- Every cut in a six-regular eleven-by-eleven graph contains at least `6s` edges. -/
theorem sixRegular_cut_lower {allowed : Fin 11 → Fin 11 → Prop}
    (regular : IsSpanningRegular 6 allowed)
    (rows colors : Finset (Fin 11)) :
    6 * (rows.card + colors.card - 11) ≤
      bipartiteEdgeCount allowed rows colors := by
  classical
  have rowTotal := bipartiteEdgeCount_univ_right allowed 6 regular.1 rows
  have partition := bipartiteEdgeCount_partition_right allowed rows colors
  have outsideMono := bipartiteEdgeCount_mono_rows allowed
    (colors := Finset.univ \ colors) (Finset.subset_univ rows)
  have colorTotal := bipartiteEdgeCount_univ_left allowed 6 regular.2
    (Finset.univ \ colors)
  have colorCard : (Finset.univ \ colors).card = 11 - colors.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ colors)]
    simp
  have rowsLe : rows.card ≤ 11 := by simpa using rows.card_le_univ
  have colorsLe : colors.card ≤ 11 := by simpa using colors.card_le_univ
  rw [colorTotal, colorCard] at outsideMono
  omega

/-- Every cut in a seven-regular eleven-by-eleven graph contains at least `7s` edges. -/
theorem sevenRegular_cut_lower {allowed : Fin 11 → Fin 11 → Prop}
    (regular : IsSpanningRegular 7 allowed)
    (rows colors : Finset (Fin 11)) :
    7 * (rows.card + colors.card - 11) ≤
      bipartiteEdgeCount allowed rows colors := by
  classical
  have rowTotal := bipartiteEdgeCount_univ_right allowed 7 regular.1 rows
  have partition := bipartiteEdgeCount_partition_right allowed rows colors
  have outsideMono := bipartiteEdgeCount_mono_rows allowed
    (colors := Finset.univ \ colors) (Finset.subset_univ rows)
  have colorTotal := bipartiteEdgeCount_univ_left allowed 7 regular.2
    (Finset.univ \ colors)
  have colorCard : (Finset.univ \ colors).card = 11 - colors.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ colors)]
    simp
  have rowsLe : rows.card ≤ 11 := by simpa using rows.card_le_univ
  have colorsLe : colors.card ≤ 11 := by simpa using colors.card_le_univ
  rw [colorTotal, colorCard] at outsideMono
  omega

/-- The necessary cut inequality inside any five-regular spanning relation. -/
theorem fiveRegular_cut_lower {allowed : Fin 11 → Fin 11 → Prop}
    (regular : IsSpanningRegular 5 allowed)
    (rows colors : Finset (Fin 11)) :
    5 * (rows.card + colors.card - 11) ≤
      bipartiteEdgeCount allowed rows colors := by
  classical
  have rowTotal := bipartiteEdgeCount_univ_right allowed 5 regular.1 rows
  have partition := bipartiteEdgeCount_partition_right allowed rows colors
  have outsideMono := bipartiteEdgeCount_mono_rows allowed
    (colors := Finset.univ \ colors) (Finset.subset_univ rows)
  have colorTotal := bipartiteEdgeCount_univ_left allowed 5 regular.2
    (Finset.univ \ colors)
  have colorCard : (Finset.univ \ colors).card = 11 - colors.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ colors)]
    simp
  have rowsLe : rows.card ≤ 11 := by simpa using rows.card_le_univ
  have colorsLe : colors.card ≤ 11 := by simpa using colors.card_le_univ
  rw [colorTotal, colorCard] at outsideMono
  omega

/-- Delete a relation `deleted` from an allowed relation. -/
def deleteBipartiteEdges (allowed deleted : Fin 11 → Fin 11 → Prop)
    (row color : Fin 11) : Prop :=
  allowed row color ∧ ¬deleted row color

theorem bipartiteEdgeCount_delete_add
    (allowed deleted : Fin 11 → Fin 11 → Prop)
    (deletedAllowed : IsSubrelation deleted allowed)
    (rows colors : Finset (Fin 11)) :
    bipartiteEdgeCount allowed rows colors =
      bipartiteEdgeCount (deleteBipartiteEdges allowed deleted) rows colors +
        bipartiteEdgeCount deleted rows colors := by
  classical
  simp only [bipartiteEdgeCount]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro row _hrow
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro color _hcolor
  by_cases hdeleted : deleted row color
  · have hallowed := deletedAllowed hdeleted
    simp [deleteBipartiteEdges, hdeleted, hallowed]
  · simp [deleteBipartiteEdges, hdeleted]

theorem bipartiteEdgeCount_mono_rectangle
    (allowed : Fin 11 → Fin 11 → Prop)
    (rows colors : Finset (Fin 11)) :
    bipartiteEdgeCount allowed rows colors ≤
      bipartiteEdgeCount allowed Finset.univ Finset.univ := by
  exact (bipartiteEdgeCount_mono_rows allowed (Finset.subset_univ rows)).trans <|
    by
      classical
      simp only [bipartiteEdgeCount]
      apply Finset.sum_le_sum
      intro row _hrow
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ colors) (by simp)

/-- The fixed-size five-factor cut inequality on eleven vertices per side. -/
def FiveFactorCutCondition (allowed : Fin 11 → Fin 11 → Prop) : Prop :=
  ∀ rows colors : Finset (Fin 11),
    5 * (rows.card + colors.card - 11) ≤
      bipartiteEdgeCount allowed rows colors

/-- The fixed-size six-factor cut inequality on eleven vertices per side. -/
def SixFactorCutCondition (allowed : Fin 11 → Fin 11 → Prop) : Prop :=
  ∀ rows colors : Finset (Fin 11),
    6 * (rows.card + colors.card - 11) ≤
      bipartiteEdgeCount allowed rows colors

/-- Every six-factor satisfies the fixed-size bipartite cut inequality. -/
theorem HasSixFactor.cutCondition {allowed : Fin 11 → Fin 11 → Prop}
    (factor : HasSixFactor allowed) : SixFactorCutCondition allowed := by
  obtain ⟨regular, sixRegular, contained⟩ := factor
  intro rows colors
  exact (sixRegular_cut_lower sixRegular rows colors).trans
    (bipartiteEdgeCount_mono_relation contained rows colors)

/-- Every five-factor satisfies the fixed-size bipartite cut inequality. -/
theorem HasFiveFactor.cutCondition {allowed : Fin 11 → Fin 11 → Prop}
    (factor : HasFiveFactor allowed) : FiveFactorCutCondition allowed := by
  obtain ⟨regular, fiveRegular, contained⟩ := factor
  intro rows colors
  exact (fiveRegular_cut_lower fiveRegular rows colors).trans
    (bipartiteEdgeCount_mono_relation contained rows colors)

/--
Failure of the five-factor cut inequality after at most five deletions from a
six-regular graph has a small, concentrated defect witness.
-/
theorem sixRegular_fiveFactorCut_defect
    (allowed deleted : Fin 11 → Fin 11 → Prop)
    (regular : IsSpanningRegular 6 allowed)
    (deletedAllowed : IsSubrelation deleted allowed)
    (atMostFive :
      bipartiteEdgeCount deleted Finset.univ Finset.univ ≤ 5)
    (failure : ¬FiveFactorCutCondition
      (deleteBipartiteEdges allowed deleted)) :
    ∃ (rows colors : Finset (Fin 11)) (s : Nat),
      s = rows.card + colors.card - 11 ∧
      1 ≤ s ∧ s ≤ 4 ∧
      s + 1 ≤ bipartiteEdgeCount deleted rows colors := by
  classical
  rw [FiveFactorCutCondition] at failure
  push Not at failure
  obtain ⟨rows, colors, violates⟩ := failure
  let s := rows.card + colors.card - 11
  have baseLower := sixRegular_cut_lower regular rows colors
  have split := bipartiteEdgeCount_delete_add allowed deleted deletedAllowed rows colors
  have deletedLe := (bipartiteEdgeCount_mono_rectangle deleted rows colors).trans atMostFive
  refine ⟨rows, colors, s, rfl, ?_, ?_, ?_⟩
  · dsimp [s]
    omega
  · dsimp [s]
    omega
  · dsimp [s] at baseLower violates ⊢
    omega

/--
Failure of the six-factor cut inequality after at most four deletions from a
seven-regular graph has a defect witness with excess in `{1,2,3}`.
-/
theorem sevenRegular_sixFactorCut_defect
    (allowed deleted : Fin 11 → Fin 11 → Prop)
    (regular : IsSpanningRegular 7 allowed)
    (deletedAllowed : IsSubrelation deleted allowed)
    (atMostFour :
      bipartiteEdgeCount deleted Finset.univ Finset.univ ≤ 4)
    (failure : ¬SixFactorCutCondition
      (deleteBipartiteEdges allowed deleted)) :
    ∃ (rows colors : Finset (Fin 11)) (s : Nat),
      s = rows.card + colors.card - 11 ∧
      1 ≤ s ∧ s ≤ 3 ∧
      s + 1 ≤ bipartiteEdgeCount deleted rows colors := by
  classical
  rw [SixFactorCutCondition] at failure
  push Not at failure
  obtain ⟨rows, colors, violates⟩ := failure
  let s := rows.card + colors.card - 11
  have baseLower := sevenRegular_cut_lower regular rows colors
  have split := bipartiteEdgeCount_delete_add allowed deleted deletedAllowed rows colors
  have deletedLe := (bipartiteEdgeCount_mono_rectangle deleted rows colors).trans atMostFour
  refine ⟨rows, colors, s, rfl, ?_, ?_, ?_⟩
  · dsimp [s]
    omega
  · dsimp [s]
    omega
  · dsimp [s] at baseLower violates ⊢
    omega

/-- The preceding defect follows from six-factor nonexistence once cut sufficiency is supplied. -/
theorem sevenRegular_no_sixFactor_defect_of_cut_sufficient
    (allowed deleted : Fin 11 → Fin 11 → Prop)
    (regular : IsSpanningRegular 7 allowed)
    (deletedAllowed : IsSubrelation deleted allowed)
    (atMostFour :
      bipartiteEdgeCount deleted Finset.univ Finset.univ ≤ 4)
    (cutSufficient : SixFactorCutCondition
      (deleteBipartiteEdges allowed deleted) →
        HasSixFactor (deleteBipartiteEdges allowed deleted))
    (noFactor : ¬HasSixFactor (deleteBipartiteEdges allowed deleted)) :
    ∃ (rows colors : Finset (Fin 11)) (s : Nat),
      s = rows.card + colors.card - 11 ∧
      1 ≤ s ∧ s ≤ 3 ∧
      s + 1 ≤ bipartiteEdgeCount deleted rows colors := by
  apply sevenRegular_sixFactorCut_defect allowed deleted regular deletedAllowed atMostFour
  intro cutCondition
  exact noFactor (cutSufficient cutCondition)

/--
The defect conclusion from actual nonexistence of a five-factor, conditional
only on the still-unformalized sufficient direction of the exact cut
criterion.  Keeping that direction as an argument prevents the reduction from
silently assuming the desired graph theorem.
-/
theorem sixRegular_no_fiveFactor_defect_of_cut_sufficient
    (allowed deleted : Fin 11 → Fin 11 → Prop)
    (regular : IsSpanningRegular 6 allowed)
    (deletedAllowed : IsSubrelation deleted allowed)
    (atMostFive :
      bipartiteEdgeCount deleted Finset.univ Finset.univ ≤ 5)
    (cutSufficient : FiveFactorCutCondition
      (deleteBipartiteEdges allowed deleted) →
        HasFiveFactor (deleteBipartiteEdges allowed deleted))
    (noFactor : ¬HasFiveFactor (deleteBipartiteEdges allowed deleted)) :
    ∃ (rows colors : Finset (Fin 11)) (s : Nat),
      s = rows.card + colors.card - 11 ∧
      1 ≤ s ∧ s ≤ 4 ∧
      s + 1 ≤ bipartiteEdgeCount deleted rows colors := by
  apply sixRegular_fiveFactorCut_defect allowed deleted regular deletedAllowed atMostFive
  intro cutCondition
  exact noFactor (cutSufficient cutCondition)

end BlackPegExtraCheck
