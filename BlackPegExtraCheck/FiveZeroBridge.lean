/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.TenFieldsElevenColors
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

No converse to the five-factor cut criterion and no permanent inequality are
assumed globally here.  The theorem using the permanent bound takes that
inequality as an explicit premise.
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

/-- A five-factor is a five-regular spanning subrelation. -/
def HasFiveFactor (allowed : Fin 11 → Fin 11 → Prop) : Prop :=
  ∃ regular : Fin 11 → Fin 11 → Prop,
    IsSpanningRegular 5 regular ∧ IsSubrelation regular allowed

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
