/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.FiveZeroBridge
import Mathlib.Combinatorics.Hall.Basic

/-!
# The exact edge-disjoint completed-query class

Every simple seven-regular relation on eleven rows and eleven colors is the
avoidance graph of four edge-disjoint completed queries.  Thus the remaining
one-sixth marginal conjecture on the edge-disjoint query class is exactly a
claim about all simple seven-regular bipartite graphs of this size, not a
smaller game-specific subclass.

The proof is structural.  Hall's theorem supplies a perfect matching in every
positive regular bipartite relation.  Removing it lowers both degrees by one;
four iterations factor the four-regular complement into four permutations.
-/

namespace BlackPegExtraCheck

@[simp] theorem mem_rowNeighborFinset_iff
    (allowed : Fin 11 → Fin 11 → Prop) (row color : Fin 11) :
    color ∈ rowNeighborFinset allowed row ↔ allowed row color := by
  classical
  simp [rowNeighborFinset]

@[simp] theorem mem_colorNeighborFinset_iff
    (allowed : Fin 11 → Fin 11 → Prop) (row color : Fin 11) :
    row ∈ colorNeighborFinset allowed color ↔ allowed row color := by
  classical
  simp [colorNeighborFinset]

noncomputable def rowsNeighborFinset
    (allowed : Fin 11 → Fin 11 → Prop) (rows : Finset (Fin 11)) :
    Finset (Fin 11) := by
  classical
  exact Finset.univ.filter fun color => ∃ row ∈ rows, allowed row color

theorem bipartiteEdgeCount_rows_neighbors
    (allowed : Fin 11 → Fin 11 → Prop) (rows : Finset (Fin 11)) :
    bipartiteEdgeCount allowed rows (rowsNeighborFinset allowed rows) =
      bipartiteEdgeCount allowed rows Finset.univ := by
  classical
  simp only [bipartiteEdgeCount]
  apply Finset.sum_congr rfl
  intro row rowMem
  apply Finset.sum_subset (Finset.subset_univ _)
  intro color _colorUniv colorNotNeighbor
  have notAllowed : ¬allowed row color := by
    intro edge
    apply colorNotNeighbor
    simp only [rowsNeighborFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨row, rowMem, edge⟩
  simp [notAllowed]

/-- A positive spanning-regular bipartite relation has a perfect matching. -/
theorem exists_permutation_of_spanningRegular
    (degree : Nat) (allowed : Fin 11 → Fin 11 → Prop)
    (positive : 0 < degree) (regular : IsSpanningRegular degree allowed) :
    ∃ σ : Equiv.Perm (Fin 11), ∀ row, allowed row (σ row) := by
  classical
  have hall : ∀ rows : Finset (Fin 11),
      rows.card ≤ (rowsNeighborFinset allowed rows).card := by
    intro rows
    have rowTotal := bipartiteEdgeCount_univ_right
      allowed degree regular.1 rows
    have colorTotal := bipartiteEdgeCount_univ_left
      allowed degree regular.2 (rowsNeighborFinset allowed rows)
    have mono := bipartiteEdgeCount_mono_rows allowed
      (colors := rowsNeighborFinset allowed rows) (Finset.subset_univ rows)
    rw [bipartiteEdgeCount_rows_neighbors, rowTotal, colorTotal] at mono
    exact Nat.le_of_mul_le_mul_left mono positive
  let neighbors := fun row => rowNeighborFinset allowed row
  obtain ⟨f, injective, matching⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' neighbors).mp (by
      intro rows
      calc
        rows.card ≤ (rowsNeighborFinset allowed rows).card := hall rows
        _ = (rows.biUnion neighbors).card := by
          congr 1
          apply Finset.ext
          intro color
          simp [rowsNeighborFinset, neighbors, rowNeighborFinset])
  have matchingAllowed : ∀ row, allowed row (f row) := by
    intro row
    simpa [neighbors, rowNeighborFinset] using matching row
  have bijective : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨injective, rfl⟩
  exact ⟨Equiv.ofBijective f bijective, matchingAllowed⟩

/-- Remove the edges of one permutation from a relation. -/
def deletePermutationEdges (allowed : Fin 11 → Fin 11 → Prop)
    (σ : Equiv.Perm (Fin 11)) (row color : Fin 11) : Prop :=
  allowed row color ∧ σ row ≠ color

/-- Removing a contained perfect matching lowers a regular degree by one. -/
theorem spanningRegular_deletePermutationEdges
    (degree : Nat) (allowed : Fin 11 → Fin 11 → Prop)
    (σ : Equiv.Perm (Fin 11)) (positive : 0 < degree)
    (regular : IsSpanningRegular degree allowed)
    (matching : ∀ row, allowed row (σ row)) :
    IsSpanningRegular (degree - 1) (deletePermutationEdges allowed σ) := by
  classical
  let chosen : Fin 11 → Fin 11 → Prop := fun row color => σ row = color
  have chosenAllowed : IsSubrelation chosen allowed := by
    intro row color equality
    simpa [chosen, equality] using matching row
  have deleteEq : deleteBipartiteEdges allowed chosen =
      deletePermutationEdges allowed σ := by
    funext row color
    apply propext
    simp [deleteBipartiteEdges, deletePermutationEdges, chosen]
  constructor
  · intro row
    have split := bipartiteEdgeCount_delete_add
      allowed chosen chosenAllowed {row} Finset.univ
    rw [deleteEq, regular.1 row] at split
    have chosenOne : bipartiteEdgeCount chosen {row} Finset.univ = 1 := by
      simp only [bipartiteEdgeCount, Finset.sum_singleton, chosen]
      rw [Finset.sum_eq_single (σ row)]
      · simp
      · intro color _colorMem colorNe
        simp [Ne.symm colorNe]
      · simp
    rw [chosenOne] at split
    omega
  · intro color
    have split := bipartiteEdgeCount_delete_add
      allowed chosen chosenAllowed Finset.univ {color}
    rw [deleteEq, regular.2 color] at split
    have chosenOne : bipartiteEdgeCount chosen Finset.univ {color} = 1 := by
      simp only [bipartiteEdgeCount, Finset.sum_singleton, chosen]
      rw [Finset.sum_eq_single (σ.symm color)]
      · simp
      · intro row _rowMem rowNe
        have mapsNe : σ row ≠ color := by
          intro maps
          apply rowNe
          apply σ.injective
          simpa using maps
        simp [mapsNe]
      · simp
    rw [chosenOne] at split
    omega

/-- A four-regular relation is the disjoint union of four permutations. -/
theorem fourRegular_factorization
    (forbidden : Fin 11 → Fin 11 → Prop)
    (regular : IsSpanningRegular 4 forbidden) :
    ∃ factors : Fin 4 → Equiv.Perm (Fin 11),
      ∀ row color, forbidden row color ↔ ∃ t, factors t row = color := by
  classical
  obtain ⟨σ₀, h₀⟩ := exists_permutation_of_spanningRegular 4 forbidden (by omega) regular
  let forbidden₁ := deletePermutationEdges forbidden σ₀
  have regular₁ : IsSpanningRegular 3 forbidden₁ := by
    simpa [forbidden₁] using
      spanningRegular_deletePermutationEdges 4 forbidden σ₀ (by omega) regular h₀
  obtain ⟨σ₁, h₁⟩ :=
    exists_permutation_of_spanningRegular 3 forbidden₁ (by omega) regular₁
  let forbidden₂ := deletePermutationEdges forbidden₁ σ₁
  have regular₂ : IsSpanningRegular 2 forbidden₂ := by
    simpa [forbidden₂] using
      spanningRegular_deletePermutationEdges 3 forbidden₁ σ₁ (by omega) regular₁ h₁
  obtain ⟨σ₂, h₂⟩ :=
    exists_permutation_of_spanningRegular 2 forbidden₂ (by omega) regular₂
  let forbidden₃ := deletePermutationEdges forbidden₂ σ₂
  have regular₃ : IsSpanningRegular 1 forbidden₃ := by
    simpa [forbidden₃] using
      spanningRegular_deletePermutationEdges 2 forbidden₂ σ₂ (by omega) regular₂ h₂
  obtain ⟨σ₃, h₃⟩ :=
    exists_permutation_of_spanningRegular 1 forbidden₃ (by omega) regular₃
  let factors : Fin 4 → Equiv.Perm (Fin 11) := ![σ₀, σ₁, σ₂, σ₃]
  refine ⟨factors, ?_⟩
  intro row color
  constructor
  · intro edge
    by_cases first : σ₀ row = color
    · exact ⟨0, by simpa [factors]⟩
    · have edge₁ : forbidden₁ row color := ⟨edge, first⟩
      by_cases second : σ₁ row = color
      · exact ⟨1, by simpa [factors]⟩
      · have edge₂ : forbidden₂ row color := ⟨edge₁, second⟩
        by_cases third : σ₂ row = color
        · exact ⟨2, by simpa [factors]⟩
        · have edge₃ : forbidden₃ row color := ⟨edge₂, third⟩
          have rowCard :
              (rowNeighborFinset forbidden₃ row).card = 1 := by
            rw [← bipartiteEdgeCount_singleton_row]
            exact regular₃.1 row
          have colorMem : color ∈ rowNeighborFinset forbidden₃ row := by
            simpa [rowNeighborFinset] using edge₃
          have factorMem : σ₃ row ∈ rowNeighborFinset forbidden₃ row := by
            simpa [rowNeighborFinset] using h₃ row
          have equality : color = σ₃ row :=
            (Finset.card_le_one.mp (by omega)) color colorMem (σ₃ row) factorMem
          exact ⟨3, by simp [factors, equality]⟩
  · rintro ⟨t, rfl⟩
    fin_cases t
    · simpa [factors] using h₀ row
    · simpa [factors] using (h₁ row).1
    · simpa [factors] using (h₂ row).1.1
    · simpa [factors] using (h₃ row).1.1.1

def complementRelation (allowed : Fin 11 → Fin 11 → Prop)
    (row color : Fin 11) : Prop :=
  ¬allowed row color

theorem spanningRegular_complement_seven_to_four
    (allowed : Fin 11 → Fin 11 → Prop)
    (regular : IsSpanningRegular 7 allowed) :
    IsSpanningRegular 4 (complementRelation allowed) := by
  classical
  constructor
  · intro row
    rw [bipartiteEdgeCount_singleton_row]
    have partition : rowNeighborFinset (complementRelation allowed) row =
        Finset.univ \ rowNeighborFinset allowed row := by
      ext color
      simp [complementRelation]
    rw [partition, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    rw [← bipartiteEdgeCount_singleton_row, regular.1 row]
    decide
  · intro color
    rw [bipartiteEdgeCount_singleton_color]
    have partition : colorNeighborFinset (complementRelation allowed) color =
        Finset.univ \ colorNeighborFinset allowed color := by
      ext row
      simp [complementRelation]
    rw [partition, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    rw [← bipartiteEdgeCount_singleton_color, regular.2 color]
    decide

/--
Every seven-regular graph is exactly the query-only graph of four legal,
edge-disjoint completed queries.
-/
theorem sevenRegular_eq_completedFourQueriesAllowed
    (allowed : Fin 11 → Fin 11 → Prop)
    (regular : IsSpanningRegular 7 allowed) :
    ∃ guesses : Fin 4 → TenElevenSecret,
      completedFourQueriesAllowed guesses = allowed := by
  classical
  obtain ⟨factors, factorization⟩ := fourRegular_factorization
    (complementRelation allowed)
    (spanningRegular_complement_seven_to_four allowed regular)
  let guesses : Fin 4 → TenElevenSecret :=
    fun t => restrictElevenPermutation (factors t)
  refine ⟨guesses, ?_⟩
  funext row color
  apply propext
  simp only [completedFourQueriesAllowed, guesses,
    complete_restrictElevenPermutation]
  constructor
  · intro avoids
    by_contra forbidden
    obtain ⟨t, equality⟩ := (factorization row color).1 forbidden
    exact avoids t equality.symm
  · intro edge t equality
    exact (factorization row color).2 ⟨t, equality.symm⟩ edge

end BlackPegExtraCheck
