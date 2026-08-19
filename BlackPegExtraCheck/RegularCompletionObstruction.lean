/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.FiveZeroBridge

/-!
# A regular-completion obstruction

An overlap support need not extend to a simple four-regular forbidden graph on
the same vertices.  The first three rows and colors form `K_3,3`; the other
eight vertices support four cyclic factors.  Four completed query permutations
generate this support, with one factor repeated on the `K_3,3` block.
-/

namespace BlackPegExtraCheck

def nonextendableQueryFunction : Fin 4 → Fin 11 → Fin 11 :=
  ![
    (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : Fin 11 → Fin 11),
    (![1, 2, 0, 4, 5, 6, 7, 8, 9, 10, 3] : Fin 11 → Fin 11),
    (![2, 0, 1, 5, 6, 7, 8, 9, 10, 3, 4] : Fin 11 → Fin 11),
    (![0, 1, 2, 6, 7, 8, 9, 10, 3, 4, 5] : Fin 11 → Fin 11)
  ]

theorem nonextendableQueryFunction_bijective (t : Fin 4) :
    Function.Bijective (nonextendableQueryFunction t) := by
  fin_cases t <;> decide

noncomputable def nonextendableQueryPermutation (t : Fin 4) : Equiv.Perm (Fin 11) :=
  Equiv.ofBijective (nonextendableQueryFunction t)
    (nonextendableQueryFunction_bijective t)

def nonextendableQueryForbidden (row color : Fin 11) : Prop :=
  ∃ t, nonextendableQueryFunction t row = color

def nonextendableFirstColors : Finset (Fin 11) := {0, 1, 2}

def nonextendableSaturatedRows : Fin 11 → Finset (Fin 11) :=
  ![
    ∅, ∅, ∅,
    {3, 8, 9, 10}, {3, 4, 9, 10}, {3, 4, 5, 10}, {3, 4, 5, 6},
    {4, 5, 6, 7}, {5, 6, 7, 8}, {6, 7, 8, 9}, {7, 8, 9, 10}
  ]

theorem nonextendableFirstColors_forbidden :
    ∀ color ∈ nonextendableFirstColors,
      nonextendableQueryForbidden 0 color := by
  intro color membership
  fin_cases color <;> simp [nonextendableFirstColors] at membership
  all_goals first
    | exact ⟨0, by decide⟩
    | exact ⟨1, by decide⟩
    | exact ⟨2, by decide⟩

theorem nonextendableSaturatedRows_card :
    ∀ color, color ∉ nonextendableFirstColors →
      (nonextendableSaturatedRows color).card = 4 := by
  decide

theorem nonextendableSaturatedRows_forbidden :
    ∀ color row, row ∈ nonextendableSaturatedRows color →
      nonextendableQueryForbidden row color := by
  intro color row membership
  fin_cases color <;> fin_cases row <;>
    simp [nonextendableSaturatedRows] at membership
  all_goals first
    | exact ⟨0, by decide⟩
    | exact ⟨1, by decide⟩
    | exact ⟨2, by decide⟩
    | exact ⟨3, by decide⟩

theorem row_zero_not_mem_nonextendableSaturatedRows :
    ∀ color, (0 : Fin 11) ∉ nonextendableSaturatedRows color := by
  decide

/--
The support of these four legal completed queries has no simple four-regular
superrelation on the same eleven-by-eleven vertex set.
-/
theorem nonextendableQueryForbidden_no_fourRegular_superrelation :
    ¬∃ regular : Fin 11 → Fin 11 → Prop,
      IsSpanningRegular 4 regular ∧
        IsSubrelation nonextendableQueryForbidden regular := by
  classical
  rintro ⟨regular, regularDegree, contained⟩
  let regularRow := rowNeighborFinset regular 0
  have rowSubset : nonextendableFirstColors ⊆ regularRow := by
    intro color membership
    simp only [regularRow, rowNeighborFinset,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact contained (nonextendableFirstColors_forbidden color membership)
  have firstColorsCard : nonextendableFirstColors.card = 3 := by decide
  have regularRowCard : regularRow.card = 4 := by
    rw [← bipartiteEdgeCount_singleton_row]
    exact regularDegree.1 0
  have extra : ∃ color, color ∈ regularRow ∧
      color ∉ nonextendableFirstColors := by
    by_contra noExtra
    push Not at noExtra
    have reverse : regularRow ⊆ nonextendableFirstColors := by
      intro color membership
      exact noExtra color membership
    have cards := Finset.card_le_card reverse
    rw [firstColorsCard, regularRowCard] at cards
    omega
  obtain ⟨color, colorRegular, colorNotForbidden⟩ := extra
  let regularColor := colorNeighborFinset regular color
  have colorSubset : nonextendableSaturatedRows color ⊆ regularColor := by
    intro row membership
    simp only [regularColor, colorNeighborFinset,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact contained (nonextendableSaturatedRows_forbidden color row membership)
  have saturatedRowsCard : (nonextendableSaturatedRows color).card = 4 :=
    nonextendableSaturatedRows_card color colorNotForbidden
  have regularColorCard : regularColor.card = 4 := by
    rw [← bipartiteEdgeCount_singleton_color]
    exact regularDegree.2 color
  have rowZeroNotForbidden : (0 : Fin 11) ∉
      nonextendableSaturatedRows color :=
    row_zero_not_mem_nonextendableSaturatedRows color
  have rowZeroRegular : (0 : Fin 11) ∈ regularColor := by
    simpa [regularRow, regularColor, rowNeighborFinset,
      colorNeighborFinset] using colorRegular
  have insertedSubset : insert (0 : Fin 11)
      (nonextendableSaturatedRows color) ⊆ regularColor := by
    intro row membership
    rw [Finset.mem_insert] at membership
    rcases membership with rfl | membership
    · exact rowZeroRegular
    · exact colorSubset membership
  have insertedCard := Finset.card_le_card insertedSubset
  rw [Finset.card_insert_of_notMem rowZeroNotForbidden,
    saturatedRowsCard, regularColorCard] at insertedCard
  omega

end BlackPegExtraCheck
