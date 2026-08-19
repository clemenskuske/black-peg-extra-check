/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.FiveZeroBridge

/-!
# Exact four-cycle incidence bound

The earlier switching argument selected only two four-cycles per matching.
Here the source contains every legal four-cycle.  The switched output uniquely
determines both the original matching and the switched row, so the reverse
multiplicity is exactly one.  Consequently the total number of legal
four-cycle incidences is at most the number of matchings avoiding the edge.

This is the sharp statement obtainable from four-cycles alone.  The external
seven-regular counterexample in `switching_layer_counterexample.py` shows that
its left side can still be below five times the edge cofactor, so longer cycles
remain necessary for the conjectured one-sixth marginal.
-/

namespace BlackPegExtraCheck

/-- Every legal four-cycle switch, with its matching-dependent row type. -/
noncomputable def AllFourCycleSwitchSource
    (allowed : Fin 11 → Fin 11 → Prop) (row color : Fin 11) :=
  Σ σ : ↥(regularEdgeUseFinset allowed row color),
    ↥(goodSwitchRowFinset allowed row color σ.1)

noncomputable instance allFourCycleSwitchSourceFintype
    (allowed : Fin 11 → Fin 11 → Prop) (row color : Fin 11) :
    Fintype (AllFourCycleSwitchSource allowed row color) :=
  by
    classical
    unfold AllFourCycleSwitchSource
    infer_instance

/-- Switch an arbitrary legal four-cycle away from a specified edge. -/
noncomputable def allFourCycleSwitchMap
    (allowed : Fin 11 → Fin 11 → Prop) (row color : Fin 11) :
    AllFourCycleSwitchSource allowed row color →
      ↥(regularEdgeAvoidFinset allowed row color) := by
  classical
  rintro ⟨σ, selected⟩
  let other := selected.1
  have σMem := (mem_regularEdgeUseFinset allowed row color σ.1).mp σ.2
  have otherFacts :
      other ≠ row ∧ allowed other color ∧ allowed row (σ.1 other) := by
    have otherMem := selected.2
    change other ∈ goodSwitchRowFinset allowed row color σ.1 at otherMem
    simpa only [goodSwitchRowFinset, Finset.mem_erase, Finset.mem_inter,
      colorNeighborFinset, permutedRowNeighborFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] using otherMem
  refine ⟨swapPermutationRows σ.1 row other, ?_⟩
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
    apply σ.1.injective
    simpa [σMem.2] using equal

/-- A switched matching has exactly one four-cycle source. -/
theorem allFourCycleSwitchMap_injective
    (allowed : Fin 11 → Fin 11 → Prop) (row color : Fin 11) :
    Function.Injective (allFourCycleSwitchMap allowed row color) := by
  classical
  rintro ⟨σ, first⟩ ⟨τ, second⟩ switchedEqual
  let other := first.1
  let another := second.1
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
  have selectedEqual : first = second := Subtype.ext otherEqual
  subst second
  rfl

/--
All legal four-cycle incidences inject into the edge-avoiding matchings; this
states the reverse-multiplicity-one count without discarding extra switches.
-/
theorem card_allFourCycleSwitchSource_le_avoid
    (allowed : Fin 11 → Fin 11 → Prop) (row color : Fin 11) :
    Fintype.card (AllFourCycleSwitchSource allowed row color) ≤
      (regularEdgeAvoidFinset allowed row color).card := by
  have cardLe := Fintype.card_le_of_injective
    (allFourCycleSwitchMap allowed row color)
    (allFourCycleSwitchMap_injective allowed row color)
  simpa using cardLe

/-- The same exact incidence bound as an explicit sum over edge-using matchings. -/
theorem sum_card_goodSwitchRowFinset_le_avoid
    (allowed : Fin 11 → Fin 11 → Prop) (row color : Fin 11) :
    (∑ σ ∈ regularEdgeUseFinset allowed row color,
        (goodSwitchRowFinset allowed row color σ).card) ≤
      (regularEdgeAvoidFinset allowed row color).card := by
  have sourceBound := card_allFourCycleSwitchSource_le_avoid allowed row color
  simp only [AllFourCycleSwitchSource, Fintype.card_sigma,
    Fintype.card_coe] at sourceBound
  rw [Finset.sum_subtype
    (p := fun σ => σ ∈ regularEdgeUseFinset allowed row color)
    (regularEdgeUseFinset allowed row color) (fun _ => Iff.rfl)]
  exact sourceBound

end BlackPegExtraCheck
