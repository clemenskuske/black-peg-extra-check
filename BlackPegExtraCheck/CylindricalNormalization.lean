/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

/-!
# Compatible affine normalization on the cylindrical coordinate cycle

This file records the kernel-checked algebra behind the external eight-rook
normalizer.  The normalizer may relabel residual support positions and colors
by

```text
p |-> a*p+s,   c |-> a*c+t       (a != 0 mod 11)
```

with one common multiplier.  Under exactly this compatible action,
displacements `c-p` are relabeled by `d |-> a*d+(t-s)`.

This is not yet the universal `CylindricalFiber` theorem; the remaining bridge
has to identify each concrete residual cylindrical fiber with one of these
enumerated abstract fibers before applying separator transport.
-/

namespace BlackPegExtraCheck

/-- The residual cylindrical coordinate cycle. -/
abbrev Cycle11 := ZMod 11

/-- The affine map `x |-> a*x+t` on the eleven-cycle. -/
def cycleAffineMap (a : Cycle11ˣ) (t x : Cycle11) : Cycle11 :=
  (a : Cycle11) * x + t

/-- A unit affine map is a permutation of the eleven-cycle. -/
def cycleAffineEquiv (a : Cycle11ˣ) (t : Cycle11) : Cycle11 ≃ Cycle11 where
  toFun := cycleAffineMap a t
  invFun y := (a⁻¹ : Cycle11ˣ) * (y - t)
  left_inv := by
    intro x
    calc
      (a⁻¹ : Cycle11ˣ) * (cycleAffineMap a t x - t) =
          ((a⁻¹ : Cycle11ˣ) * (a : Cycle11ˣ) : Cycle11) * x := by
            simp [cycleAffineMap]
      _ = x := by simp
  right_inv := by
    intro y
    calc
      cycleAffineMap a t ((a⁻¹ : Cycle11ˣ) * (y - t)) =
          ((a : Cycle11ˣ) * (a⁻¹ : Cycle11ˣ) : Cycle11) * (y - t) + t := by
            simp [cycleAffineMap]
      _ = y := by simp

@[simp] theorem cycleAffineEquiv_apply
    (a : Cycle11ˣ) (t x : Cycle11) :
    cycleAffineEquiv a t x = cycleAffineMap a t x := rfl

theorem cycleAffineMap_sub
    (a : Cycle11ˣ) (s t c p : Cycle11) :
    cycleAffineMap a t c - cycleAffineMap a s p =
      cycleAffineMap a (t - s) (c - p) := by
  simp [cycleAffineMap]
  ring

/--
Transport a residual row by compatible affine position/color relabeling.
The input row is a total function on the cycle; only its values on the chosen
support are relevant to the abstract fiber.
-/
def compatibleAffineRow
    (a : Cycle11ˣ) (s t : Cycle11) (row : Cycle11 → Cycle11) :
    Cycle11 → Cycle11 :=
  fun position => cycleAffineEquiv a t (row ((cycleAffineEquiv a s).symm position))

@[simp] theorem compatibleAffineRow_apply_image
    (a : Cycle11ˣ) (s t : Cycle11)
    (row : Cycle11 → Cycle11) (position : Cycle11) :
    compatibleAffineRow a s t row (cycleAffineEquiv a s position) =
      cycleAffineEquiv a t (row position) := by
  change cycleAffineEquiv a t
      (row ((cycleAffineEquiv a s).symm (cycleAffineEquiv a s position))) =
    cycleAffineEquiv a t (row position)
  rw [Equiv.symm_apply_apply]

theorem compatibleAffineRow_displacement
    (a : Cycle11ˣ) (s t : Cycle11)
    (row : Cycle11 → Cycle11) (position : Cycle11) :
    compatibleAffineRow a s t row (cycleAffineEquiv a s position) -
        cycleAffineEquiv a s position =
      cycleAffineEquiv a (t - s) (row position - position) := by
  rw [compatibleAffineRow_apply_image]
  simp only [cycleAffineEquiv_apply]
  exact cycleAffineMap_sub a s t (row position) position

/-- Positions in a support whose row value has displacement `d`. -/
def displacementClass
    (support : Finset Cycle11) (row : Cycle11 → Cycle11) (d : Cycle11) :
    Finset Cycle11 :=
  support.filter fun position => row position - position = d

@[simp] theorem mem_displacementClass
    (support : Finset Cycle11) (row : Cycle11 → Cycle11)
    (d position : Cycle11) :
    position ∈ displacementClass support row d ↔
      position ∈ support ∧ row position - position = d := by
  simp [displacementClass]

theorem displacementClass_compatibleAffineRow
    (a : Cycle11ˣ) (s t : Cycle11)
    (support : Finset Cycle11) (row : Cycle11 → Cycle11) (d : Cycle11) :
    displacementClass
        (support.map (cycleAffineEquiv a s).toEmbedding)
        (compatibleAffineRow a s t row)
        (cycleAffineEquiv a (t - s) d) =
      (displacementClass support row d).map
        (cycleAffineEquiv a s).toEmbedding := by
  ext position
  constructor
  · intro member
    rw [mem_displacementClass] at member
    rcases Finset.mem_map.1 member.1 with ⟨preimage, preimage_mem, rfl⟩
    have member_displacement := member.2
    change compatibleAffineRow a s t row (cycleAffineEquiv a s preimage) -
        cycleAffineEquiv a s preimage =
      cycleAffineEquiv a (t - s) d at member_displacement
    rw [compatibleAffineRow_displacement] at member_displacement
    have displacement_eq : row preimage - preimage = d :=
      (cycleAffineEquiv a (t - s)).injective member_displacement
    exact Finset.mem_map.2
      ⟨preimage, by simp [preimage_mem, displacement_eq], rfl⟩
  · intro member
    rcases Finset.mem_map.1 member with ⟨preimage, preimage_mem, rfl⟩
    rw [mem_displacementClass] at preimage_mem
    rw [mem_displacementClass]
    constructor
    · exact Finset.mem_map.2 ⟨preimage, preimage_mem.1, rfl⟩
    · change compatibleAffineRow a s t row (cycleAffineEquiv a s preimage) -
          cycleAffineEquiv a s preimage =
        cycleAffineEquiv a (t - s) d
      rw [compatibleAffineRow_displacement, preimage_mem.2]

theorem displacementClass_card_compatibleAffineRow
    (a : Cycle11ˣ) (s t : Cycle11)
    (support : Finset Cycle11) (row : Cycle11 → Cycle11) (d : Cycle11) :
    (displacementClass
        (support.map (cycleAffineEquiv a s).toEmbedding)
        (compatibleAffineRow a s t row)
        (cycleAffineEquiv a (t - s) d)).card =
      (displacementClass support row d).card := by
  rw [displacementClass_compatibleAffineRow]
  simp

end BlackPegExtraCheck
