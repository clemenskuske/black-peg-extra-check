/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.Separator

/-!
# Transporting separator proofs through board symmetries

This file records the kernel-checked part needed by normalized certificate
families: legal position and color relabelings preserve black answers,
checked equality branches, and therefore `Sep`.
-/

namespace BlackPegExtraCheck

namespace TenElevenSymmetry

/-- Relabel positions by `positions` and colors by `colors`. -/
def mapSecret (positions : Equiv.Perm (Fin 10)) (colors : Equiv.Perm (Fin 11))
    (secret : TenElevenSecret) : TenElevenSecret where
  toFun i := colors (secret (positions.symm i))
  inj' := by
    intro i j hij
    exact positions.symm.injective (secret.injective (colors.injective hij))

@[simp] theorem mapSecret_apply
    (positions : Equiv.Perm (Fin 10)) (colors : Equiv.Perm (Fin 11))
    (secret : TenElevenSecret) (i : Fin 10) :
    mapSecret positions colors secret i = colors (secret (positions.symm i)) := rfl

@[simp] theorem mapSecret_symm_apply
    (positions : Equiv.Perm (Fin 10)) (colors : Equiv.Perm (Fin 11))
    (secret : TenElevenSecret) (i : Fin 10) :
    mapSecret positions.symm colors.symm (mapSecret positions colors secret) i =
      secret i := by
  simp

@[simp] theorem mapSecret_apply_symm
    (positions : Equiv.Perm (Fin 10)) (colors : Equiv.Perm (Fin 11))
    (secret : TenElevenSecret) (i : Fin 10) :
    mapSecret positions colors (mapSecret positions.symm colors.symm secret) i =
      secret i := by
  simp

/-- Position/color relabeling as an equivalence on ten-field secrets. -/
def secretEquiv (positions : Equiv.Perm (Fin 10)) (colors : Equiv.Perm (Fin 11)) :
    TenElevenSecret ≃ TenElevenSecret where
  toFun := mapSecret positions colors
  invFun := mapSecret positions.symm colors.symm
  left_inv := by
    intro secret
    apply Function.Embedding.ext
    intro i
    simp
  right_inv := by
    intro secret
    apply Function.Embedding.ext
    intro i
    simp

@[simp] theorem secretEquiv_apply
    (positions : Equiv.Perm (Fin 10)) (colors : Equiv.Perm (Fin 11))
    (secret : TenElevenSecret) :
    secretEquiv positions colors secret = mapSecret positions colors secret := rfl

@[simp] theorem secretEquiv_symm_apply
    (positions : Equiv.Perm (Fin 10)) (colors : Equiv.Perm (Fin 11))
    (secret : TenElevenSecret) :
    (secretEquiv positions colors).symm secret =
      mapSecret positions.symm colors.symm secret := rfl

theorem matchSet_map
    (positions : Equiv.Perm (Fin 10)) (colors : Equiv.Perm (Fin 11))
    (guess secret : TenElevenSecret) :
    MatchSet (mapSecret positions colors guess) (mapSecret positions colors secret) =
      (MatchSet guess secret).map positions.toEmbedding := by
  ext i
  constructor
  · intro hi
    rw [MatchSet] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [MatchSet]
    refine Finset.mem_map.2 ⟨positions.symm i, ?_, ?_⟩
    · simpa [MatchSet] using colors.injective hi
    · simp
  · intro hi
    rw [MatchSet] at hi ⊢
    rcases Finset.mem_map.1 hi with ⟨j, hj, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    simp [hj]

theorem blackAnswer_map
    (positions : Equiv.Perm (Fin 10)) (colors : Equiv.Perm (Fin 11))
    (guess secret : TenElevenSecret) :
    tenElevenBlackAnswer (mapSecret positions colors guess)
        (mapSecret positions colors secret) =
      tenElevenBlackAnswer guess secret := by
  apply Fin.ext
  simp [tenElevenBlackAnswer, matchSet_map]

def mapCandidates (positions : Equiv.Perm (Fin 10)) (colors : Equiv.Perm (Fin 11))
    (candidates : Finset TenElevenSecret) : Finset TenElevenSecret :=
  candidates.map (secretEquiv positions colors).toEmbedding

@[simp] theorem mem_mapCandidates
    (positions : Equiv.Perm (Fin 10)) (colors : Equiv.Perm (Fin 11))
    (candidates : Finset TenElevenSecret) (secret : TenElevenSecret) :
    secret ∈ mapCandidates positions colors candidates ↔
      mapSecret positions.symm colors.symm secret ∈ candidates := by
  constructor
  · intro h
    rcases Finset.mem_map.1 h with ⟨pre, hpre, hpre_eq⟩
    have pre_eq : mapSecret positions.symm colors.symm secret = pre := by
      rw [← hpre_eq]
      apply Function.Embedding.ext
      intro i
      simp
    simpa [pre_eq] using hpre
  · intro h
    rw [mapCandidates]
    refine Finset.mem_map.2
      ⟨mapSecret positions.symm colors.symm secret, h, ?_⟩
    apply Function.Embedding.ext
    intro i
    simp

def mapEdge (positions : Equiv.Perm (Fin 10)) (colors : Equiv.Perm (Fin 11)) :
    Fin 10 × Fin 11 → Fin 10 × Fin 11 :=
  fun edge => (positions edge.1, colors edge.2)

theorem checkedBranch_map
    (positions : Equiv.Perm (Fin 10)) (colors : Equiv.Perm (Fin 11))
    (candidates : Finset TenElevenSecret) (guess : TenElevenSecret)
    (black : Fin 11) (edge : Fin 10 × Fin 11) (bit : Bool) :
    checkedBranch (mapCandidates positions colors candidates)
        (mapSecret positions colors guess) black (mapEdge positions colors edge) bit =
      mapCandidates positions colors
        (checkedBranch candidates guess black edge bit) := by
  ext secret
  constructor
  · intro h
    rw [mem_checkedBranch] at h
    rw [mem_mapCandidates] at h
    rw [mem_mapCandidates, mem_checkedBranch]
    refine ⟨h.1, ?_, ?_⟩
    · calc
        tenElevenBlackAnswer guess
            (mapSecret positions.symm colors.symm secret) =
          tenElevenBlackAnswer
            (mapSecret positions.symm colors.symm
              (mapSecret positions colors guess))
            (mapSecret positions.symm colors.symm secret) := by
              congr 1
              apply Function.Embedding.ext
              intro i
              simp
        _ = tenElevenBlackAnswer (mapSecret positions colors guess) secret :=
              blackAnswer_map positions.symm colors.symm
                (mapSecret positions colors guess) secret
        _ = black := h.2.1
    · have hedge :
          decide ((colors.symm (secret (positions edge.1))) = edge.2) =
            decide (secret (positions edge.1) = colors edge.2) := by
          by_cases hleft :
              colors.symm (secret (positions edge.1)) = edge.2
          · have hright : secret (positions edge.1) = colors edge.2 := by
              rw [← hleft]
              simp
            simp [hright]
          · have hright : secret (positions edge.1) ≠ colors edge.2 := by
              intro hright
              exact hleft (colors.symm_apply_eq.2 hright)
            simp [hleft, hright]
      change decide (colors.symm (secret (positions edge.1)) = edge.2) = bit
      exact hedge.trans h.2.2
  · intro h
    rw [mem_mapCandidates, mem_checkedBranch] at h
    rw [mem_checkedBranch, mem_mapCandidates]
    refine ⟨h.1, ?_, ?_⟩
    · calc
        tenElevenBlackAnswer (mapSecret positions colors guess) secret =
          tenElevenBlackAnswer (mapSecret positions colors guess)
            (mapSecret positions colors
              (mapSecret positions.symm colors.symm secret)) := by
              congr 1
              apply Function.Embedding.ext
              intro i
              simp
        _ = tenElevenBlackAnswer guess
            (mapSecret positions.symm colors.symm secret) := by
              rw [blackAnswer_map positions colors guess
                (mapSecret positions.symm colors.symm secret)]
        _ = black := h.2.1
    · have hedge :
          decide (secret (positions edge.1) = colors edge.2) =
            decide ((colors.symm (secret (positions edge.1))) = edge.2) := by
          by_cases hright : secret (positions edge.1) = colors edge.2
          · have hleft :
                colors.symm (secret (positions edge.1)) = edge.2 :=
              colors.symm_apply_eq.2 hright
            simp [hright]
          · have hleft :
                colors.symm (secret (positions edge.1)) ≠ edge.2 := by
              intro hleft
              exact hright (colors.symm_apply_eq.1 hleft)
            simp [hleft, hright]
      change decide (secret (positions edge.1) = colors edge.2) = bit
      exact hedge.trans h.2.2

theorem Sep.map
    (positions : Equiv.Perm (Fin 10)) (colors : Equiv.Perm (Fin 11))
    {depth : Nat} {candidates : Finset TenElevenSecret}
    (separates : Sep depth candidates) :
    Sep depth (mapCandidates positions colors candidates) := by
  induction depth generalizing candidates with
  | zero =>
      rw [sep_zero_iff] at separates ⊢
      simpa [mapCandidates] using separates
  | succ depth ih =>
      rw [sep_succ_iff] at separates ⊢
      obtain ⟨guess, hguess⟩ := separates
      refine ⟨mapSecret positions colors guess, ?_⟩
      intro black
      obtain ⟨edge, yes, no⟩ := hguess black
      refine ⟨mapEdge positions colors edge, ?_, ?_⟩
      · rw [checkedBranch_map]
        exact ih yes
      · rw [checkedBranch_map]
        exact ih no

theorem Sep.unmap
    (positions : Equiv.Perm (Fin 10)) (colors : Equiv.Perm (Fin 11))
    {depth : Nat} {candidates : Finset TenElevenSecret}
    (separates : Sep depth
      (mapCandidates positions.symm colors.symm candidates)) :
    Sep depth candidates := by
  have transported := Sep.map positions colors separates
  convert transported using 1
  ext secret
  rw [mem_mapCandidates, mem_mapCandidates]
  have hsecret :
      mapSecret positions colors
        (mapSecret positions.symm colors.symm secret) = secret := by
    apply Function.Embedding.ext
    intro i
    simp
  simp [hsecret]

end TenElevenSymmetry

end BlackPegExtraCheck
