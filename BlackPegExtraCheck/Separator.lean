/-
Copyright (c) 2026 Clemens Kuske. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clemens Kuske, OpenAI Codex
-/
import BlackPegExtraCheck.TenFieldsElevenColors
import Mathlib.Data.Finset.Fold

/-!
# Exact separator predicates and finite certificates

This file gives the exact recursive separator predicate for the ten-field,
eleven-color game.  Queries and checked edges are legal by construction:
queries have type `Fin 10 ↪ Fin 11`, and a checked edge has type
`Fin 10 × Fin 11` and may depend on the observed black response.

`SeparatorCertificate` is a finite proof-producing tree.  Internal nodes
contain a legal query, one checked edge for each black class, and references
to the two children.  A leaf names the sole secret it permits.  The executable
checker is proved sound for `Sep`, and both `Sep` and certificates are
monotone under taking subsets of the candidate state.
-/

namespace BlackPegExtraCheck

/-- One legal black class followed by one legal coordinate-check answer. -/
def checkedBranch (candidates : Finset TenElevenSecret)
    (guess : TenElevenSecret) (black : Fin 11)
    (edge : Fin 10 × Fin 11) (bit : Bool) : Finset TenElevenSecret :=
  candidates.filter fun secret =>
    tenElevenBlackAnswer guess secret = black ∧
      decide (secret edge.1 = edge.2) = bit

@[simp] theorem mem_checkedBranch (candidates : Finset TenElevenSecret)
    (guess : TenElevenSecret) (black : Fin 11)
    (edge : Fin 10 × Fin 11) (bit : Bool) (secret : TenElevenSecret) :
    secret ∈ checkedBranch candidates guess black edge bit ↔
      secret ∈ candidates ∧ tenElevenBlackAnswer guess secret = black ∧
        decide (secret edge.1 = edge.2) = bit := by
  simp [checkedBranch]

theorem checkedBranch_mono {smaller larger : Finset TenElevenSecret}
    (subset : smaller ⊆ larger) (guess : TenElevenSecret) (black : Fin 11)
    (edge : Fin 10 × Fin 11) (bit : Bool) :
    checkedBranch smaller guess black edge bit ⊆
      checkedBranch larger guess black edge bit := by
  intro secret hsecret
  rw [mem_checkedBranch] at hsecret ⊢
  exact ⟨subset hsecret.1, hsecret.2⟩

theorem checkedBranch_eq_answerBranch (candidates : Finset TenElevenSecret)
    (guess : TenElevenSecret) (check : Fin 11 → Fin 10 × Fin 11)
    (black : Fin 11) (bit : Bool) :
    checkedBranch candidates guess black (check black) bit =
      TenElevenRelaxedStrategy.answerBranch candidates guess
        (fun response secret =>
          decide (secret (check response).1 = (check response).2)) black bit := by
  classical
  ext secret
  simp [checkedBranch, TenElevenRelaxedStrategy.answerBranch,
    TenElevenRelaxedStrategy.blackBranch, and_assoc]

/-!
The quantifier order is the game timing: choose a query, observe `black`, then
choose an edge, observe its Boolean answer, and continue separately in the two
children.
-/

/-- Exact recursive separator predicate for legal adaptive strategies. -/
noncomputable def Sep : Nat → Finset TenElevenSecret → Prop
  | 0, candidates => candidates.card ≤ 1
  | depth + 1, candidates =>
      ∃ guess : TenElevenSecret, ∀ black : Fin 11,
        ∃ edge : Fin 10 × Fin 11,
          Sep depth (checkedBranch candidates guess black edge true) ∧
          Sep depth (checkedBranch candidates guess black edge false)

@[simp] theorem sep_zero_iff (candidates : Finset TenElevenSecret) :
    Sep 0 candidates ↔ candidates.card ≤ 1 := Iff.rfl

@[simp] theorem sep_succ_iff (depth : Nat)
    (candidates : Finset TenElevenSecret) :
    Sep (depth + 1) candidates ↔
      ∃ guess : TenElevenSecret, ∀ black : Fin 11,
        ∃ edge : Fin 10 × Fin 11,
          Sep depth (checkedBranch candidates guess black edge true) ∧
          Sep depth (checkedBranch candidates guess black edge false) := Iff.rfl

/-- Separator solvability is preserved when candidates are removed. -/
theorem Sep.mono {depth : Nat} {smaller larger : Finset TenElevenSecret}
    (subset : smaller ⊆ larger) (separates : Sep depth larger) :
    Sep depth smaller := by
  induction depth generalizing smaller larger with
  | zero =>
      exact (Finset.card_le_card subset).trans separates
  | succ depth ih =>
      rw [sep_succ_iff] at separates ⊢
      obtain ⟨guess, separates⟩ := separates
      refine ⟨guess, ?_⟩
      intro black
      obtain ⟨edge, yes, no⟩ := separates black
      refine ⟨edge, ?_, ?_⟩
      · exact ih (checkedBranch_mono subset guess black edge true) yes
      · exact ih (checkedBranch_mono subset guess black edge false) no

/-! ## Finite certificates -/

/--
A finite legal separator certificate.  The two Boolean child references may
depend on the black class through `next`.
-/
inductive SeparatorCertificate : Nat → Type
  | leaf (secret : TenElevenSecret) : SeparatorCertificate 0
  | node {depth : Nat}
      (guess : TenElevenSecret)
      (check : Fin 11 → Fin 10 × Fin 11)
      (next : Fin 11 → Bool → SeparatorCertificate depth) :
      SeparatorCertificate (depth + 1)

namespace SeparatorCertificate

/-- Executable universal quantification over a finite set. -/
def finsetAll {α : Type*} (items : Finset α) (predicate : α → Bool) : Bool :=
  items.fold (· && ·) true predicate

@[simp] theorem finsetAll_eq_true {α : Type*} (items : Finset α)
    (predicate : α → Bool) :
    finsetAll items predicate = true ↔
      ∀ item ∈ items, predicate item = true := by
  classical
  induction items using Finset.induction_on with
  | empty => simp [finsetAll]
  | @insert item items notMem ih =>
      rw [finsetAll, Finset.fold_insert notMem, Bool.and_eq_true]
      change predicate item = true ∧ finsetAll items predicate = true ↔ _
      rw [ih]
      simp

/-- Propositional meaning of a separator certificate on a candidate state. -/
def Certifies : {depth : Nat} →
    SeparatorCertificate depth → Finset TenElevenSecret → Prop
  | 0, .leaf expected, candidates => ∀ secret ∈ candidates, secret = expected
  | _ + 1, .node guess check next, candidates =>
      ∀ black bit,
        (next black bit).Certifies
          (checkedBranch candidates guess black (check black) bit)

/-- A certificate's propositional meaning implies the exact separator predicate. -/
theorem certifies_sep {depth : Nat} (certificate : SeparatorCertificate depth)
    (candidates : Finset TenElevenSecret)
    (certifies : certificate.Certifies candidates) : Sep depth candidates := by
  induction certificate generalizing candidates with
  | leaf expected =>
      rw [sep_zero_iff, Finset.card_le_one]
      intro first hfirst second hsecond
      exact (certifies first hfirst).trans (certifies second hsecond).symm
  | @node depth guess check next ih =>
      rw [sep_succ_iff]
      refine ⟨guess, ?_⟩
      intro black
      refine ⟨check black, ?_, ?_⟩
      · exact ih black true _ (certifies black true)
      · exact ih black false _ (certifies black false)

/-- Certificate validity is preserved when candidates are removed. -/
theorem Certifies.mono {depth : Nat} {certificate : SeparatorCertificate depth}
    {smaller larger : Finset TenElevenSecret} (subset : smaller ⊆ larger)
    (certifies : certificate.Certifies larger) : certificate.Certifies smaller := by
  induction certificate generalizing smaller larger with
  | leaf expected =>
      intro secret hsecret
      exact certifies secret (subset hsecret)
  | @node depth guess check next ih =>
      intro black bit
      exact ih black bit (checkedBranch_mono subset guess black (check black) bit)
        (certifies black bit)

/-- A decidable Boolean checker for a finite certificate. -/
def check : {depth : Nat} →
    SeparatorCertificate depth → Finset TenElevenSecret → Bool
  | 0, .leaf expected, candidates =>
      finsetAll candidates fun secret => decide (secret = expected)
  | _ + 1, .node guess edge next, candidates =>
      finsetAll (Finset.univ : Finset (Fin 11)) fun black =>
        finsetAll (Finset.univ : Finset Bool) fun bit =>
          (next black bit).check
            (checkedBranch candidates guess black (edge black) bit)

theorem check_eq_true_iff_certifies {depth : Nat}
    (certificate : SeparatorCertificate depth)
    (candidates : Finset TenElevenSecret) :
    certificate.check candidates = true ↔ certificate.Certifies candidates := by
  induction certificate generalizing candidates with
  | leaf expected =>
      simp [check, Certifies]
  | @node depth guess edge next ih =>
      simp only [check, finsetAll_eq_true, Finset.mem_univ,
        true_implies, Certifies]
      exact forall_congr' fun black => forall_congr' fun bit => ih black bit _

/-- Every accepted finite certificate is a proof of the exact separator predicate. -/
theorem check_sound {depth : Nat} (certificate : SeparatorCertificate depth)
    (candidates : Finset TenElevenSecret)
    (accepted : certificate.check candidates = true) : Sep depth candidates :=
  certificate.certifies_sep candidates
    ((certificate.check_eq_true_iff_certifies candidates).1 accepted)

/-- An accepted certificate remains accepted after candidates are removed. -/
theorem check_mono {depth : Nat} (certificate : SeparatorCertificate depth)
    {smaller larger : Finset TenElevenSecret} (subset : smaller ⊆ larger)
    (accepted : certificate.check larger = true) :
    certificate.check smaller = true := by
  rw [certificate.check_eq_true_iff_certifies smaller]
  exact Certifies.mono subset
    ((certificate.check_eq_true_iff_certifies larger).1 accepted)

end SeparatorCertificate

/-! ## Correspondence with the existing legal strategy trees -/

theorem sep_of_strategy {depth : Nat} (tree : TenElevenStrategy depth)
    (candidates : Finset TenElevenSecret) (solves : tree.Solves candidates) :
    Sep depth candidates := by
  induction tree generalizing candidates with
  | leaf => exact solves
  | @node depth guess check next ih =>
      rw [sep_succ_iff]
      refine ⟨guess, ?_⟩
      intro black
      refine ⟨check black, ?_, ?_⟩
      · have branchSolves := solves black true
        rw [← checkedBranch_eq_answerBranch candidates guess check black true] at branchSolves
        exact ih black true _ branchSolves
      · have branchSolves := solves black false
        rw [← checkedBranch_eq_answerBranch candidates guess check black false] at branchSolves
        exact ih black false _ branchSolves

/-- Every separator witness can be assembled into an existing legal strategy tree. -/
theorem exists_strategy_of_sep {depth : Nat} (candidates : Finset TenElevenSecret)
    (separates : Sep depth candidates) :
    ∃ tree : TenElevenStrategy depth, tree.Solves candidates := by
  induction depth generalizing candidates with
  | zero =>
      exact ⟨.leaf, separates⟩
  | succ depth ih =>
      rw [sep_succ_iff] at separates
      obtain ⟨guess, separates⟩ := separates
      choose check children using separates
      have yesExists : ∀ black, ∃ tree : TenElevenStrategy depth,
          tree.Solves (checkedBranch candidates guess black (check black) true) :=
        fun black => ih _ (children black).1
      have noExists : ∀ black, ∃ tree : TenElevenStrategy depth,
          tree.Solves (checkedBranch candidates guess black (check black) false) :=
        fun black => ih _ (children black).2
      choose yesTree yesSolves using yesExists
      choose noTree noSolves using noExists
      let next : Fin 11 → Bool → TenElevenStrategy depth := fun black bit =>
        if bit then yesTree black else noTree black
      refine ⟨.node guess check next, ?_⟩
      intro black bit
      rw [← checkedBranch_eq_answerBranch candidates guess check black bit]
      cases bit
      · exact noSolves black
      · exact yesSolves black

/-- `Sep` is exactly existence of a legal adaptive strategy tree of that depth. -/
theorem sep_iff_exists_strategy (depth : Nat) (candidates : Finset TenElevenSecret) :
    Sep depth candidates ↔
      ∃ tree : TenElevenStrategy depth, tree.Solves candidates := by
  constructor
  · intro separates
    exact exists_strategy_of_sep candidates separates
  · rintro ⟨tree, solves⟩
    exact sep_of_strategy tree candidates solves

end BlackPegExtraCheck
