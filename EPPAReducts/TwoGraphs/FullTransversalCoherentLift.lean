import EPPAReducts.TwoGraphs.FullTransversalLift

/-!
# The canonical full-transversal lift preserves composition

The unique extension of each full-transversal automorphism, within
the combined permutation/matrix group, is *coherent*. We prove
closure of the chosen lift family, its identity, and its composition
law without selecting arbitrary matrix representatives.

The block-inflation homomorphism and abstract coherentization step
are separate future obligations.
-/

namespace EPPAReducts.TwoGraphs

variable {X : Type}

/-- A chosen combined-index/matrix action extends the permutation
p of the full transversal whose valuations are χ. -/
def IsCombinedFullTransversalLift
    (χ : X → Valuation X) (p : Equiv.Perm X)
    (g : Equiv.Perm (ValuationVertex X)) : Prop :=
  (∃ F : X → X → Bool,
    IsSymmetricBoolMatrix F ∧ g = matrixIndexPerm p F) ∧
  ∀ x, g (x, valuationClass (χ x)) =
    (p x, valuationClass (χ (p x)))

/-- The identity index permutation acts trivially on quotient valuations. -/
theorem indexPermVertex_refl :
    indexPermVertex (Equiv.refl X) =
      Equiv.refl (ValuationVertex X) := by
  apply Equiv.ext
  rintro ⟨x, q⟩
  induction q using Quotient.inductionOn with
  | _ a =>
    change (x, valuationClass (reindexValuation (Equiv.refl X) a)) =
      (x, valuationClass a)
    rfl

/-- The zero-matrix action with the identity index permutation is the
identity permutation of the entire valuation witness. -/
theorem matrixIndexPerm_refl_zero :
    matrixIndexPerm (Equiv.refl X) (zeroMatrix X) =
      Equiv.refl (ValuationVertex X) := by
  unfold matrixIndexPerm
  rw [rowShiftPerm_zero, indexPermVertex_refl]
  rfl

/-- The identity permutation on the full transversal has the identity
combined action as its extension. -/
theorem fullTransversal_identity_isLift
    (χ : X → Valuation X) :
    IsCombinedFullTransversalLift χ (Equiv.refl X)
      (Equiv.refl (ValuationVertex X)) := by
  refine ⟨⟨zeroMatrix X, zeroMatrix_symmetric, ?_⟩, ?_⟩
  · exact (matrixIndexPerm_refl_zero (X := X)).symm
  · intro x
    rfl

/-- Combined full-transversal lifts are closed under composition;
this uses the already proved *semidirect*, not direct-product,
matrix/index multiplication law. -/
theorem combinedFullTransversalLift_trans
    (χ : X → Valuation X)
    (p q : Equiv.Perm X)
    (gp gq : Equiv.Perm (ValuationVertex X))
    (hp : IsCombinedFullTransversalLift χ p gp)
    (hq : IsCombinedFullTransversalLift χ q gq) :
    IsCombinedFullTransversalLift χ (p.trans q) (gp.trans gq) := by
  rcases hp with ⟨⟨F, hF, rfl⟩, hmapP⟩
  rcases hq with ⟨⟨G, hG, rfl⟩, hmapQ⟩
  let H := xorMatrix (reindexMatrix p.symm G) F
  have hH : IsSymmetricBoolMatrix H := by
    exact xorMatrix_symmetric _ _
      (reindexMatrix_symmetric p.symm G hG) hF
  refine ⟨⟨H, hH, ?_⟩, ?_⟩
  · exact matrixIndexPerm_trans p q F G
  · intro x
    change
      (matrixIndexPerm q G)
        ((matrixIndexPerm p F) (x, valuationClass (χ x))) =
        (q (p x), valuationClass (χ (q (p x))))
    rw [hmapP x, hmapQ (p x)]

/-- A combined full-transversal extension is unique as a
permutation, even if represented by different Boolean matrices. -/
theorem combinedFullTransversalLift_unique
    (χ : X → Valuation X)
    (p : Equiv.Perm X)
    (g₁ g₂ : Equiv.Perm (ValuationVertex X))
    (h₁ : IsCombinedFullTransversalLift χ p g₁)
    (h₂ : IsCombinedFullTransversalLift χ p g₂) :
    g₁ = g₂ := by
  rcases h₁ with ⟨⟨F, hF, rfl⟩, hmapF⟩
  rcases h₂ with ⟨⟨G, hG, rfl⟩, hmapG⟩
  exact matrixIndexPerm_eq_of_full_transversal
    p p F G (fun x => valuationClass (χ x))
      (fun x => (hmapF x).trans (hmapG x).symm)

/-- Pick the unique combined-action lift of an automorphism of the
full transversal. The choice is unique *as an action*, hence independent
of how we constructed a Boolean matrix representative. -/
noncomputable def canonicalFullTransversalLift
    [Fintype X] [DecidableEq X] [Nonempty X]
    (χ : X → Valuation X)
    (p : Equiv.Perm X)
    (hp : PreservesFullTransversal χ p) :
    Equiv.Perm (ValuationVertex X) :=
  Classical.choose (existsUnique_fullTransversal_combinedLift χ p hp)

/-- The chosen canonical lift really is a combined action extending p. -/
theorem canonicalFullTransversalLift_spec
    [Fintype X] [DecidableEq X] [Nonempty X]
    (χ : X → Valuation X)
    (p : Equiv.Perm X)
    (hp : PreservesFullTransversal χ p) :
    IsCombinedFullTransversalLift χ p
      (canonicalFullTransversalLift χ p hp) := by
  exact (Classical.choose_spec
    (existsUnique_fullTransversal_combinedLift χ p hp)).1

/-- Canonical extension maps the identity to the identity. -/
theorem canonicalFullTransversalLift_refl
    [Fintype X] [DecidableEq X] [Nonempty X]
    (χ : X → Valuation X) :
    canonicalFullTransversalLift χ (Equiv.refl X)
        (preservesFullTransversal_refl χ) =
      Equiv.refl (ValuationVertex X) := by
  exact combinedFullTransversalLift_unique χ (Equiv.refl X)
    _ _ (canonicalFullTransversalLift_spec χ _ _)
    (fullTransversal_identity_isLift χ)

/-- **Coherence on a full transversal:** the unique chosen extensions
respect composition for every two automorphisms of the induced
full-transversal two-graph. -/
theorem canonicalFullTransversalLift_trans
    [Fintype X] [DecidableEq X] [Nonempty X]
    (χ : X → Valuation X)
    (p q : Equiv.Perm X)
    (hp : PreservesFullTransversal χ p)
    (hq : PreservesFullTransversal χ q) :
    (canonicalFullTransversalLift χ p hp).trans
      (canonicalFullTransversalLift χ q hq) =
      canonicalFullTransversalLift χ (p.trans q)
        (preservesFullTransversal_trans χ p q hp hq) := by
  apply combinedFullTransversalLift_unique χ (p.trans q)
  · exact combinedFullTransversalLift_trans χ p q _ _
      (canonicalFullTransversalLift_spec χ p hp)
      (canonicalFullTransversalLift_spec χ q hq)
  · exact canonicalFullTransversalLift_spec χ (p.trans q)
      (preservesFullTransversal_trans χ p q hp hq)

end EPPAReducts.TwoGraphs
