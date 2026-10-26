import EPPAReducts.TwoGraphs.CombinedBlockActionLaws

/-!
# Homomorphic inflated lifts of full transversals

A full transversal has a unique combined-action extension of each induced
automorphism.  Package that extension as a faithful combined-action class
and inflate it through marked block coordinates.

The resulting automorphism of C_X extends the correct action on the
inflated full transversal; its identity and composition laws are literal.
The remaining conjugation to an arbitrary transversal in C_X and abstract
coherentisation are separate obligations.
-/

namespace EPPAReducts.TwoGraphs

/-- Represent the already proved canonical full-transversal lift as
combined index/matrix data, using one of its symmetric matrices. -/
noncomputable def canonicalFullTransversalActionData
    {D : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    (χ : D → Valuation D) (p : Equiv.Perm D)
    (hp : PreservesFullTransversal χ p) : CombinedActionData D := by
  classical
  let h := (canonicalFullTransversalLift_spec χ p hp).1
  exact {
    indexPerm := p
    matrix := Classical.choose h
    symmetric := (Classical.choose_spec h).1
  }

/-- The chosen data acts as the canonical full-transversal lift. -/
theorem canonicalFullTransversalActionData_spec
    {D : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    (χ : D → Valuation D) (p : Equiv.Perm D)
    (hp : PreservesFullTransversal χ p) :
    (canonicalFullTransversalActionData χ p hp).action =
      canonicalFullTransversalLift χ p hp := by
  change matrixIndexPerm p
      (Classical.choose (canonicalFullTransversalLift_spec χ p hp).1) =
        canonicalFullTransversalLift χ p hp
  exact (Classical.choose_spec
    (canonicalFullTransversalLift_spec χ p hp).1).2.symm

/-- Canonical full-transversal extension as a faithful action class. -/
noncomputable def canonicalFullTransversalActionClass
    {D : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    (χ : D → Valuation D) (p : Equiv.Perm D)
    (hp : PreservesFullTransversal χ p) : CombinedActionClass D :=
  Quotient.mk (combinedActionSetoid D)
    (canonicalFullTransversalActionData χ p hp)

/-- Faithful-class action agrees with the previously audited canonical lift. -/
theorem canonicalFullTransversalActionClass_spec
    {D : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    (χ : D → Valuation D) (p : Equiv.Perm D)
    (hp : PreservesFullTransversal χ p) :
    combinedActionClassPerm (canonicalFullTransversalActionClass χ p hp) =
      canonicalFullTransversalLift χ p hp := by
  exact canonicalFullTransversalActionData_spec χ p hp

theorem canonicalFullTransversalActionClass_identity
    {D : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    (χ : D → Valuation D) :
    combinedActionClassPerm
      (canonicalFullTransversalActionClass χ (Equiv.refl D)
        (preservesFullTransversal_refl χ)) =
      Equiv.refl (ValuationVertex D) := by
  rw [canonicalFullTransversalActionClass_spec]
  exact canonicalFullTransversalLift_refl χ

theorem canonicalFullTransversalActionClass_trans
    {D : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    (χ : D → Valuation D)
    (p q : Equiv.Perm D)
    (hp : PreservesFullTransversal χ p)
    (hq : PreservesFullTransversal χ q) :
    (combinedActionClassPerm (canonicalFullTransversalActionClass χ p hp)).trans
      (combinedActionClassPerm (canonicalFullTransversalActionClass χ q hq)) =
    combinedActionClassPerm
      (canonicalFullTransversalActionClass χ (p.trans q)
        (preservesFullTransversal_trans χ p q hp hq)) := by
  simpa only [canonicalFullTransversalActionClass_spec] using
    canonicalFullTransversalLift_trans χ p q hp hq

/-- Every faithful combined-action class is an actual automorphism of
the approved valuation two-graph. -/
theorem combinedActionClassPerm_isTwoGraphAutomorphism
    {X : Type} [DecidableEq (ValuationVertex X)]
    (g : CombinedActionClass X) :
    HumanTargets.IsTwoGraphAutomorphism (valuationTwoGraph X)
      (combinedActionClassPerm g) := by
  induction g using Quotient.inductionOn with
  | _ a =>
    exact matrixIndexPerm_isTwoGraphAutomorphism
      a.indexPerm a.matrix a.symmetric

/-- The full-transversal section on D, inflated to automorphisms of C_X. -/
noncomputable def BlockCoordinates.inflatedCanonicalFullTransversalLift
    {D X : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    (B : BlockCoordinates D X)
    (χ : D → Valuation D) (p : Equiv.Perm D)
    (hp : PreservesFullTransversal χ p) :
    Equiv.Perm (ValuationVertex X) :=
  combinedActionClassPerm
    (B.inflateCombinedActionClass
      (canonicalFullTransversalActionClass χ p hp))

/-- Inflated lifts preserve the actual two-graph relation. -/
theorem BlockCoordinates.inflatedCanonicalFullTransversalLift_isAutomorphism
    {D X : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    [DecidableEq (ValuationVertex X)]
    (B : BlockCoordinates D X)
    (χ : D → Valuation D) (p : Equiv.Perm D)
    (hp : PreservesFullTransversal χ p) :
    HumanTargets.IsTwoGraphAutomorphism (valuationTwoGraph X)
      (B.inflatedCanonicalFullTransversalLift χ p hp) := by
  exact combinedActionClassPerm_isTwoGraphAutomorphism _

/-- Inflated canonical lifts preserve identity. -/
theorem BlockCoordinates.inflatedCanonicalFullTransversalLift_identity
    {D X : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    (B : BlockCoordinates D X) (χ : D → Valuation D) :
    B.inflatedCanonicalFullTransversalLift χ (Equiv.refl D)
      (preservesFullTransversal_refl χ) =
        Equiv.refl (ValuationVertex X) := by
  exact B.inflateCombinedActionClass_identity
    (canonicalFullTransversalActionClass χ (Equiv.refl D)
      (preservesFullTransversal_refl χ))
    (canonicalFullTransversalActionClass_identity χ)

/-- Inflated canonical lifts preserve composition. -/
theorem BlockCoordinates.inflatedCanonicalFullTransversalLift_trans
    {D X : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    (B : BlockCoordinates D X) (χ : D → Valuation D)
    (p q : Equiv.Perm D)
    (hp : PreservesFullTransversal χ p)
    (hq : PreservesFullTransversal χ q) :
    (B.inflatedCanonicalFullTransversalLift χ p hp).trans
      (B.inflatedCanonicalFullTransversalLift χ q hq) =
    B.inflatedCanonicalFullTransversalLift χ (p.trans q)
      (preservesFullTransversal_trans χ p q hp hq) := by
  exact (B.inflateCombinedActionClass_trans
    (canonicalFullTransversalActionClass χ p hp)
    (canonicalFullTransversalActionClass χ q hq)
    (canonicalFullTransversalActionClass χ (p.trans q)
      (preservesFullTransversal_trans χ p q hp hq))
    (canonicalFullTransversalActionClass_trans χ p q hp hq).symm).symm

/-- Each inflated lift acts on the marked embedded full transversal
by exactly the automorphism prescribed on its D-coordinates. -/
theorem BlockCoordinates.inflatedCanonicalFullTransversalLift_marked
    {D X : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    (B : BlockCoordinates D X) (χ : D → Valuation D)
    (p : Equiv.Perm D) (hp : PreservesFullTransversal χ p)
    (d : D) :
    B.inflatedCanonicalFullTransversalLift χ p hp
        (B.inflateValuationVertex (d, valuationClass (χ d))) =
      B.inflateValuationVertex
        (p d, valuationClass (χ (p d))) := by
  have heq := B.inflateValuationVertex_combinedActionClass
    (canonicalFullTransversalActionClass χ p hp)
    (d, valuationClass (χ d))
  rw [canonicalFullTransversalActionClass_spec] at heq
  exact heq.symm.trans (congrArg B.inflateValuationVertex
    ((canonicalFullTransversalLift_spec χ p hp).2 d))

end EPPAReducts.TwoGraphs
