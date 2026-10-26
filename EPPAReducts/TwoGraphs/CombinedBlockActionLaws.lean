import EPPAReducts.TwoGraphs.CombinedBlockAction

/-!
# Identity and composition for block-inflated combined actions

The quotient of symmetric-matrix/index action data is identified with its
faithful image in permutations of valuation vertices.  Without choosing
any presentation of a quotient class, the block inflation sends the
identity to the identity and respects the actual permutation composition
law.  This supplies the homomorphic algebra for the future subgroup lift.
-/

namespace EPPAReducts.TwoGraphs

/-- The identity combined action has trivial index permutation and matrix. -/
def CombinedActionData.identity (X : Type) : CombinedActionData X where
  indexPerm := Equiv.refl X
  matrix := zeroMatrix X
  symmetric := zeroMatrix_symmetric

/-- The identity combined action really is the identity permutation. -/
theorem CombinedActionData.action_identity (X : Type) :
    (CombinedActionData.identity X).action =
      Equiv.refl (ValuationVertex X) := by
  exact matrixIndexPerm_refl_zero

/-- The exact semidirect multiplication of combined-action data. -/
def CombinedActionData.trans {X : Type}
    (a b : CombinedActionData X) : CombinedActionData X where
  indexPerm := a.indexPerm.trans b.indexPerm
  matrix := xorMatrix (reindexMatrix a.indexPerm.symm b.matrix) a.matrix
  symmetric := xorMatrix_symmetric _ _
    (reindexMatrix_symmetric a.indexPerm.symm b.matrix b.symmetric)
    a.symmetric

/-- Data multiplication corresponds to permutation composition. -/
theorem CombinedActionData.action_trans {X : Type}
    (a b : CombinedActionData X) :
    (a.trans b).action = (a.action).trans (b.action) := by
  exact (matrixIndexPerm_trans a.indexPerm b.indexPerm
    a.matrix b.matrix).symm

/-- Inflating the identity combined action remains the identity. -/
theorem BlockCoordinates.inflateActionData_identity
    {D X : Type} (B : BlockCoordinates D X) :
    (B.inflateActionData (CombinedActionData.identity D)).action =
      Equiv.refl (ValuationVertex X) := by
  change matrixIndexPerm (B.liftPerm (Equiv.refl D))
      (inflateMatrix B.projection (zeroMatrix D)) =
        Equiv.refl (ValuationVertex X)
  rw [B.liftPerm_refl]
  change matrixIndexPerm (Equiv.refl X) (zeroMatrix X) =
    Equiv.refl (ValuationVertex X)
  exact matrixIndexPerm_refl_zero

/-- Inflation is compatible with the full semidirect product formula. -/
theorem BlockCoordinates.inflateActionData_trans
    {D X : Type} (B : BlockCoordinates D X)
    (a b : CombinedActionData D) :
    ((B.inflateActionData a).action).trans
      ((B.inflateActionData b).action) =
      (B.inflateActionData (a.trans b)).action := by
  exact B.combinedAction_trans a.indexPerm b.indexPerm a.matrix b.matrix

/-- At the quotient level, identity actions on D inflate to
identity actions on X, independently of all data representatives. -/
theorem BlockCoordinates.inflateCombinedActionClass_identity
    {D X : Type} [Nonempty D] (B : BlockCoordinates D X)
    (g : CombinedActionClass D)
    (hg : combinedActionClassPerm g =
      Equiv.refl (ValuationVertex D)) :
    combinedActionClassPerm (B.inflateCombinedActionClass g) =
      Equiv.refl (ValuationVertex X) := by
  induction g using Quotient.inductionOn with
  | _ a =>
    have hdata : (CombinedActionData.identity D).action = a.action :=
      (CombinedActionData.action_identity D).trans hg.symm
    have hinf := B.inflateActionData_wellDefined
      (CombinedActionData.identity D) a hdata
    change (B.inflateActionData a).action = Equiv.refl (ValuationVertex X)
    exact hinf.symm.trans (B.inflateActionData_identity)

/-- **Homomorphism law on faithful classes:** if r is the composition
of p and q as genuine quotient actions, the inflated action of r
is the composition of their inflated actions. No representative is
chosen for this statement. -/
theorem BlockCoordinates.inflateCombinedActionClass_trans
    {D X : Type} [Nonempty D] (B : BlockCoordinates D X)
    (p q r : CombinedActionClass D)
    (hcomp : combinedActionClassPerm r =
      (combinedActionClassPerm p).trans (combinedActionClassPerm q)) :
    combinedActionClassPerm (B.inflateCombinedActionClass r) =
      (combinedActionClassPerm (B.inflateCombinedActionClass p)).trans
        (combinedActionClassPerm (B.inflateCombinedActionClass q)) := by
  induction p using Quotient.inductionOn with
  | _ a =>
    induction q using Quotient.inductionOn with
    | _ b =>
      induction r using Quotient.inductionOn with
      | _ c =>
        have hdata : (a.trans b).action = c.action :=
          (CombinedActionData.action_trans a b).trans hcomp.symm
        have hinf := B.inflateActionData_wellDefined
          (a.trans b) c hdata
        change (B.inflateActionData c).action =
          ((B.inflateActionData a).action).trans
            ((B.inflateActionData b).action)
        exact hinf.symm.trans (B.inflateActionData_trans a b).symm

end EPPAReducts.TwoGraphs
