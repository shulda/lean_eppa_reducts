import EPPAReducts.TwoGraphs.IndexMatrixConjugation
import EPPAReducts.TwoGraphs.MatrixAutomorphism

/-!
# The full permutation-and-matrix family of two-graph automorphisms

An element (σ,F) first adds the symmetric matrix row F(x,-) to the
valuation at x and then reindexes every coordinate by σ. The resulting
map is an actual permutation preserving the author's literal two-graph.

The correct semidirect composition law, matrix quotient/faithfulness,
and transversal EPPA section are subsequent obligations.
-/

namespace EPPAReducts.TwoGraphs

/-- Apply a matrix row shift first, then permute the index coordinates. -/
def matrixIndexPerm {X : Type*}
    (σ : Equiv.Perm X) (F : X → X → Bool) :
    Equiv.Perm (ValuationVertex X) :=
  (rowShiftPerm F).trans (indexPermVertex σ)

/-- A composite of two genuine two-graph automorphisms is again an
automorphism, in the exact independent human-readable API. -/
theorem twoGraphAutomorphism_trans
    {V : Type} (A : HumanTargets.TwoGraph V)
    (p q : Equiv.Perm V)
    (hp : HumanTargets.IsTwoGraphAutomorphism A p)
    (hq : HumanTargets.IsTwoGraphAutomorphism A q) :
    HumanTargets.IsTwoGraphAutomorphism A (p.trans q) := by
  intro a b c
  exact (hp a b c).trans (hq (p a) (p b) (p c))

/-- For every permutation σ of X and every symmetric Boolean matrix F,
their composite is a genuine automorphism of valuationTwoGraph X. -/
theorem matrixIndexPerm_isTwoGraphAutomorphism
    {X : Type} [DecidableEq (ValuationVertex X)]
    (σ : Equiv.Perm X) (F : X → X → Bool)
    (hF : IsSymmetricBoolMatrix F) :
    HumanTargets.IsTwoGraphAutomorphism (valuationTwoGraph X)
      (matrixIndexPerm σ F) := by
  exact twoGraphAutomorphism_trans (valuationTwoGraph X)
    (rowShiftPerm F) (indexPermVertex σ)
    (rowShiftPerm_isTwoGraphAutomorphism F hF)
    (indexPermVertex_isTwoGraphAutomorphism σ)

end EPPAReducts.TwoGraphs
