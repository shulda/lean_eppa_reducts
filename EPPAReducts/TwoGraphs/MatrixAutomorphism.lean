import EPPAReducts.TwoGraphs.AnyTripleParity
import EPPAReducts.TwoGraphs.MatrixXor
import EPPAReducts.TwoGraphs.ValuationTwoGraph

/-!
# Real automorphisms of the author-approved valuation two-graph

A permutation preserving the ternary valuation parity automatically
preserves the unordered-triple relation, including repeated input
vertices. Symmetric matrix row shifts thus give honest automorphisms
in the exact HumanTargets.IsTwoGraphAutomorphism interface.

This still does not prove partial-automorphism extension or coherence.
-/

namespace EPPAReducts.TwoGraphs

variable {X : Type} [DecidableEq (ValuationVertex X)]

/-- The readable Finset triple and the explicit triple notation agree. -/
private theorem humanTriple_eq
    (a b c : ValuationVertex X) :
    HumanTargets.triple a b c =
      ({a, b, c} : Finset (ValuationVertex X)) := by
  classical
  ext x
  simp [HumanTargets.triple]

/-- Any vertex permutation preserving the ternary valuation formula
is an automorphism of the exact approved unordered two-graph. -/
theorem valuationTwoGraph_automorphism_of_ternary
    (g : Equiv.Perm (ValuationVertex X))
    (h : ∀ a b c,
      vertexTripleParity (g a) (g b) (g c) =
        vertexTripleParity a b c) :
    HumanTargets.IsTwoGraphAutomorphism (valuationTwoGraph X) g := by
  intro a b c
  change
    unorderedTripleParity (HumanTargets.triple a b c) =
      unorderedTripleParity (HumanTargets.triple (g a) (g b) (g c))
  simpa only [humanTriple_eq, unorderedTripleParity_on_any_three] using
    (h a b c).symm

/-- Every symmetric Boolean matrix acts by an actual automorphism of
the original, author-approved finite valuation two-graph. -/
theorem rowShiftPerm_isTwoGraphAutomorphism
    (F : X → X → Bool) (hF : IsSymmetricBoolMatrix F) :
    HumanTargets.IsTwoGraphAutomorphism (valuationTwoGraph X)
      (rowShiftPerm F) := by
  apply valuationTwoGraph_automorphism_of_ternary
  intro a b c
  exact vertexTripleParity_rowShift F hF a b c

end EPPAReducts.TwoGraphs
