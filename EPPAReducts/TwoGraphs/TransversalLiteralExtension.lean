import EPPAReducts.TwoGraphs.TransversalMatrixAction
import EPPAReducts.TwoGraphs.MatrixAutomorphism

/-!
# Extending induced isomorphisms of valuation two-graph transversals

This bridges the cut/matrix construction to the **literal**
author-approved TwoGraph relation, not merely to its raw parity
formula. A coordinate permutation σ is taken as given; extending
an arbitrary partial injection to such a permutation is a separate
finite combinatorial obligation.

There is no claim of full EPPA or coherent EPPA here.
-/

namespace EPPAReducts.TwoGraphs

variable {X : Type}
variable [DecidableEq X] [DecidableEq (ValuationVertex X)]

/-- The triple predicate of the constructed two-graph agrees with the
symmetric ternary valuation parity even on repeated vertices. -/
theorem valuationTwoGraph_triple_eq_vertexParity
    (a b c : ValuationVertex X) :
    (valuationTwoGraph X).isTriple (HumanTargets.triple a b c) =
      vertexTripleParity a b c := by
  classical
  have hset : HumanTargets.triple a b c =
      ({a, b, c} : Finset (ValuationVertex X)) := by
    ext t
    simp [HumanTargets.triple]
  change unorderedTripleParity (HumanTargets.triple a b c) =
    vertexTripleParity a b c
  rw [hset]
  exact unorderedTripleParity_on_any_three a b c

/-- A source-transversal vertex with chosen raw valuation. -/
def sourceTransversalVertex
    (s : Finset X) (χ : {x : X // x ∈ s} → Valuation X)
    (x : {z : X // z ∈ s}) : ValuationVertex X :=
  (x.val, valuationClass (χ x))

/-- The desired target-transversal vertex after coordinate permutation σ. -/
def targetTransversalVertex
    (s : Finset X) (σ : Equiv.Perm X)
    (η : {x : X // x ∈ s} → Valuation X)
    (x : {z : X // z ∈ s}) : ValuationVertex X :=
  (σ x.val, valuationClass (η x))

/-- The literal induced two-graph relation agrees between source and
target transversals, for every ordered triple of domain vertices.
Each map is an embedding because its first-coordinate map is injective. -/
def PreservesTransversalTwoGraph
    (s : Finset X) (σ : Equiv.Perm X)
    (χ η : {x : X // x ∈ s} → Valuation X) : Prop :=
  ∀ x y z : {w : X // w ∈ s},
    (valuationTwoGraph X).isTriple
      (HumanTargets.triple (sourceTransversalVertex s χ x)
        (sourceTransversalVertex s χ y)
        (sourceTransversalVertex s χ z)) =
    (valuationTwoGraph X).isTriple
      (HumanTargets.triple (targetTransversalVertex s σ η x)
        (targetTransversalVertex s σ η y)
        (targetTransversalVertex s σ η z))

/-- Preservation of the literal two-graph triple relation implies
preservation of the raw six-entry Boolean parity expression. -/
theorem rawTripleParity_of_preservesTransversalTwoGraph
    (s : Finset X) (σ : Equiv.Perm X)
    (χ η : {x : X // x ∈ s} → Valuation X)
    (h : PreservesTransversalTwoGraph s σ χ η) :
    ∀ x y z : {w : X // w ∈ s},
      rawTripleParity x.val y.val z.val (χ x) (χ y) (χ z) =
      rawTripleParity (σ x.val) (σ y.val) (σ z.val)
        (η x) (η y) (η z) := by
  intro x y z
  have hp := h x y z
  rw [valuationTwoGraph_triple_eq_vertexParity,
      valuationTwoGraph_triple_eq_vertexParity] at hp
  change quotientTripleParity x.val y.val z.val
      (valuationClass (χ x)) (valuationClass (χ y)) (valuationClass (χ z)) =
    quotientTripleParity (σ x.val) (σ y.val) (σ z.val)
      (valuationClass (η x)) (valuationClass (η y))
      (valuationClass (η z)) at hp
  simpa only [quotientTripleParity_mk] using hp

/-- Every induced isomorphism between two prescribed nonempty
transversals with a chosen total extension of its index map extends
to a genuine automorphism of the literal valuation two-graph. -/
theorem exists_twoGraphAutomorphism_extending_transversal
    (s : Finset X) (hne : s.Nonempty)
    (σ : Equiv.Perm X)
    (χ η : {x : X // x ∈ s} → Valuation X)
    (h : PreservesTransversalTwoGraph s σ χ η) :
    ∃ g : Equiv.Perm (ValuationVertex X),
      HumanTargets.IsTwoGraphAutomorphism (valuationTwoGraph X) g ∧
      ∀ x : {w : X // w ∈ s},
        g (sourceTransversalVertex s χ x) =
          targetTransversalVertex s σ η x := by
  obtain ⟨F, hF, hmaps⟩ :=
    exists_matrixIndexPerm_extending_raw_transversal s hne σ χ η
      (rawTripleParity_of_preservesTransversalTwoGraph s σ χ η h)
  refine ⟨matrixIndexPerm σ F,
    matrixIndexPerm_isTwoGraphAutomorphism σ F hF, ?_⟩
  intro x
  exact hmaps x

end EPPAReducts.TwoGraphs
