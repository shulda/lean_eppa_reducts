import EPPAReducts.TwoGraphs.TransversalLiteralExtension
import Mathlib.Logic.Equiv.Fintype

/-!
# Removing the prescribed-coordinate-permutation assumption

An arbitrary injective map from one finite index subset into X can
be extended to a total permutation of X. The Mathlib theorem
Equiv.Perm.exists_extending_pair supplies the exact finite
combinatorial result. Combining it with the certified cut/matrix lift
gives automorphism extension for *any* injective target coordinate
map of a nonempty valuation two-graph transversal.

The result is still about transversals, not yet a coherent EPPA
witness for an arbitrary input two-graph.
-/

namespace EPPAReducts.TwoGraphs

variable {X : Type} [DecidableEq X] [DecidableEq (ValuationVertex X)]

/-- Extend any injection on a finite set of old index coordinates
to a permutation of the ambient index set X. -/
theorem exists_indexPerm_extending_transversal_embedding
    (s : Finset X) (f : {x : X // x ∈ s} ↪ X) :
    ∃ σ : Equiv.Perm X, ∀ x : {z : X // z ∈ s}, σ x.val = f x := by
  classical
  exact Equiv.Perm.exists_extending_pair
    (fun x : {z : X // z ∈ s} => x.val)
    (fun x : {z : X // z ∈ s} => f x)
    Subtype.val_injective f.injective

/-- Literal relation-preservation on two transversals with a general
injective target projection, without first choosing a permutation. -/
def PreservesTransversalEmbeddingTwoGraph
    (s : Finset X) (f : {x : X // x ∈ s} ↪ X)
    (χ η : {x : X // x ∈ s} → Valuation X) : Prop :=
  ∀ x y z : {w : X // w ∈ s},
    (valuationTwoGraph X).isTriple
      (HumanTargets.triple (sourceTransversalVertex s χ x)
        (sourceTransversalVertex s χ y)
        (sourceTransversalVertex s χ z)) =
    (valuationTwoGraph X).isTriple
      (HumanTargets.triple (f x, valuationClass (η x))
        (f y, valuationClass (η y))
        (f z, valuationClass (η z)))

/-- Every induced isomorphism of nonempty transversals with any
injective coordinate map extends to an automorphism of the actual
finite valuation two-graph. -/
theorem exists_twoGraphAutomorphism_extending_transversal_embedding
    (s : Finset X) (hne : s.Nonempty)
    (f : {x : X // x ∈ s} ↪ X)
    (χ η : {x : X // x ∈ s} → Valuation X)
    (h : PreservesTransversalEmbeddingTwoGraph s f χ η) :
    ∃ g : Equiv.Perm (ValuationVertex X),
      HumanTargets.IsTwoGraphAutomorphism (valuationTwoGraph X) g ∧
      ∀ x : {w : X // w ∈ s},
        g (sourceTransversalVertex s χ x) =
          (f x, valuationClass (η x)) := by
  obtain ⟨σ, hσ⟩ :=
    exists_indexPerm_extending_transversal_embedding s f
  have hpres : PreservesTransversalTwoGraph s σ χ η := by
    intro x y z
    change
      (valuationTwoGraph X).isTriple
        (HumanTargets.triple (sourceTransversalVertex s χ x)
          (sourceTransversalVertex s χ y)
          (sourceTransversalVertex s χ z)) =
      (valuationTwoGraph X).isTriple
        (HumanTargets.triple (σ x.val, valuationClass (η x))
          (σ y.val, valuationClass (η y))
          (σ z.val, valuationClass (η z)))
    rw [hσ x, hσ y, hσ z]
    exact h x y z
  obtain ⟨g, hg, hmaps⟩ :=
    exists_twoGraphAutomorphism_extending_transversal s hne σ χ η hpres
  refine ⟨g, hg, ?_⟩
  intro x
  have hx := hmaps x
  change g (sourceTransversalVertex s χ x) =
    (σ x.val, valuationClass (η x)) at hx
  simpa only [hσ x] using hx

end EPPAReducts.TwoGraphs
