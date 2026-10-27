import AllThoseEPPA.FiniteSet
import AllThoseEPPA.Examples.GraphExtension

/-!
# Positive baseline results for the five-reduct table

This module exposes the *already proved* coherent EPPA theorem
for finite sets and ordinary EPPA for finite simple graphs from
the pinned AllThoseEPPA dependency. It does not claim a
coherent graph theorem, nor the full five-reduct classification.

The positive cases must have actual theorem types, not a
table whose truth values are defined by hand.
-/

namespace EPPAReducts.Classification

/-- Every finite set admits a coherent extension of all partial
permutations to full permutations. There is a single choice which
respects composition and is invariant under equivalent partial maps. -/
theorem finiteSetsHaveCoherentEPPA (V : Type) [Finite V] :
    ∃ extension : PartialEquiv V V → Equiv.Perm V,
      (∀ (p : PartialEquiv V V) (x : V),
        x ∈ p.source → extension p x = p x) ∧
      (∀ (p q : PartialEquiv V V),
        PartialEquiv.EqOnSource p q → extension p = extension q) ∧
      ∀ (p q : PartialEquiv V V) (h : p.target = q.source),
        extension (p.trans' q h) =
          (extension p).trans (extension q) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  exact AllThoseEPPA.finiteSetsHaveCoherentEPPA V

/-- Every finite simple graph admits an actual finite graph EPPA witness
in the pinned upstream valuation construction. This is ordinary EPPA:
the coherent graph-positive case requires a separate checked bridge. -/
theorem finiteGraphsHaveOrdinaryEPPA
    {V : Type} [Finite V] (G : SimpleGraph V) :
    ∃ ψ : AllThoseEPPA.Structure.Embedding
      AllThoseEPPA.Graph.action
      (AllThoseEPPA.Graph.toStructure G)
      (AllThoseEPPA.Graph.toStructure
        (AllThoseEPPA.Graph.WitnessVertex.witnessGraph V)),
      AllThoseEPPA.Structure.IsEPPAWitness
        AllThoseEPPA.Graph.action ψ := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  exact AllThoseEPPA.Graph.finiteGraphsHaveEPPA G

end EPPAReducts.Classification
