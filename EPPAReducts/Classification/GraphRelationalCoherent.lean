import EPPAReducts.Classification.PositiveBaselines
import AllThoseEPPA.MainTheorems

/-!
# Coherent EPPA for the relational encoding of every finite graph

The pinned unrestricted faithful coherent EPPA theorem applies to the
original graph relation viewed as a binary relation in the trivial
language-action setting. It produces an actual finite coherent
relational witness. A later simple-graph normalization must still
show that one can choose the witness inside SimpleGraph, rather than
in arbitrary binary-relational structures.
-/

namespace EPPAReducts.Classification

/-- The binary graph language has no function symbols, hence its
unary-function condition holds vacuously. -/
instance graphLanguageHasUnaryFunctions :
    AllThoseEPPA.Graph.language.HasUnaryFunctions where
  arity_eq_one := by
    intro n F
    exact Empty.elim F

/-- The graph language has trivial one-element relabelling group,
so every graph has a finite relabelling orbit. -/
theorem finiteGraphRelabelOrbit
    {V : Type} (G : SimpleGraph V) :
    (AllThoseEPPA.Graph.toStructure G).HasFiniteRelabelOrbit
      AllThoseEPPA.Graph.action := by
  unfold AllThoseEPPA.Structure.HasFiniteRelabelOrbit
  exact Set.finite_range _

/-- A true coherent EPPA witness exists for the relational graph
presentation, with a genuine induced embedding and all coherent
partial-isomorphism extension laws. The witness is not yet claimed
to be a SimpleGraph. -/
theorem finiteGraphRelationalCoherentEPPA
    {V : Type} [Finite V] (G : SimpleGraph V) :
    ∃ (W : Type) (_ : Finite W)
      (B : AllThoseEPPA.Structure AllThoseEPPA.Graph.language W)
      (ι : AllThoseEPPA.Structure.Embedding
        AllThoseEPPA.Graph.action
        (AllThoseEPPA.Graph.toStructure G) B),
      AllThoseEPPA.Structure.IsCoherentEPPAWitness
        AllThoseEPPA.Graph.action ι := by
  have horbit := finiteGraphRelabelOrbit G
  obtain ⟨W, hW, B, ι, hcoh, _⟩ :=
    AllThoseEPPA.MainTheorems.unrestrictedFaithfulCoherentEPPA
      AllThoseEPPA.Graph.action (AllThoseEPPA.Graph.toStructure G) horbit
  exact ⟨W, hW, B, ι, hcoh⟩

end EPPAReducts.Classification
