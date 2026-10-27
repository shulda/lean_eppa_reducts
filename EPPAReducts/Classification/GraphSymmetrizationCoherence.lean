import EPPAReducts.Classification.GraphSymmetrizationAutomorphism

/-!
# Transfer of actual coherent extension systems to simple graphs

Starting from the coherent witness for the binary relational
presentation of an input simple graph, retain only mutual
off-diagonal edges of the ambient witness. The original embedding
remains induced, and the same full automorphisms preserve this
normalized relation. The extension function therefore retains the
same identities, equivalence invariance and coherence equation.

This route does not assume that the arbitrary relational witness
already has symmetric edges or is loopless.
-/

namespace EPPAReducts.Classification

open AllThoseEPPA
open AllThoseEPPA.Graph

/-- Transport an honest simultaneous coherent extension function
from the original binary relational witness to its genuine
simple-graph normalization, preserving all partial maps. -/
noncomputable def symmetrizedGraphCoherentExtension
    {V W : Type}
    (G : SimpleGraph V)
    (B : Structure Graph.language W)
    (ψ : Structure.Embedding Graph.action (Graph.toStructure G) B)
    (E : Structure.CoherentExtension Graph.action ψ) :
    Structure.CoherentExtension Graph.action
      (symmetrizedGraphEmbedding G B ψ) where
  extension := fun p => symmetrizedGraphAutomorphism B (E.extension p)
  extension_spec := by
    intro p
    exact E.extension_spec p
  respects_equivalent := by
    intro p q hpq
    exact congrArg (symmetrizedGraphAutomorphism B)
      (E.respects_equivalent p q hpq)
  coherent := by
    intro p q r hpqr
    have h := E.coherent p q r hpqr
    apply Structure.Automorphism.ext_of_lang_apply
    · have hl := congrArg
        (fun a : Structure.Automorphism Graph.action B => a.lang) h
      simpa only [symmetrizedGraphAutomorphism_lang,
        Structure.Automorphism.comp_lang] using hl
    · intro x
      have hx := congrArg
        (fun a : Structure.Automorphism Graph.action B => a x) h
      simpa only [symmetrizedGraphAutomorphism_apply,
        Structure.Automorphism.comp_apply] using hx

/-- **Coherent EPPA for all finite simple graphs.** A single finite
simple graph B and one induced embedding are chosen before all
partial automorphisms; their chosen extensions form a coherent
system in the exact typed original graph language. -/
theorem finiteSimpleGraphsHaveCoherentEPPA
    {V : Type} [Finite V]
    (G : SimpleGraph V) :
    ∃ (W : Type) (_ : Finite W)
      (H : SimpleGraph W)
      (ψ : Structure.Embedding Graph.action
        (Graph.toStructure G) (Graph.toStructure H)),
      Structure.IsCoherentEPPAWitness Graph.action ψ := by
  obtain ⟨W, hW, B, ψ, hcoh⟩ :=
    finiteGraphRelationalCoherentEPPA G
  obtain ⟨E⟩ := hcoh
  exact ⟨W, hW, symmetrizedSimpleGraph B,
    symmetrizedGraphEmbedding G B ψ,
    ⟨symmetrizedGraphCoherentExtension G B ψ E⟩⟩

end EPPAReducts.Classification
