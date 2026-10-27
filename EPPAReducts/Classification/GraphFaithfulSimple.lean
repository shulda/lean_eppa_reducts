import EPPAReducts.Classification.GraphRelationalCoherent
import AllThoseEPPA.Irreducible
import Mathlib.Data.Fin.VecNotation

/-!
# Irreducible faithfulness forces graph-shaped binary relations

The general coherent EPPA construction returns a structure in the
original one-symbol binary language. Its *faithfulness* ensures that
no loops and no asymmetric edges can appear when the input is a
simple graph: any realized relation tuple generates an irreducible
substructure, which an ambient automorphism moves into the input copy.

This keeps us in the true original-language class of simple graphs;
there is no unjustified assumption that all binary structures are
simple graphs.
-/

namespace EPPAReducts.Classification

open AllThoseEPPA
open AllThoseEPPA.Structure
open AllThoseEPPA.Graph

private theorem graphEmbedding_rel_iff
    {V W : Type}
    (G : SimpleGraph V)
    (B : Structure Graph.language W)
    (ι : Structure.Embedding Graph.action (Graph.toStructure G) B)
    (a b : V) :
    B.rel Graph.RelSymbol.edge (![ι a, ι b] : Fin 2 → W) ↔
      G.Adj a b := by
  have h := ι.map_rel_iff Graph.RelSymbol.edge (![a, b] : Fin 2 → V)
  have hlang : ι.lang = 1 := Subsingleton.elim _ _
  simpa [hlang, Graph.toStructure, Language.Action.onRel_one,
    Function.comp_apply] using h

private theorem graphAutomorphism_rel_iff
    {W : Type} (B : Structure Graph.language W)
    (g : Structure.Automorphism Graph.action B)
    (a b : W) :
    B.rel Graph.RelSymbol.edge (![g a, g b] : Fin 2 → W) ↔
      B.rel Graph.RelSymbol.edge (![a, b] : Fin 2 → W) := by
  have hsrc :
      ∀ i : Fin 2,
        (![a, b] : Fin 2 → W) i ∈
          g.toPartialIsomorphism.toPartialEquiv.source := by
    intro i
    change (![a, b] : Fin 2 → W) i ∈
      g.toPartialIsomorphism.source
    rw [g.source_eq_univ]
    exact Set.mem_univ _
  have h := g.toPartialIsomorphism.map_rel_iff
      Graph.RelSymbol.edge (![a, b] : Fin 2 → W) hsrc
  have hlang : g.toPartialIsomorphism.lang = 1 := Subsingleton.elim _ _
  simpa [hlang, Language.Action.onRel_one,
    Function.comp_apply] using h

/-- An irreducible-structure faithful binary witness for a simple
graph must have a symmetric binary edge relation. -/
theorem faithfulGraphRelation_symmetric
    {V W : Type} (G : SimpleGraph V)
    (B : Structure Graph.language W)
    (ι : Structure.Embedding Graph.action (Graph.toStructure G) B)
    (hfaithful : Structure.IsIrreducibleStructureFaithful
      Graph.action ι)
    (x y : W) :
    B.rel Graph.RelSymbol.edge (![x, y] : Fin 2 → W) →
      B.rel Graph.RelSymbol.edge (![y, x] : Fin 2 → W) := by
  intro hxy
  let xs : Fin 2 → W := ![x, y]
  have hrel : B.rel Graph.RelSymbol.edge xs := hxy
  have hclosed := B.isClosed_closureSet (Set.range xs)
  have hirr : (B.induce (B.closureSet (Set.range xs)) hclosed).IsIrreducible :=
    B.relationTupleClosure_isIrreducible Graph.RelSymbol.edge xs hrel
  obtain ⟨g, hg⟩ := hfaithful (B.closureSet (Set.range xs)) hclosed hirr
  have hx : x ∈ B.closureSet (Set.range xs) :=
    B.subset_closureSet _ ⟨0, rfl⟩
  have hy : y ∈ B.closureSet (Set.range xs) :=
    B.subset_closureSet _ ⟨1, rfl⟩
  obtain ⟨a, ha⟩ := hg x hx
  obtain ⟨b, hb⟩ := hg y hy
  have hImage : B.rel Graph.RelSymbol.edge
      (![ι a, ι b] : Fin 2 → W) := by
    have h := (graphAutomorphism_rel_iff B g x y).2 hxy
    simpa [ha, hb] using h
  have hG : G.Adj a b :=
    (graphEmbedding_rel_iff G B ι a b).mp hImage
  have hBack : B.rel Graph.RelSymbol.edge
      (![g y, g x] : Fin 2 → W) := by
    have h := (graphEmbedding_rel_iff G B ι b a).mpr hG.symm
    simpa [ha, hb] using h
  exact (graphAutomorphism_rel_iff B g y x).mp hBack

/-- The same faithfulness excludes every diagonal edge. -/
theorem faithfulGraphRelation_loopless
    {V W : Type} (G : SimpleGraph V)
    (B : Structure Graph.language W)
    (ι : Structure.Embedding Graph.action (Graph.toStructure G) B)
    (hfaithful : Structure.IsIrreducibleStructureFaithful
      Graph.action ι)
    (x : W) :
    ¬ B.rel Graph.RelSymbol.edge (![x, x] : Fin 2 → W) := by
  intro hxx
  let xs : Fin 2 → W := ![x, x]
  have hrel : B.rel Graph.RelSymbol.edge xs := hxx
  have hclosed := B.isClosed_closureSet (Set.range xs)
  have hirr : (B.induce (B.closureSet (Set.range xs)) hclosed).IsIrreducible :=
    B.relationTupleClosure_isIrreducible Graph.RelSymbol.edge xs hrel
  obtain ⟨g, hg⟩ := hfaithful (B.closureSet (Set.range xs)) hclosed hirr
  have hx : x ∈ B.closureSet (Set.range xs) :=
    B.subset_closureSet _ ⟨0, rfl⟩
  obtain ⟨a, ha⟩ := hg x hx
  have hImage : B.rel Graph.RelSymbol.edge
      (![ι a, ι a] : Fin 2 → W) := by
    have h := (graphAutomorphism_rel_iff B g x x).2 hxx
    simpa [ha] using h
  have hG : G.Adj a a :=
    (graphEmbedding_rel_iff G B ι a a).mp hImage
  exact G.loopless.irrefl a hG

/-- The coherent faithful witness's original binary relation is
literally the adjacency relation of an actual simple graph. -/
def faithfulBinaryToSimpleGraph
    {W : Type} (B : Structure Graph.language W)
    (hsym : ∀ x y : W, B.rel Graph.RelSymbol.edge (![x, y] : Fin 2 → W) →
      B.rel Graph.RelSymbol.edge (![y, x] : Fin 2 → W))
    (hirr : ∀ x : W, ¬ B.rel Graph.RelSymbol.edge
      (![x, x] : Fin 2 → W)) :
    SimpleGraph W where
  Adj := fun x y => B.rel Graph.RelSymbol.edge (![x, y] : Fin 2 → W)
  symm := ⟨hsym⟩
  loopless := ⟨hirr⟩

end EPPAReducts.Classification
