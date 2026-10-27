import EPPAReducts.Classification.GraphRelationalCoherent
import Mathlib.Data.Fin.VecNotation

/-!
# Canonical simple-graph reduct of an arbitrary binary relational witness

The general coherent EPPA theorem yields a binary *relational* witness,
which need not have a symmetric or irreflexive interpretation. We
normalize the relation by retaining only symmetric non-loop pairs.
This produces an actual SimpleGraph and preserves the induced old
graph copy. The next module will show that all witness automorphisms
preserve this canonical normalized relation, with coherence intact.

No irreducible-faithfulness assumption is required for this trick.
-/

namespace EPPAReducts.Classification

open AllThoseEPPA
open AllThoseEPPA.Graph

/-- The symmetric, loopless subrelation of a single arbitrary
binary relation. Its carrier is unchanged. -/
def symmetrizedSimpleGraph {W : Type}
    (B : Structure Graph.language W) : SimpleGraph W where
  Adj := fun x y =>
    x ≠ y ∧
      B.rel Graph.RelSymbol.edge (![x, y] : Fin 2 → W) ∧
      B.rel Graph.RelSymbol.edge (![y, x] : Fin 2 → W)
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by
    constructor
    intro x h
    exact h.1 rfl

/-- An arbitrary induced embedding of a simple graph into a
binary-relational structure is an induced embedding into its
normalized simple-graph part. -/
noncomputable def symmetrizedGraphEmbedding
    {V W : Type} (G : SimpleGraph V)
    (B : Structure Graph.language W)
    (ψ : Structure.Embedding Graph.action
      (Graph.toStructure G) B) :
    Structure.Embedding Graph.action
      (Graph.toStructure G)
      (Graph.toStructure (symmetrizedSimpleGraph B)) where
  lang := ψ.lang
  toFun := ψ.toFun
  injective := ψ.injective
  map_rel_iff := by
    intro n R xs
    cases R with
    | edge =>
      have hψ : ψ.lang = 1 := Subsingleton.elim _ _
      have hr (x y : V) :
          B.rel Graph.RelSymbol.edge (![ψ x, ψ y] : Fin 2 → W) ↔
            G.Adj x y := by
        have h := ψ.map_rel_iff Graph.RelSymbol.edge
          (![x, y] : Fin 2 → V)
        have hs : Graph.action.onRel ψ.lang Graph.RelSymbol.edge =
            Graph.RelSymbol.edge := by
          simp [hψ, Graph.action, Language.Action.trivial,
            Language.Action.onRel]
        rw [hs] at h
        have he :
            (ψ.toFun ∘ (![x, y] : Fin 2 → V)) =
              (![ψ x, ψ y] : Fin 2 → W) := by
          funext i
          fin_cases i <;> rfl
        rw [he] at h
        simpa only [Graph.toStructure_edge] using h
      change (ψ (xs 0) ≠ ψ (xs 1) ∧
        B.rel Graph.RelSymbol.edge (![ψ (xs 0), ψ (xs 1)] : Fin 2 → W) ∧
        B.rel Graph.RelSymbol.edge (![ψ (xs 1), ψ (xs 0)] : Fin 2 → W)) ↔
        G.Adj (xs 0) (xs 1)
      constructor
      · intro h
        exact (hr _ _).mp h.2.1
      · intro h
        have hne : xs 0 ≠ xs 1 := by
          intro he
          rw [he] at h
          exact G.loopless.irrefl _ h
        refine ⟨ψ.injective.ne hne, (hr _ _).2 h, ?_⟩
        exact (hr _ _).2 h.symm
  map_func := by
    intro n F xs
    exact Empty.elim F

end EPPAReducts.Classification
