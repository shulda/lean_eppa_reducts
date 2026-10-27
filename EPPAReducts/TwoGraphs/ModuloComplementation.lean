import EPPAReducts.BoundedEquivalence.UnorderedWitnessAPI
import EPPAReducts.TwoGraphs.RootingParity

/-!
# Two-graphs modulo global complementation: exact unlabelled interface

An object is an equivalence on unordered triples which admits a
(two-graph) indicator as a *non-structural* auxiliary labelling. The
actual automorphisms preserve equality of triple classes and may swap
them. The representative exists propositionally; it is not named by
the reduct. A complement of a two-graph is again a two-graph.

This is a separate arity-three interface: it must not be confused
with ordinary two-graphs, for which coherent EPPA is already proved.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets
open EPPAReducts.BoundedEquivalence

/-- The genuine unordered triples. -/
abbrev UnorderedTriples (V : Type) := RSubsets V 3

/-- Equivalence on triples with at most two *unnamed* classes, admitting
a four-point-even two-graph as a representative. -/
structure TwoGraphModuloComplementation (V : Type) where
  sameClass : Setoid (UnorderedTriples V)
  representative : ∃ T : TwoGraph V,
    ∀ e f : UnorderedTriples V,
      sameClass.r e f ↔ T.isTriple e.val = T.isTriple f.val

/-- Induced embeddings reflect as well as preserve class equality. -/
def IsInducedTripleClassEmbedding {V W : Type}
    (A : TwoGraphModuloComplementation V)
    (B : TwoGraphModuloComplementation W)
    (ι : V ↪ W) : Prop :=
  ∀ e f : UnorderedTriples V,
    A.sameClass.r e f ↔
      B.sameClass.r (mapRSubset ι e) (mapRSubset ι f)

/-- Literal partial vertex bijections: classes may be exchanged. -/
def IsTripleClassPartialAutomorphism {V : Type}
    (A : TwoGraphModuloComplementation V)
    (p : PartialBijection V) : Prop :=
  ∀ e f : UnorderedTriples {x : V // x ∈ p.source},
    A.sameClass.r
      (mapRSubset (subtypeEmbedding p.source) e)
      (mapRSubset (subtypeEmbedding p.source) f) ↔
    A.sameClass.r
      (mapRSubset
        (equivThenEmbedding p.bijection (subtypeEmbedding p.target)) e)
      (mapRSubset
        (equivThenEmbedding p.bijection (subtypeEmbedding p.target)) f)

/-- The actual full automorphism group preserves the triple kernel,
not the name of a chosen two-graph representative. -/
def IsTripleClassAutomorphism {V : Type}
    (A : TwoGraphModuloComplementation V)
    (g : Equiv.Perm V) : Prop :=
  ∀ e f : UnorderedTriples V,
    A.sameClass.r e f ↔
      A.sameClass.r (permuteRSubset g e) (permuteRSubset g f)

/-- Ordinary EPPA for one unlabelled triple-class structure. -/
def IsTripleClassEPPAWitness {V W : Type}
    (A : TwoGraphModuloComplementation V)
    (B : TwoGraphModuloComplementation W)
    (ι : V ↪ W) : Prop :=
  IsInducedTripleClassEmbedding A B ι ∧
    ∀ p : PartialBijection V,
      IsTripleClassPartialAutomorphism A p →
      ∃ g : Equiv.Perm W,
        IsTripleClassAutomorphism B g ∧ Extends ι p g

/-- The precise (hypothetical) EPPA assertion for the fifth reduct. -/
def TwoGraphsModuloHaveEPPA : Prop :=
  ∀ (V : Type), Finite V →
    ∀ (A : TwoGraphModuloComplementation V),
      ∃ (W : Type), Finite W ∧
        ∃ (B : TwoGraphModuloComplementation W) (ι : V ↪ W),
          IsTripleClassEPPAWitness A B ι

/-- Its explicit negative, quantifying over *all* finite witnesses. -/
def TwoGraphsModuloFailEPPA : Prop :=
  ∃ (V : Type), Finite V ∧
    ∃ (A : TwoGraphModuloComplementation V),
      ∀ (W : Type), Finite W →
        ∀ (B : TwoGraphModuloComplementation W)
          (ι : V ↪ W),
            ¬ IsTripleClassEPPAWitness A B ι

end EPPAReducts.TwoGraphs
