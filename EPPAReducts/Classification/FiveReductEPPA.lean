import EPPAReducts.Classification.GraphSymmetrizationCoherence
import EPPAReducts.Classification.OrdinaryPositiveCorollaries
import EPPAReducts.TwoGraphs.RootingGlobalTransfer

/-!
# Exact EPPA and coherent-EPPA classification of the five named finite reduct classes

The propositions below quantify over real structures, finite common witnesses,
induced embeddings and every partial automorphism. The theorem proves the
five rows and both columns, rather than encoding a list of Boolean constants.

The assertion that these are *all* first-order reducts of the random graph
is Thomas's external model-theoretic classification; it is NOT asserted to
have been proved in Lean here.
-/

namespace EPPAReducts.Classification

open AllThoseEPPA
open EPPAReducts.HumanTargets

/-- Finite simple graphs, with the exact typed original graph language:
one finite *simple graph* witnesses coherent EPPA for every finite input. -/
def GraphsHaveCoherentEPPA : Prop :=
  ∀ (V : Type), Finite V → ∀ (G : SimpleGraph V),
    ∃ (W : Type), Finite W ∧
      ∃ (H : SimpleGraph W)
        (ψ : Structure.Embedding AllThoseEPPA.Graph.action.{0}
          (AllThoseEPPA.Graph.toStructure G)
          (AllThoseEPPA.Graph.toStructure H)),
        Structure.IsCoherentEPPAWitness AllThoseEPPA.Graph.action.{0} ψ

/-- The corresponding ordinary EPPA class assertion for actual simple graphs. -/
def GraphsHaveEPPA : Prop :=
  ∀ (V : Type), Finite V → ∀ (G : SimpleGraph V),
    ∃ (W : Type), Finite W ∧
      ∃ (H : SimpleGraph W)
        (ψ : Structure.Embedding AllThoseEPPA.Graph.action.{0}
          (AllThoseEPPA.Graph.toStructure G)
          (AllThoseEPPA.Graph.toStructure H)),
        Structure.IsEPPAWitness AllThoseEPPA.Graph.action.{0} ψ

theorem graphsHaveCoherentEPPA : GraphsHaveCoherentEPPA := by
  intro V hV G
  letI : Finite V := hV
  obtain ⟨W, hW, H, ψ, hcoh⟩ :=
    finiteSimpleGraphsHaveCoherentEPPA G
  exact ⟨W, hW, H, ψ, hcoh⟩

theorem graphsHaveEPPA : GraphsHaveEPPA := by
  intro V hV G
  letI : Finite V := hV
  obtain ⟨W, hW, H, ψ, ⟨E⟩⟩ :=
    finiteSimpleGraphsHaveCoherentEPPA G
  exact ⟨W, hW, H, ψ, E.isEPPAWitness⟩

/-- Finite pure sets with one common coherent extension of all
partial permutations; the witness set is the input set itself. -/
def SetsHaveCoherentEPPA : Prop :=
  ∀ (V : Type), Finite V →
    ∃ extension : PartialEquiv V V → Equiv.Perm V,
      (∀ (p : PartialEquiv V V) (x : V),
        x ∈ p.source → extension p x = p x) ∧
      (∀ (p q : PartialEquiv V V),
        PartialEquiv.EqOnSource p q → extension p = extension q) ∧
      ∀ (p q : PartialEquiv V V) (h : p.target = q.source),
        extension (p.trans' q h) =
          (extension p).trans (extension q)

theorem setsHaveCoherentEPPA : SetsHaveCoherentEPPA := by
  intro V hV
  letI : Finite V := hV
  exact finiteSetsHaveCoherentEPPA V

/-- Coherent EPPA requires an actual choice of extensions satisfying
composable products for every partial automorphism of the *unnamed*
pair-equivalence reduct. -/
def IsPairCoherentEPPAWitness {V W : Type}
    (A : GraphModuloComplementation V)
    (B : GraphModuloComplementation W) (ι : V ↪ W) : Prop :=
  IsInducedPairEmbedding A B ι ∧
    ∃ extension : (p : PartialBijection V) →
      IsPairPartialAutomorphism A p → Equiv.Perm W,
      (∀ (p : PartialBijection V)
        (hp : IsPairPartialAutomorphism A p),
        IsPairAutomorphism B (extension p hp) ∧
          Extends ι p (extension p hp)) ∧
      ∀ (p q r : PartialBijection V)
        (hp : IsPairPartialAutomorphism A p)
        (hq : IsPairPartialAutomorphism A q)
        (hr : IsPairPartialAutomorphism A r),
        IsComposition p q r →
        ∀ w : W, extension r hr w =
          extension q hq (extension p hp w)

/-- Coherent EPPA for the fourth reduct (graphs modulo global
complementation), quantified over the whole finite class. -/
def GraphsModuloHaveCoherentEPPA : Prop :=
  ∀ (V : Type), Finite V →
    ∀ (A : GraphModuloComplementation V),
      ∃ (W : Type), Finite W ∧
        ∃ (B : GraphModuloComplementation W) (ι : V ↪ W),
          IsPairCoherentEPPAWitness A B ι

/-- A hypothetical coherent extension system necessarily provides
a single ordinary EPPA witness for all partial automorphisms. -/
theorem graphsModuloCoherentImpliesEPPA
    (h : GraphsModuloHaveCoherentEPPA) :
    EPPAReducts.TwoGraphs.GraphsModuloHaveEPPA := by
  intro V hV A
  obtain ⟨W, hW, B, ι, hι, extension, hspec, _⟩ :=
    h V hV A
  refine ⟨W, hW, B, ι, ⟨hι, ?_⟩⟩
  intro p hp
  obtain ⟨hauto, hext⟩ := hspec p hp
  exact ⟨extension p hp, hauto, hext⟩

theorem graphsModuloNotHaveCoherentEPPA :
    ¬ GraphsModuloHaveCoherentEPPA := by
  intro h
  exact EPPAReducts.TwoGraphs.graphsModuloNotHaveEPPA
    (graphsModuloCoherentImpliesEPPA h)

/-- Coherent EPPA for the fifth reduct uses the genuine
unlabelled triple-equivalence structure, not a chosen representative. -/
def IsTripleCoherentEPPAWitness {V W : Type}
    (A : EPPAReducts.TwoGraphs.TwoGraphModuloComplementation V)
    (B : EPPAReducts.TwoGraphs.TwoGraphModuloComplementation W)
    (ι : V ↪ W) : Prop :=
  EPPAReducts.TwoGraphs.IsInducedTripleClassEmbedding A B ι ∧
    ∃ extension : (p : PartialBijection V) →
      EPPAReducts.TwoGraphs.IsTripleClassPartialAutomorphism A p →
        Equiv.Perm W,
      (∀ (p : PartialBijection V)
        (hp : EPPAReducts.TwoGraphs.IsTripleClassPartialAutomorphism A p),
        EPPAReducts.TwoGraphs.IsTripleClassAutomorphism B
          (extension p hp) ∧
        Extends ι p (extension p hp)) ∧
      ∀ (p q r : PartialBijection V)
        (hp : EPPAReducts.TwoGraphs.IsTripleClassPartialAutomorphism A p)
        (hq : EPPAReducts.TwoGraphs.IsTripleClassPartialAutomorphism A q)
        (hr : EPPAReducts.TwoGraphs.IsTripleClassPartialAutomorphism A r),
        IsComposition p q r →
        ∀ w : W, extension r hr w =
          extension q hq (extension p hp w)

def TwoGraphsModuloHaveCoherentEPPA : Prop :=
  ∀ (V : Type), Finite V →
    ∀ (A : EPPAReducts.TwoGraphs.TwoGraphModuloComplementation V),
      ∃ (W : Type), Finite W ∧
        ∃ (B : EPPAReducts.TwoGraphs.TwoGraphModuloComplementation W)
          (ι : V ↪ W),
          IsTripleCoherentEPPAWitness A B ι

theorem twoGraphsModuloCoherentImpliesEPPA
    (h : TwoGraphsModuloHaveCoherentEPPA) :
    EPPAReducts.TwoGraphs.TwoGraphsModuloHaveEPPA := by
  intro V hV A
  obtain ⟨W, hW, B, ι, hι, extension, hspec, _⟩ :=
    h V hV A
  refine ⟨W, hW, B, ι, ⟨hι, ?_⟩⟩
  intro p hp
  obtain ⟨hauto, hext⟩ := hspec p hp
  exact ⟨extension p hp, hauto, hext⟩

theorem twoGraphsModuloNotHaveCoherentEPPA :
    ¬ TwoGraphsModuloHaveCoherentEPPA := by
  intro h
  exact EPPAReducts.TwoGraphs.twoGraphsModuloNotHaveEPPA
    (twoGraphsModuloCoherentImpliesEPPA h)

/-- The five-row, two-column classification of EPPA and coherent EPPA,
in terms of actual structure-class properties with checked witnesses:

- simple graphs: both YES
- finite sets: both YES
- finite two-graphs: both YES
- graphs modulo complementation: both NO
- two-graphs modulo complementation: both NO

It does not re-prove Thomas's external enumeration of the reducts. -/
def FiveReductEPPAClassification : Prop :=
  (GraphsHaveEPPA ∧ GraphsHaveCoherentEPPA) ∧
  (FiniteSetsHaveEPPA ∧ SetsHaveCoherentEPPA) ∧
  (FiniteTwoGraphsHaveEPPA ∧ twoGraphsHaveCoherentEPPA) ∧
  (¬ EPPAReducts.TwoGraphs.GraphsModuloHaveEPPA ∧
    ¬ GraphsModuloHaveCoherentEPPA) ∧
  (¬ EPPAReducts.TwoGraphs.TwoGraphsModuloHaveEPPA ∧
    ¬ TwoGraphsModuloHaveCoherentEPPA)

/-- Exact proof of the published EPPA/coherent-EPPA status table for
the five named finite reduct classes. Every positive part supplies
genuine finite coherent or ordinary witnesses; every negative part
is a formally proved no-witness statement. -/
theorem fiveReductEPPAClassification :
    FiveReductEPPAClassification := by
  exact ⟨⟨graphsHaveEPPA, graphsHaveCoherentEPPA⟩,
    ⟨finiteSetsHaveEPPA, setsHaveCoherentEPPA⟩,
    ⟨finiteTwoGraphsHaveEPPA,
      EPPAReducts.TwoGraphs.humanTwoGraphsHaveCoherentEPPA⟩,
    ⟨EPPAReducts.TwoGraphs.graphsModuloNotHaveEPPA,
      graphsModuloNotHaveCoherentEPPA⟩,
    ⟨EPPAReducts.TwoGraphs.twoGraphsModuloNotHaveEPPA,
      twoGraphsModuloNotHaveCoherentEPPA⟩⟩

end EPPAReducts.Classification
