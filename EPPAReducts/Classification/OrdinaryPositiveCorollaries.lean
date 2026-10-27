import EPPAReducts.Classification.PositiveBaselines
import EPPAReducts.TwoGraphs.FiniteCoherentEPPA

/-!
# Ordinary EPPA follows from already certified coherent positive results

These reader-facing propositions retain the usual finite common-witness
quantifier order. They are direct projections of actual coherent witness
data for finite sets and finite two-graphs, not names for a truth table.

The analogous simple-graph coherent theorem is a separate workstream.
-/

namespace EPPAReducts.Classification

open EPPAReducts.HumanTargets

/-- An ordinary EPPA witness for a finite set can be the set itself:
one choice of total permutations extends all its partial permutations. -/
def FiniteSetsHaveEPPA : Prop :=
  ∀ (V : Type), Finite V →
    ∃ extension : PartialEquiv V V → Equiv.Perm V,
      ∀ (p : PartialEquiv V V) (x : V),
        x ∈ p.source → extension p x = p x

theorem finiteSetsHaveEPPA : FiniteSetsHaveEPPA := by
  intro V hV
  letI : Finite V := hV
  obtain ⟨extension, hExt, _, _⟩ :=
    finiteSetsHaveCoherentEPPA V
  exact ⟨extension, hExt⟩

/-- Every finite two-graph has one common finite induced EPPA
witness, extending every induced partial automorphism. This is
the ordinary consequence of the independently certified coherent
two-graph construction. -/
def FiniteTwoGraphsHaveEPPA : Prop :=
  ∀ (V : Type), Finite V → ∀ (A : TwoGraph V),
    ∃ (W : Type), Finite W ∧
      ∃ (B : TwoGraph W) (ι : V ↪ W),
        IsInducedTwoGraphEmbedding A B ι ∧
        ∀ (p : PartialBijection V),
          IsTwoGraphPartialAutomorphism A p →
          ∃ (g : Equiv.Perm W),
            IsTwoGraphAutomorphism B g ∧ Extends ι p g

theorem finiteTwoGraphsHaveEPPA : FiniteTwoGraphsHaveEPPA := by
  intro V hV A
  obtain ⟨C⟩ :=
    EPPAReducts.TwoGraphs.humanTwoGraphsHaveCoherentEPPA V hV A
  refine ⟨C.W, C.finiteW, C.B, C.inclusion, C.induced, ?_⟩
  intro p hp
  exact ⟨C.extension p hp, C.isAutomorphism p hp, C.extendsOld p hp⟩

end EPPAReducts.Classification
