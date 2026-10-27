import EPPAReducts.TwoGraphs.RootShadowAutomorphism
import EPPAReducts.BoundedEquivalence.UnorderedNoEPPAWitness

/-!
# Rooting transfer: one explicit remaining partial-automorphism obligation

The only additional requirement for the full root-shadow EPPA
reduction is that each *genuine* partial automorphism of an
unlabelled pair-equivalence induces a genuine partial automorphism
of the rooted triple equivalence. It is explicitly a hypothesis in
this module, rather than an axiom or an unproved theorem.

Once this bridge is discharged by an independent proof, the rest
of the transfer and the finite negative obstruction are unconditional.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets
open EPPAReducts.BoundedEquivalence

/-- The exact missing geometric parity/partial-map bridge. -/
def RootedPartialLiftProperty : Prop :=
  ∀ (V : Type) (A : GraphModuloComplementation V)
    (p : PartialBijection V),
    IsPairPartialAutomorphism A p →
      IsTripleClassPartialAutomorphism
        (rootedOfPairClasses A) (liftRootPartial p)

/-- Conditional but complete transfer of an actual common rooted
triple-class EPPA witness to an actual pair-class EPPA witness.
There is no conditional assumption about the ambient witness. -/
theorem shadowEPPAWitness_of_rooting
    (hLift : RootedPartialLiftProperty)
    {V W : Type}
    (A : GraphModuloComplementation V)
    (C : TwoGraphModuloComplementation W)
    (ι : Option V ↪ W)
    (hC : IsTripleClassEPPAWitness (rootedOfPairClasses A) C ι) :
    IsPairEPPAWitness A (shadowAtRoot C (ι none))
      (shadowEmbedding ι) := by
  refine ⟨inducedPairShadow_of_inducedRootedTriples A C ι hC.1, ?_⟩
  intro p hp
  obtain ⟨g, hg, hext⟩ :=
    hC.2 (liftRootPartial p) (hLift V A p hp)
  have hfix : g (ι none) = ι none :=
    extends_liftRootPartial_fixesRoot ι p g hext
  exact ⟨restrictAutToOutside (ι none) g hfix,
    restrictAutToOutside_isPairAutomorphism C (ι none) g hfix hg,
    restrictAutToOutside_extendsOld ι p g hext⟩

/-- A genuinely proved explicit negative construction from the
rooting partial-map property: the old graph non-EPPA obstruction
becomes a rooted unlabelled triple non-EPPA obstruction. This is
a conditional theorem, not yet the fully certified final result. -/
theorem twoGraphsModuloFailEPPA_of_rooting
    (hLift : RootedPartialLiftProperty) :
    TwoGraphsModuloFailEPPA := by
  obtain ⟨V, hV, A, hno⟩ :=
    EPPAReducts.BoundedEquivalence.humanGraphsModuloComplementationFailEPPA
  letI : Finite V := hV
  refine ⟨Option V, inferInstance, rootedOfPairClasses A, ?_⟩
  intro W hW C ι hC
  letI : Finite W := hW
  have hshadow : IsPairEPPAWitness A
      (shadowAtRoot C (ι none)) (shadowEmbedding ι) :=
    shadowEPPAWitness_of_rooting hLift A C ι hC
  exact hno (OutsideRoot (ι none)) inferInstance
    (shadowAtRoot C (ι none)) (shadowEmbedding ι) hshadow

end EPPAReducts.TwoGraphs
