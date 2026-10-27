import EPPAReducts.TwoGraphs.RootingPartialAutomorphism

/-!
# The unconditional rooting reduction at the level of finite classes

This states the actual implication of ordinary EPPA properties of the
two unlabelled reduct classes, not just the counterexample-specialized
negative corollary. Adding a fixed isolated root to an old pair class
and deleting the root from every hypothetical induced witness gives
the implication. No class labels are named and no rooted hypothesis
is imposed on the original finite graph-modulo-complementation class.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- Ordinary EPPA for finite graphs modulo global complementation. -/
def GraphsModuloHaveEPPA : Prop :=
  ∀ (V : Type), Finite V →
    ∀ (A : GraphModuloComplementation V),
      ∃ (W : Type), Finite W ∧
        ∃ (B : GraphModuloComplementation W) (ι : V ↪ W),
          IsPairEPPAWitness A B ι

/-- **Rooting reduction.** Ordinary EPPA for all finite two-graphs
modulo global complementation implies ordinary EPPA for all finite
graphs modulo global complementation, with their genuine unlabelled
automorphism groups and induced embeddings. -/
theorem graphsModuloHaveEPPA_of_twoGraphsModulo
    (h : TwoGraphsModuloHaveEPPA) :
    GraphsModuloHaveEPPA := by
  intro V hV A
  letI : Finite V := hV
  obtain ⟨W, hW, C, ι, hC⟩ :=
    h (Option V) inferInstance (rootedOfPairClasses A)
  letI : Finite W := hW
  refine ⟨OutsideRoot (ι none), inferInstance,
    shadowAtRoot C (ι none), shadowEmbedding ι, ?_⟩
  exact shadowEPPAWitness_of_rooting
    allRootedPartialLifts A C ι hC

/-- Ordinary EPPA for the graph-modulo-complementation reduct
contradicts the verified original finite counterexample. -/
theorem graphsModuloNotHaveEPPA :
    ¬ GraphsModuloHaveEPPA := by
  intro h
  obtain ⟨V, hV, A, hno⟩ :=
    EPPAReducts.BoundedEquivalence.humanGraphsModuloComplementationFailEPPA
  obtain ⟨W, hW, B, ι, hEPPA⟩ := h V hV A
  exact hno W hW B ι hEPPA

/-- Consequently, the class of finite two-graphs modulo global
complementation does not have ordinary EPPA either. -/
theorem twoGraphsModuloNotHaveEPPA :
    ¬ TwoGraphsModuloHaveEPPA := by
  intro h
  exact graphsModuloNotHaveEPPA
    (graphsModuloHaveEPPA_of_twoGraphsModulo h)

end EPPAReducts.TwoGraphs
