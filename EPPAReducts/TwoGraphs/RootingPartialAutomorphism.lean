import EPPAReducts.TwoGraphs.RootingPairGauge
import EPPAReducts.TwoGraphs.RootingTransfer

/-!
# Actual rooting lift for unlabelled graph partial automorphisms

We now remove the sole hypothesis in RootingTransfer. A genuine
unlabelled pair-equivalence partial automorphism acts by one
Boolean class shift on every pair in its source. Its root-fixing lift
then acts by that same shift on every unordered triple in its source,
including the triples through the root. The finite-set transport
uses the audited gauge-parity identity.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets
open EPPAReducts.BoundedEquivalence

private theorem boolBit_injective_root :
    Function.Injective boolBit := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolBit]

/-- Every genuine unlabelled graph-modulo-complementation partial
automorphism, with one root adjoined and fixed, is a literal
partial automorphism of the unlabelled triple-class rooted structure. -/
theorem rootedPartialLift_isPartialAutomorphism
    {V : Type}
    (A : GraphModuloComplementation V)
    (p : PartialBijection V)
    (hp : IsPairPartialAutomorphism A p) :
    IsTripleClassPartialAutomorphism
      (rootedOfPairClasses A) (liftRootPartial p) := by
  classical
  let c : UnorderedPairs V → Bool :=
    Classical.choose A.atMostTwoClasses
  have hc : ∀ e f : UnorderedPairs V,
      A.sameClass.r e f ↔ c e = c f :=
    Classical.choose_spec A.atMostTwoClasses
  obtain ⟨δ, hshift⟩ := pairPartialHasGlobalShift A c hc p hp
  let src : RootLiftDomain p ↪ Option V := rootLiftSource p
  let dst : RootLiftDomain p ↪ Option V := rootLiftTarget p
  have hbits (s : UnorderedTriples (RootLiftDomain p)) :
      boolBit ((rootedTwoGraph c).isTriple (mapRSubset dst s).val) =
        boolBit ((rootedTwoGraph c).isTriple (mapRSubset src s).val) +
          boolBit δ := by
    change boolBit (pairParityTriple (rootedPairBit c)
      (s.val.map dst)) =
        boolBit (pairParityTriple (rootedPairBit c)
          (s.val.map src)) + boolBit δ
    exact pairParityTriple_map_gauge
      (rootedPairBit c) src dst (boolBit δ) (rootGauge p δ)
      (rootLift_pairGauge c p δ hshift) s.val s.property
  intro e f
  change (rootedTwoGraph c).isTriple (mapRSubset src e).val =
        (rootedTwoGraph c).isTriple (mapRSubset src f).val ↔
      (rootedTwoGraph c).isTriple (mapRSubset dst e).val =
        (rootedTwoGraph c).isTriple (mapRSubset dst f).val
  constructor
  · intro heq
    apply boolBit_injective_root
    rw [hbits e, hbits f, heq]
  · intro heq
    have hb := congrArg boolBit heq
    rw [hbits e, hbits f] at hb
    exact boolBit_injective_root (add_right_cancel hb)

/-- The exact previously isolated rooting-lift obligation, without
additional hypotheses. -/
theorem allRootedPartialLifts :
    RootedPartialLiftProperty := by
  intro V A p hp
  exact rootedPartialLift_isPartialAutomorphism A p hp

/-- The fifth reduct, two-graphs modulo global complementation,
fails ordinary EPPA unconditionally. The result rules out every
finite induced EPPA witness for one explicit finite rooted object. -/
theorem twoGraphsModuloFailEPPA :
    TwoGraphsModuloFailEPPA :=
  twoGraphsModuloFailEPPA_of_rooting allRootedPartialLifts

end EPPAReducts.TwoGraphs
