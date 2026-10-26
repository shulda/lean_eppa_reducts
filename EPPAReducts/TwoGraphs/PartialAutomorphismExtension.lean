import EPPAReducts.TwoGraphs.IndexedTransversalExtension

/-!
# Ordinary EPPA for induced valuation-transversal copies

An induced copy of an arbitrary two-graph A in the valuation witness C_X
is a transversal over an injective index map.  Every literal partial
automorphism of A gives an isomorphism between finite injected source
and target transversals.  The indexed-transversal extension theorem
therefore produces a genuine automorphism of the common finite witness.

The target here uses exactly the approved HumanTargets partial-bijection
API, not an auxiliary total permutation of the old carrier.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- Every partial automorphism of an induced transversal copy of A
extends to an automorphism of the whole actual valuation two-graph. -/
theorem exists_valuationTwoGraph_extension_of_partial
    {V X : Type} [Fintype V] [DecidableEq X]
    [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (p : PartialBijection V)
    (hp : IsTwoGraphPartialAutomorphism A p) :
    ∃ g : Equiv.Perm (ValuationVertex X),
      IsTwoGraphAutomorphism (valuationTwoGraph X) g ∧
      Extends (indexedTransversalEmbedding ι χ) p g := by
  classical
  let ιs : {v : V // v ∈ p.source} ↪ X :=
    (subtypeEmbedding p.source).trans ι
  let τs : {v : V // v ∈ p.source} ↪ X :=
    (equivThenEmbedding p.bijection
      (subtypeEmbedding p.target)).trans ι
  let χs : {v : V // v ∈ p.source} → Valuation X :=
    fun d => χ d.val
  let ηs : {v : V // v ∈ p.source} → Valuation X :=
    fun d => χ (p.bijection d).val
  have hpres (d e f : {v : V // v ∈ p.source}) :
      (valuationTwoGraph X).isTriple
        (triple (ιs d, valuationClass (χs d))
                (ιs e, valuationClass (χs e))
                (ιs f, valuationClass (χs f))) =
      (valuationTwoGraph X).isTriple
        (triple (τs d, valuationClass (ηs d))
                (τs e, valuationClass (ηs e))
                (τs f, valuationClass (ηs f))) := by
    change (valuationTwoGraph X).isTriple
        (triple (ι d.val, valuationClass (χ d.val))
                (ι e.val, valuationClass (χ e.val))
                (ι f.val, valuationClass (χ f.val))) =
      (valuationTwoGraph X).isTriple
        (triple (ι (p.bijection d).val,
                  valuationClass (χ (p.bijection d).val))
                (ι (p.bijection e).val,
                  valuationClass (χ (p.bijection e).val))
                (ι (p.bijection f).val,
                  valuationClass (χ (p.bijection f).val)))
    exact ((hind d.val e.val f.val).symm).trans
      ((hp d e f).trans
        (hind (p.bijection d).val (p.bijection e).val
          (p.bijection f).val))
  obtain ⟨g, hg, hmaps⟩ :=
    exists_twoGraphAutomorphism_extending_indexedTransversalIso
      ιs τs χs ηs hpres
  refine ⟨g, hg, ?_⟩
  intro v hv
  exact hmaps ⟨v, hv⟩

end EPPAReducts.TwoGraphs
