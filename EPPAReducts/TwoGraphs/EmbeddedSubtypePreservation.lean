import EPPAReducts.TwoGraphs.FactorialRootedWitness
import EPPAReducts.TwoGraphs.DivisibleTransversalSection

/-!
# Induced substructure automorphisms preserve embedded transversals

Suppose A is induced in the actual valuation two-graph C_X over an
injective index map ι : V ↪ X with valuations χ.  Any permutation of
an induced subset s of V preserving the literal two-graph triple
relation also preserves the exact raw valuation-parity relation
required by the certified divisible-transversal subgroup section.

This is a genuine bridge from the approved HumanTargets induced
embedding to the internal preservation predicate. It has no
divisibility or subgroup-section hypothesis of its own.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- Induced isomorphisms of a chosen old substructure preserve the
corresponding valuation-transversal parity in the witness. -/
theorem preservesEmbeddedTransversal_of_inducedSubtype
    {V X : Type} [DecidableEq X]
    [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V)
    (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (s : Finset V)
    (p : Equiv.Perm {v : V // v ∈ s})
    (hp : ∀ x y z : {v : V // v ∈ s},
      A.isTriple (triple x.val y.val z.val) =
        A.isTriple (triple (p x).val (p y).val (p z).val)) :
    PreservesEmbeddedTransversal
      ((subtypeEmbedding s).trans ι) (fun v => χ v.val) p := by
  intro x y z
  have hsource := hind x.val y.val z.val
  have htarget := hind (p x).val (p y).val (p z).val
  rw [valuationTwoGraph_triple_eq_vertexParity] at hsource htarget
  change A.isTriple (triple x.val y.val z.val) =
    rawTripleParity (ι x.val) (ι y.val) (ι z.val)
      (χ x.val) (χ y.val) (χ z.val) at hsource
  change A.isTriple
    (triple (p x).val (p y).val (p z).val) =
    rawTripleParity (ι (p x).val) (ι (p y).val) (ι (p z).val)
      (χ (p x).val) (χ (p y).val) (χ (p z).val) at htarget
  change rawTripleParity (ι x.val) (ι y.val) (ι z.val)
      (χ x.val) (χ y.val) (χ z.val) =
    rawTripleParity (ι (p x).val) (ι (p y).val) (ι (p z).val)
      (χ (p x).val) (χ (p y).val) (χ (p z).val)
  exact hsource.symm.trans ((hp x y z).trans htarget)

end EPPAReducts.TwoGraphs
