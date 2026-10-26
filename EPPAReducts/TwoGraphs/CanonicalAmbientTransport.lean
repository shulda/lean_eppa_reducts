import EPPAReducts.TwoGraphs.CanonicalSubsetTransport
import EPPAReducts.TwoGraphs.PartialAutomorphismExtension

/-!
# Fixed ambient transporters for induced sub-two-graphs

For each induced subset s, the canonical choice of an isomorphism
from its representative to s is a literal partial automorphism.
Ordinary valuation EPPA extends this choice to a genuine automorphism
of the common witness. Choose that ambient automorphism ONCE per s.

We prove both the forward and inverse pointwise transport identities.
These will be the outer factors of the coherentisation formula.
No coherence or subgroup-section conclusion is claimed yet.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- One fixed ambient extension of the chosen isomorphism from
the canonical representative to a given induced subset. -/
noncomputable def canonicalSubsetAmbientTransport
    {V X : Type} [Fintype V] [DecidableEq X]
    [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (s : Finset V) : Equiv.Perm (ValuationVertex X) :=
  Classical.choose
    (exists_valuationTwoGraph_extension_of_partial A ι χ hind
      (chosenTransportPartialBijection A s)
      (chosenTransportPartialBijection_preserves A s))

/-- Every chosen transporter preserves the entire witness two-graph. -/
theorem canonicalSubsetAmbientTransport_isAutomorphism
    {V X : Type} [Fintype V] [DecidableEq X]
    [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (s : Finset V) :
    IsTwoGraphAutomorphism (valuationTwoGraph X)
      (canonicalSubsetAmbientTransport A ι χ hind s) :=
  (Classical.choose_spec
    (exists_valuationTwoGraph_extension_of_partial A ι χ hind
      (chosenTransportPartialBijection A s)
      (chosenTransportPartialBijection_preserves A s))).1

/-- On the canonical representative, the fixed ambient transporter
has precisely the prescribed action of the chosen isomorphism. -/
theorem canonicalSubsetAmbientTransport_on_representative
    {V X : Type} [Fintype V] [DecidableEq X]
    [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (s : Finset V)
    (v : {v : V // v ∈ canonicalInducedSubset A s}) :
    canonicalSubsetAmbientTransport A ι χ hind s
        (indexedTransversalEmbedding ι χ v.val) =
      indexedTransversalEmbedding ι χ
        (chosenInducedTransport A s v).val := by
  exact (Classical.choose_spec
    (exists_valuationTwoGraph_extension_of_partial A ι χ hind
      (chosenTransportPartialBijection A s)
      (chosenTransportPartialBijection_preserves A s))).2 v.val v.property

/-- The inverse transporter takes original subset vertices back to
the corresponding vertices of their canonical representative. -/
theorem canonicalSubsetAmbientTransport_symm_on_subset
    {V X : Type} [Fintype V] [DecidableEq X]
    [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (s : Finset V) (v : {v : V // v ∈ s}) :
    (canonicalSubsetAmbientTransport A ι χ hind s).symm
        (indexedTransversalEmbedding ι χ v.val) =
      indexedTransversalEmbedding ι χ
        ((chosenInducedTransport A s).symm v).val := by
  have h := canonicalSubsetAmbientTransport_on_representative
    A ι χ hind s ((chosenInducedTransport A s).symm v)
  apply (canonicalSubsetAmbientTransport A ι χ hind s).injective
  rw [Equiv.apply_symm_apply]
  simpa only [Equiv.apply_symm_apply] using h.symm

end EPPAReducts.TwoGraphs
