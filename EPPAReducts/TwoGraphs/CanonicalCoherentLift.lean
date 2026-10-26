import EPPAReducts.TwoGraphs.CanonicalMiddleLiftComposition

/-!
# Coherent extension candidate by fixed outer conjugation

An induced partial isomorphism is carried to its chosen canonical
representative, extended by the fixed homomorphic middle section,
and transported back. Every factor is an actual automorphism of
the common finite valuation two-graph.

This module proves the ambient preservation and extension conditions.
Functoriality is treated separately.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- The inverse of an automorphism of a two-graph is an automorphism. -/
theorem ambientTwoGraphAutomorphism_symm
    {W : Type} (B : TwoGraph W) (g : Equiv.Perm W)
    (hg : IsTwoGraphAutomorphism B g) :
    IsTwoGraphAutomorphism B g.symm := by
  intro x y z
  have h := hg (g.symm x) (g.symm y) (g.symm z)
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- Automorphisms of a two-graph compose in application order. -/
theorem ambientTwoGraphAutomorphism_trans
    {W : Type} (B : TwoGraph W) (g h : Equiv.Perm W)
    (hg : IsTwoGraphAutomorphism B g)
    (hh : IsTwoGraphAutomorphism B h) :
    IsTwoGraphAutomorphism B (g.trans h) := by
  intro x y z
  exact (hg x y z).trans (hh (g x) (g y) (g z))

/-- The fixed candidate for coherent extension of a literal partial
automorphism. All choices depend only on the domain, codomain
and the partial map, and use one common valuation witness. -/
noncomputable def canonicalConjugatedLift
    {V X : Type} [Fintype V] [Fintype X]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (hdiv : ∀ s : Finset V, s.Nonempty →
      Fintype.card {v : V // v ∈ s} ∣ Fintype.card X)
    (p : PartialBijection V)
    (hp : IsTwoGraphPartialAutomorphism A p) :
    Equiv.Perm (ValuationVertex X) :=
  ((canonicalSubsetAmbientTransport A ι χ hind p.source).symm.trans
    (canonicalMiddleLift A ι χ hind hdiv p hp)).trans
    (canonicalSubsetAmbientTransport A ι χ hind p.target)

/-- The conjugated lift preserves the full witness relation. -/
theorem canonicalConjugatedLift_isAutomorphism
    {V X : Type} [Fintype V] [Fintype X]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (hdiv : ∀ s : Finset V, s.Nonempty →
      Fintype.card {v : V // v ∈ s} ∣ Fintype.card X)
    (p : PartialBijection V)
    (hp : IsTwoGraphPartialAutomorphism A p) :
    IsTwoGraphAutomorphism (valuationTwoGraph X)
      (canonicalConjugatedLift A ι χ hind hdiv p hp) := by
  exact ambientTwoGraphAutomorphism_trans (valuationTwoGraph X) _ _ 
    (ambientTwoGraphAutomorphism_trans (valuationTwoGraph X) _ _
      (ambientTwoGraphAutomorphism_symm (valuationTwoGraph X) _
        (canonicalSubsetAmbientTransport_isAutomorphism A ι χ hind p.source))
      (canonicalMiddleLift_isAutomorphism A ι χ hind hdiv p hp))
    (canonicalSubsetAmbientTransport_isAutomorphism A ι χ hind p.target)

/-- On the original embedded vertices, the conjugated ambient
automorphism extends exactly the given literal partial bijection. -/
theorem canonicalConjugatedLift_extendsOld
    {V X : Type} [Fintype V] [Fintype X]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (hdiv : ∀ s : Finset V, s.Nonempty →
      Fintype.card {v : V // v ∈ s} ∣ Fintype.card X)
    (p : PartialBijection V)
    (hp : IsTwoGraphPartialAutomorphism A p) :
    Extends (indexedTransversalEmbedding ι χ) p
      (canonicalConjugatedLift A ι χ hind hdiv p hp) := by
  intro v hv
  let x : {v : V // v ∈ canonicalInducedSubset A p.source} :=
    (chosenInducedTransport A p.source).symm ⟨v, hv⟩
  let y := (normalizedPartialAutomorphism A p hp) x
  let hc := canonicalInducedSubset_eq_of_partial A p hp
  have hs :
      (canonicalSubsetAmbientTransport A ι χ hind p.source).symm
        (indexedTransversalEmbedding ι χ v) =
      indexedTransversalEmbedding ι χ x.val :=
    canonicalSubsetAmbientTransport_symm_on_subset
      A ι χ hind p.source ⟨v, hv⟩
  have hm :
      canonicalMiddleLift A ι χ hind hdiv p hp
        (indexedTransversalEmbedding ι χ x.val) =
      indexedTransversalEmbedding ι χ y.val :=
    canonicalMiddleLift_on_representative A ι χ hind hdiv p hp x
  have ht :
      canonicalSubsetAmbientTransport A ι χ hind p.target
        (indexedTransversalEmbedding ι χ y.val) =
      indexedTransversalEmbedding ι χ
        ((chosenInducedTransport A p.target)
          (finsetSubtypeCastEquiv hc y)).val := by
    rw [← finsetSubtypeCastEquiv_val hc y]
    exact canonicalSubsetAmbientTransport_on_representative
      A ι χ hind p.target (finsetSubtypeCastEquiv hc y)
  have hn :
      (chosenInducedTransport A p.target)
        (finsetSubtypeCastEquiv hc y) = p.bijection ⟨v, hv⟩ := by
    simpa only [x, y, hc, Equiv.apply_symm_apply] using
      (normalizedPartialAutomorphism_transport A p hp x)
  calc
    canonicalConjugatedLift A ι χ hind hdiv p hp
        (indexedTransversalEmbedding ι χ v) =
      canonicalSubsetAmbientTransport A ι χ hind p.target
        (canonicalMiddleLift A ι χ hind hdiv p hp
          ((canonicalSubsetAmbientTransport A ι χ hind p.source).symm
            (indexedTransversalEmbedding ι χ v))) := rfl
    _ = canonicalSubsetAmbientTransport A ι χ hind p.target
        (canonicalMiddleLift A ι χ hind hdiv p hp
          (indexedTransversalEmbedding ι χ x.val)) := by rw [hs]
    _ = canonicalSubsetAmbientTransport A ι χ hind p.target
        (indexedTransversalEmbedding ι χ y.val) := by rw [hm]
    _ = indexedTransversalEmbedding ι χ
        ((chosenInducedTransport A p.target)
          (finsetSubtypeCastEquiv hc y)).val := ht
    _ = indexedTransversalEmbedding ι χ
        (p.bijection ⟨v, hv⟩).val := by rw [hn]

end EPPAReducts.TwoGraphs
