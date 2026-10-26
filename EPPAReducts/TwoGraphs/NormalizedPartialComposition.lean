import EPPAReducts.TwoGraphs.PartialCompositionEquiv

/-!
# Functoriality of heterogeneous canonical normalisation

The normalization of a partial isomorphism is first treated as an
equivalence between canonical representatives of its source and target.
For composable p and q, the two consecutive normalizations compose to
the normalization of r = q ∘ p, with only the canonical subset casts
needed to identify equal source/target types.

This is an exact Equiv equality under the author's literal
HumanTargets.IsComposition predicate, and no further hypotheses.
It is the typed groupoid composition law preceding coherentisation.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- Changing an induced subset by literal equality commutes with its
chosen representative-to-subset transport as an actual equivalence,
not merely after taking underlying vertex values. -/
theorem chosenInducedTransport_cast_equiv
    {V : Type} (A : TwoGraph V) {s t : Finset V}
    (hst : s = t)
    (x : {v : V // v ∈ canonicalInducedSubset A s}) :
    (chosenInducedTransport A t)
      (finsetSubtypeCastEquiv
        (congrArg (canonicalInducedSubset A) hst) x) =
    finsetSubtypeCastEquiv hst
      (chosenInducedTransport A s x) := by
  cases hst
  rfl

/-- Exact composition law of heterogeneous normalised partial
equivalences. The given IsComposition equalities provide all
three necessary domain/range casts. -/
theorem normalizedPartialEquiv_composition
    {V : Type} (A : TwoGraph V)
    (p q r : PartialBijection V)
    (h : IsComposition p q r) :
    ((normalizedPartialEquiv A p).trans
      (finsetSubtypeCastEquiv
        (congrArg (canonicalInducedSubset A) h.1))).trans
        (normalizedPartialEquiv A q) =
    ((finsetSubtypeCastEquiv
      (congrArg (canonicalInducedSubset A) h.2.1.symm)).trans
        (normalizedPartialEquiv A r)).trans
      (finsetSubtypeCastEquiv
        (congrArg (canonicalInducedSubset A) h.2.2.1)) := by
  apply Equiv.ext
  intro x
  apply (chosenInducedTransport A q.target).injective
  simp only [Equiv.trans_apply]
  rw [normalizedPartialEquiv_transport A q]
  rw [chosenInducedTransport_cast_equiv A h.1]
  rw [normalizedPartialEquiv_transport A p]
  rw [chosenInducedTransport_cast_equiv A h.2.2.1]
  rw [normalizedPartialEquiv_transport A r]
  rw [chosenInducedTransport_cast_equiv A h.2.1.symm]
  have hc := congrArg
    (fun f : {v : V // v ∈ p.source} ≃
        {v : V // v ∈ q.target} =>
      f (chosenInducedTransport A p.source x))
    (isComposition_subtypeEquiv p q r h)
  simpa only [Equiv.trans_apply] using hc

end EPPAReducts.TwoGraphs
