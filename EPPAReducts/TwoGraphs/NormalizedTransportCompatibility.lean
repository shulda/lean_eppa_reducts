import EPPAReducts.TwoGraphs.NormalizedPartialIdentity

/-!
# Compatibility of normalization with the chosen partial transports

The normalized automorphism a_p of the canonical representative
satisfies u_target(a_p(x)) = p(u_source(x)), with the equality of the
canonical source and target subsets handled by an explicit subtype
cast. This is the pointwise equation needed in the composition proof.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- The normalized action, transported to the target representative,
agrees *exactly* with the original partial isomorphism between
the chosen copies. -/
theorem normalizedPartialAutomorphism_transport
    {V : Type} (A : TwoGraph V) (p : PartialBijection V)
    (hp : IsTwoGraphPartialAutomorphism A p)
    (x : {v : V // v ∈ canonicalInducedSubset A p.source}) :
    (chosenInducedTransport A p.target)
      (finsetSubtypeCastEquiv
        (canonicalInducedSubset_eq_of_partial A p hp)
        ((normalizedPartialAutomorphism A p hp) x)) =
    p.bijection (chosenInducedTransport A p.source x) := by
  let h := canonicalInducedSubset_eq_of_partial A p hp
  have hcast :
      finsetSubtypeCastEquiv h
        ((normalizedPartialAutomorphism A p hp) x) =
        (chosenInducedTransport A p.target).symm
          (p.bijection (chosenInducedTransport A p.source x)) := by
    apply Subtype.ext
    calc
      (finsetSubtypeCastEquiv h
        ((normalizedPartialAutomorphism A p hp) x)).val =
          ((normalizedPartialAutomorphism A p hp) x).val :=
            finsetSubtypeCastEquiv_val h _
      _ = ((chosenInducedTransport A p.target).symm
          (p.bijection (chosenInducedTransport A p.source x))).val :=
            normalizedPartialAutomorphism_val A p hp x
  change (chosenInducedTransport A p.target)
      (finsetSubtypeCastEquiv h
        ((normalizedPartialAutomorphism A p hp) x)) =
    p.bijection (chosenInducedTransport A p.source x)
  rw [hcast]
  exact (chosenInducedTransport A p.target).apply_symm_apply _

end EPPAReducts.TwoGraphs
