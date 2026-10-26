import EPPAReducts.TwoGraphs.NormalizedPartialAutomorphism

/-!
# Identity law for normalized partial two-graph automorphisms

The normalized action u_s⁻¹ ∘ id_s ∘ u_s on the fixed representative
of an induced subset s is the identity permutation.  This uses actual
subtype equivalences and does not rely on representatives being chosen
identically for different subsets.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- Normalizing the identity partial bijection on any induced
sub-two-graph gives the identity permutation of its chosen
canonical representative, even for the empty subset. -/
theorem normalizedPartialAutomorphism_identity
    {V : Type} (A : TwoGraph V) (s : Finset V) :
    normalizedPartialAutomorphism A (identityPartialBijection s)
        (identityPartialBijection_isTwoGraphPartialAutomorphism A s) =
      Equiv.refl {v : V // v ∈ canonicalInducedSubset A s} := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rw [normalizedPartialAutomorphism_val]
  change ((chosenInducedTransport A s).symm
    (chosenInducedTransport A s x)).val = x.val
  exact congrArg Subtype.val
    ((chosenInducedTransport A s).symm_apply_apply x)

/-- Transporting from a chosen representative to an induced subset
and immediately back is the identity; phrased as an Equiv law for
later cancellation of intermediate transporters. -/
theorem chosenInducedTransport_cancel
    {V : Type} (A : TwoGraph V) (s : Finset V) :
    (chosenInducedTransport A s).trans
        (chosenInducedTransport A s).symm =
      Equiv.refl {v : V // v ∈ canonicalInducedSubset A s} := by
  ext x
  simp

end EPPAReducts.TwoGraphs
