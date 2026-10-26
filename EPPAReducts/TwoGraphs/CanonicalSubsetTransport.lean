import EPPAReducts.TwoGraphs.InducedSubsetIsomorphism

/-!
# Canonical transporters for induced sub-two-graphs

The chosen representative of an induced-isomorphism class is itself
induced-isomorphic to each object in its class.  Choose, once per
vertex subset s, a specific relation-preserving bijection from its
canonical representative to s.

Package that choice as a literal HumanTargets.PartialBijection.
These transporters will later be extended to ambient automorphisms
by the certified ordinary EPPA theorem, and used in coherentisation.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- Every vertex subset is isomorphic, via the actual triple
relation, to its canonical class representative. -/
theorem canonicalInducedSubset_iso {V : Type}
    (A : TwoGraph V) (s : Finset V) :
    IsomorphicInducedSubsets A (canonicalInducedSubset A s) s := by
  exact Quotient.exact
    (Quotient.out_eq (Quotient.mk (inducedSubsetIsoSetoid A) s))

/-- One fixed isomorphism from the selected representative to s. -/
noncomputable def chosenInducedTransport {V : Type}
    (A : TwoGraph V) (s : Finset V) :
    {v : V // v ∈ canonicalInducedSubset A s} ≃
      {v : V // v ∈ s} :=
  Classical.choose (canonicalInducedSubset_iso A s)

/-- The chosen transporter genuinely preserves all original triples. -/
theorem chosenInducedTransport_preserves {V : Type}
    (A : TwoGraph V) (s : Finset V) :
    ∀ x y z : {v : V // v ∈ canonicalInducedSubset A s},
      A.isTriple (triple x.val y.val z.val) =
        A.isTriple
          (triple (chosenInducedTransport A s x).val
                  (chosenInducedTransport A s y).val
                  (chosenInducedTransport A s z).val) :=
  Classical.choose_spec (canonicalInducedSubset_iso A s)

/-- A literal partial bijection from the selected representative
to the given induced vertex subset. -/
noncomputable def chosenTransportPartialBijection {V : Type}
    (A : TwoGraph V) (s : Finset V) : PartialBijection V where
  source := canonicalInducedSubset A s
  target := s
  bijection := chosenInducedTransport A s

/-- The chosen transporter is a partial automorphism of A in the
exact approved HumanTargets interface. -/
theorem chosenTransportPartialBijection_preserves {V : Type}
    (A : TwoGraph V) (s : Finset V) :
    IsTwoGraphPartialAutomorphism A
      (chosenTransportPartialBijection A s) := by
  exact chosenInducedTransport_preserves A s

/-- The source and target of any literal partial automorphism
have exactly the same chosen representative. -/
theorem canonicalInducedSubset_eq_of_partial {V : Type}
    (A : TwoGraph V) (p : PartialBijection V)
    (hp : IsTwoGraphPartialAutomorphism A p) :
    canonicalInducedSubset A p.source =
      canonicalInducedSubset A p.target := by
  apply canonicalInducedSubset_eq_of_iso A p.source p.target
  exact ⟨p.bijection, hp⟩

end EPPAReducts.TwoGraphs
