import EPPAReducts.TwoGraphs.TransporterComposition

/-!
# Heterogeneous normalization of literal partial isomorphisms

Before identifying the canonical representatives of the source and
target of a partial isomorphism, its normalization is naturally an
equivalence *between* those representatives.  This definition does
not depend on any proof that the partial map preserves the relation.

The already certified normalized automorphism is exactly this
heterogeneous equivalence followed by a cast through the equality of
the two canonical representative subsets.  This separation makes the
composition law a type-correct equivalence-of-groupoids statement.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- Normalize a partial bijection as an equivalence from the
canonical representative of its source to the canonical
representative of its target, before equating those two carriers. -/
noncomputable def normalizedPartialEquiv
    {V : Type} (A : TwoGraph V) (p : PartialBijection V) :
    {v : V // v ∈ canonicalInducedSubset A p.source} ≃
      {v : V // v ∈ canonicalInducedSubset A p.target} :=
  ((chosenInducedTransport A p.source).trans p.bijection).trans
    (chosenInducedTransport A p.target).symm

/-- The original normalized automorphism is the normalized
heterogeneous equivalence, followed by the cast from the
target representative back to the source representative. -/
theorem normalizedPartialAutomorphism_eq_equiv_cast
    {V : Type} (A : TwoGraph V)
    (p : PartialBijection V)
    (hp : IsTwoGraphPartialAutomorphism A p) :
    normalizedPartialAutomorphism A p hp =
      (normalizedPartialEquiv A p).trans
        (finsetSubtypeCastEquiv
          (canonicalInducedSubset_eq_of_partial A p hp).symm) := by
  rfl

/-- Pointwise form of the heterogeneous normalized equivalence,
without any proof-carrying casts. -/
theorem normalizedPartialEquiv_val
    {V : Type} (A : TwoGraph V)
    (p : PartialBijection V)
    (x : {v : V // v ∈ canonicalInducedSubset A p.source}) :
    ((normalizedPartialEquiv A p) x).val =
      ((chosenInducedTransport A p.target).symm
        (p.bijection (chosenInducedTransport A p.source x))).val := by
  rfl

/-- The defining commutative square: after source-to-target
normalization, the chosen target transport gives exactly the
original partial bijection applied to the chosen source transport. -/
theorem normalizedPartialEquiv_transport
    {V : Type} (A : TwoGraph V) (p : PartialBijection V)
    (x : {v : V // v ∈ canonicalInducedSubset A p.source}) :
    (chosenInducedTransport A p.target)
      ((normalizedPartialEquiv A p) x) =
    p.bijection (chosenInducedTransport A p.source x) := by
  change (chosenInducedTransport A p.target)
      ((chosenInducedTransport A p.target).symm
        (p.bijection (chosenInducedTransport A p.source x))) =
    p.bijection (chosenInducedTransport A p.source x)
  exact (chosenInducedTransport A p.target).apply_symm_apply _

end EPPAReducts.TwoGraphs
