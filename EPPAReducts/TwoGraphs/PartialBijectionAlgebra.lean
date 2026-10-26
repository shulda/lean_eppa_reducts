import EPPAReducts.TwoGraphs.InducedSubsetGroupSections

/-!
# Algebra of literal partial bijections

The approved HumanTargets API represents a partial bijection by an
equivalence between the subtypes of its source and target.  Coherence
uses IsComposition, which is deliberately extensional on Option-valued
partial maps rather than structural equality of representation data.

Here we verify that this extensional composition condition determines
the actual composite action at every vertex in the source.  We also
construct the identity and inverse partial automorphisms, retaining
the exact original two-graph relation.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- The identity partial bijection on one finite vertex subset. -/
def identityPartialBijection {V : Type} (s : Finset V) :
    PartialBijection V where
  source := s
  target := s
  bijection := Equiv.refl _

theorem identityPartialBijection_isTwoGraphPartialAutomorphism
    {V : Type} (A : TwoGraph V) (s : Finset V) :
    IsTwoGraphPartialAutomorphism A (identityPartialBijection s) := by
  intro x y z
  rfl

/-- Inversion exchanges source and target without adding values
outside the actual domain of the partial map. -/
def inversePartialBijection {V : Type}
    (p : PartialBijection V) : PartialBijection V where
  source := p.target
  target := p.source
  bijection := p.bijection.symm

/-- An inverse of an induced partial two-graph isomorphism is again
a partial two-graph automorphism. -/
theorem inversePartialBijection_isTwoGraphPartialAutomorphism
    {V : Type} (A : TwoGraph V)
    (p : PartialBijection V)
    (hp : IsTwoGraphPartialAutomorphism A p) :
    IsTwoGraphPartialAutomorphism A (inversePartialBijection p) := by
  intro x y z
  have h := hp (p.bijection.symm x)
    (p.bijection.symm y) (p.bijection.symm z)
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- Extensional composition of literal partial bijections implies
that the designated composite sends each source vertex to the result
of first applying p and then q.  This extracts the action on genuine
subtypes from the approved Option-valued IsComposition relation. -/
theorem isComposition_bijection_apply
    {V : Type} (p q r : PartialBijection V)
    (hcomp : IsComposition p q r)
    (x : {v : V // v ∈ p.source}) :
    (r.bijection ⟨x.val, by rw [hcomp.2.1]; exact x.property⟩).val =
      (q.bijection ⟨(p.bijection x).val,
          by rw [← hcomp.1]; exact (p.bijection x).property⟩).val := by
  classical
  have hx : x.val ∈ r.source := by
    rw [hcomp.2.1]
    exact x.property
  have hy : (p.bijection x).val ∈ q.source := by
    rw [← hcomp.1]
    exact (p.bijection x).property
  simpa [PartialBijection.apply?, x.property, hx, hy] using
    (hcomp.2.2.2 x.val)

end EPPAReducts.TwoGraphs
