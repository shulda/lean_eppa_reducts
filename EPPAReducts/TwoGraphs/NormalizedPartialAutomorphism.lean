import EPPAReducts.TwoGraphs.PartialBijectionAlgebra
import EPPAReducts.TwoGraphs.CanonicalSubsetTransport

/-!
# Normalizing partial isomorphisms to automorphisms of representatives

For a partial isomorphism p : E -> F, the chosen class representative
R_E is literally equal to R_F (by the already certified setoid lemma).
Transport p by the fixed isomorphisms R_E -> E and R_F -> F and
convert that equality into a genuine permutation of R_E.

This is the middle group element of the coherentisation formula.
We prove that it preserves the original induced two-graph relation.
Its identity/composition algebra is the next separate obligation.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- Equal finite subsets have definitionally corresponding subtype
carriers, with an equivalence that fixes the underlying vertex. -/
def finsetSubtypeCastEquiv {V : Type} {s t : Finset V}
    (h : s = t) : {v : V // v ∈ s} ≃ {v : V // v ∈ t} := by
  cases h
  exact Equiv.refl _

@[simp] theorem finsetSubtypeCastEquiv_val
    {V : Type} {s t : Finset V} (h : s = t)
    (x : {v : V // v ∈ s}) :
    (finsetSubtypeCastEquiv h x).val = x.val := by
  cases h
  rfl

/-- The induced partial isomorphism p becomes a total permutation
of the fixed representative of its source isomorphism class. -/
noncomputable def normalizedPartialAutomorphism {V : Type}
    (A : TwoGraph V) (p : PartialBijection V)
    (hp : IsTwoGraphPartialAutomorphism A p) :
    Equiv.Perm {v : V // v ∈ canonicalInducedSubset A p.source} :=
  (((chosenInducedTransport A p.source).trans p.bijection).trans
      (chosenInducedTransport A p.target).symm).trans
    (finsetSubtypeCastEquiv
      (canonicalInducedSubset_eq_of_partial A p hp).symm)

/-- The normalized permutation applies the selected source
transporter, p, and the inverse target transporter, in that order.
The final finite-subset equality changes no underlying vertex. -/
theorem normalizedPartialAutomorphism_val {V : Type}
    (A : TwoGraph V) (p : PartialBijection V)
    (hp : IsTwoGraphPartialAutomorphism A p)
    (x : {v : V // v ∈ canonicalInducedSubset A p.source}) :
    ((normalizedPartialAutomorphism A p hp) x).val =
      ((chosenInducedTransport A p.target).symm
        (p.bijection (chosenInducedTransport A p.source x))).val := by
  simp only [normalizedPartialAutomorphism, Equiv.trans_apply,
    finsetSubtypeCastEquiv_val]

/-- The normalized permutation is a genuine automorphism of the
canonical induced two-graph, so the homomorphic subgroup section
can be applied to it. -/
theorem normalizedPartialAutomorphism_preserves {V : Type}
    (A : TwoGraph V) (p : PartialBijection V)
    (hp : IsTwoGraphPartialAutomorphism A p) :
    PreservesInducedSubset A (canonicalInducedSubset A p.source)
      (normalizedPartialAutomorphism A p hp) := by
  intro x y z
  let us := chosenInducedTransport A p.source
  let ut := chosenInducedTransport A p.target
  have hs := chosenInducedTransport_preserves A p.source x y z
  have hm := hp (us x) (us y) (us z)
  have ht := chosenInducedTransport_preserves A p.target
    (ut.symm (p.bijection (us x)))
    (ut.symm (p.bijection (us y)))
    (ut.symm (p.bijection (us z)))
  have hx : ut (ut.symm (p.bijection (us x))) = p.bijection (us x) :=
    ut.apply_symm_apply _
  have hy : ut (ut.symm (p.bijection (us y))) = p.bijection (us y) :=
    ut.apply_symm_apply _
  have hz : ut (ut.symm (p.bijection (us z))) = p.bijection (us z) :=
    ut.apply_symm_apply _
  rw [hx, hy, hz] at ht
  have hchain := hs.trans (hm.trans ht.symm)
  simpa only [normalizedPartialAutomorphism_val] using hchain

end EPPAReducts.TwoGraphs
