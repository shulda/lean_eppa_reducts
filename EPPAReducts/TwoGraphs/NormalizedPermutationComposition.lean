import EPPAReducts.TwoGraphs.NormalizedPartialComposition

/-!
# Composition of normalized partial automorphisms on one representative

The heterogeneous groupoid composition law is now transported to
permutations of a common representative.  All equality casts preserve
the underlying vertex, and proof irrelevance ensures that the choice
of an equality proof does not change any resulting permutation.

The statement below is exactly what the chosen homomorphic subgroup
section needs in the coherentisation formula: normalized p followed
by normalized q agrees with normalized r, up to explicit conjugation
by the fixed casts identifying their canonical representative carriers.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- The inverse of the subtype equivalence induced by a literal
equality is the equivalence induced by the reversed equality. -/
theorem finsetSubtypeCastEquiv_symm
    {V : Type} {s t : Finset V} (h : s = t) :
    (finsetSubtypeCastEquiv h).symm =
      finsetSubtypeCastEquiv h.symm := by
  cases h
  rfl

/-- The canonical normalized permutations satisfy composition once
each canonical representative is transported into the source
representative of p.  The extra equality witnesses are implied by
the hypotheses, but are exposed here to keep the subtype casts clear. -/
theorem normalizedPartialAutomorphism_composition_cast
    {V : Type} (A : TwoGraph V)
    (p q r : PartialBijection V)
    (hp : IsTwoGraphPartialAutomorphism A p)
    (hq : IsTwoGraphPartialAutomorphism A q)
    (hr : IsTwoGraphPartialAutomorphism A r)
    (h : IsComposition p q r)
    (hmid : canonicalInducedSubset A p.source =
        canonicalInducedSubset A q.source)
    (hsrc : canonicalInducedSubset A p.source =
        canonicalInducedSubset A r.source) :
    (normalizedPartialAutomorphism A p hp).trans
      (((finsetSubtypeCastEquiv hmid).trans
        (normalizedPartialAutomorphism A q hq)).trans
        (finsetSubtypeCastEquiv hmid).symm) =
      ((finsetSubtypeCastEquiv hsrc).trans
        (normalizedPartialAutomorphism A r hr)).trans
        (finsetSubtypeCastEquiv hsrc).symm := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  have hmidCast :
      finsetSubtypeCastEquiv hmid
        (finsetSubtypeCastEquiv
          (canonicalInducedSubset_eq_of_partial A p hp).symm
          ((normalizedPartialEquiv A p) x)) =
      finsetSubtypeCastEquiv
        (congrArg (canonicalInducedSubset A) h.1)
        ((normalizedPartialEquiv A p) x) := by
    apply Subtype.ext
    simp only [finsetSubtypeCastEquiv_val]
  have hsrcCast :
      finsetSubtypeCastEquiv hsrc x =
        finsetSubtypeCastEquiv
          (congrArg (canonicalInducedSubset A) h.2.1.symm) x := by
    apply Subtype.ext
    simp only [finsetSubtypeCastEquiv_val]
  have hc :
      ((normalizedPartialEquiv A q)
        (finsetSubtypeCastEquiv
          (congrArg (canonicalInducedSubset A) h.1)
          ((normalizedPartialEquiv A p) x))).val =
      ((normalizedPartialEquiv A r)
        (finsetSubtypeCastEquiv
          (congrArg (canonicalInducedSubset A) h.2.1.symm) x)).val := by
    have heq := congrArg
      (fun f : {v : V // v ∈ canonicalInducedSubset A p.source} ≃
          {v : V // v ∈ canonicalInducedSubset A q.target} =>
        (f x).val)
      (normalizedPartialEquiv_composition A p q r h)
    simpa only [Equiv.trans_apply, finsetSubtypeCastEquiv_val] using heq
  simp only [Equiv.trans_apply,
    normalizedPartialAutomorphism_eq_equiv_cast,
    finsetSubtypeCastEquiv_symm, finsetSubtypeCastEquiv_val]
  rw [hmidCast, hsrcCast]
  exact hc

end EPPAReducts.TwoGraphs
