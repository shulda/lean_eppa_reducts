import EPPAReducts.TwoGraphs.NormalizedPartialEquiv

/-!
# Exact composition of the equivalences represented by partial maps

The approved HumanTargets.IsComposition predicate specifies extensional
composition of partial maps by Option.bind. When its sources and
targets match, the bijection of r is therefore exactly that of
p followed by q, after explicit casts of the equal finite domains.

This is a genuinely typed equation of Equiv objects, not only a
pointwise fact about optional values. It will feed directly into the
composition law for heterogeneous normalized partial equivalences.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- The approved option-valued partial-map composition law implies
strict equality of the corresponding total subtype equivalences,
after transporting source, intermediate and target types along the
equalities supplied by IsComposition. -/
theorem isComposition_subtypeEquiv
    {V : Type} (p q r : PartialBijection V)
    (h : IsComposition p q r) :
    (p.bijection.trans (finsetSubtypeCastEquiv h.1)).trans
        q.bijection =
      ((finsetSubtypeCastEquiv h.2.1.symm).trans
        r.bijection).trans (finsetSubtypeCastEquiv h.2.2.1) := by
  classical
  apply Equiv.ext
  intro x
  apply Subtype.ext
  have hleft :
      finsetSubtypeCastEquiv h.1 (p.bijection x) =
        (⟨(p.bijection x).val, by
          rw [← h.1]
          exact (p.bijection x).property⟩ :
          {v : V // v ∈ q.source}) := by
    apply Subtype.ext
    exact finsetSubtypeCastEquiv_val h.1 _
  have hright :
      finsetSubtypeCastEquiv h.2.1.symm x =
        (⟨x.val, by
          rw [h.2.1]
          exact x.property⟩ : {v : V // v ∈ r.source}) := by
    apply Subtype.ext
    exact finsetSubtypeCastEquiv_val h.2.1.symm _
  change (q.bijection
      (finsetSubtypeCastEquiv h.1 (p.bijection x))).val =
    (finsetSubtypeCastEquiv h.2.2.1
      (r.bijection (finsetSubtypeCastEquiv h.2.1.symm x))).val
  rw [finsetSubtypeCastEquiv_val, hleft, hright]
  exact (isComposition_bijection_apply p q r h x).symm

end EPPAReducts.TwoGraphs
