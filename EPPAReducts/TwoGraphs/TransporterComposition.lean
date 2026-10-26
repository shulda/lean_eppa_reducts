import EPPAReducts.TwoGraphs.NormalizedTransportCompatibility

/-!
# Composition algebra for canonical transporters

The middle factors of coherentisation are conjugates by a fixed
representative-to-object equivalence. When the intermediate object
agrees, the adjacent transports cancel and normalization respects
composition.

We also prove that equality-based subtype casts are compatible with
composition and with chosen induced-substructure transports.  These
lemmas isolate dependent subtype equalities from the final coherence
theorem, without making any assumptions about the two-graph beyond
the already certified chosen transports.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- Abstract conjugation by chosen equivalences cancels the middle
transporter when two arrows are composed. This is the algebraic
content of the normalized-composition calculation. -/
theorem equiv_normalize_trans
    {R E F G : Type}
    (uE : R ≃ E) (uF : R ≃ F) (uG : R ≃ G)
    (p : E ≃ F) (q : F ≃ G) :
    (((uE.trans p).trans uF.symm).trans
      ((uF.trans q).trans uG.symm)) =
    ((uE.trans (p.trans q)).trans uG.symm) := by
  apply Equiv.ext
  intro x
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]

/-- Changing a subtype by equality of its finite carrier sets is
compatible with successive changes of that same carrier. -/
theorem finsetSubtypeCastEquiv_trans
    {V : Type} {s t u : Finset V}
    (hst : s = t) (htu : t = u) :
    (finsetSubtypeCastEquiv hst).trans
      (finsetSubtypeCastEquiv htu) =
      finsetSubtypeCastEquiv (hst.trans htu) := by
  cases hst
  cases htu
  rfl

/-- Subtype casts do not change the chosen representative-to-subset
transport: equal subsets have exactly equal chosen transports. -/
theorem chosenInducedTransport_cast_val
    {V : Type} (A : TwoGraph V) {s t : Finset V}
    (hst : s = t)
    (x : {v : V // v ∈ canonicalInducedSubset A s}) :
    ((chosenInducedTransport A t)
      (finsetSubtypeCastEquiv
        (congrArg (canonicalInducedSubset A) hst) x)).val =
      ((chosenInducedTransport A s) x).val := by
  cases hst
  rfl

/-- The same compatibility for inverse chosen transports. -/
theorem chosenInducedTransport_symm_cast_val
    {V : Type} (A : TwoGraph V) {s t : Finset V}
    (hst : s = t) (x : {v : V // v ∈ s}) :
    ((chosenInducedTransport A t).symm
      (finsetSubtypeCastEquiv hst x)).val =
    (finsetSubtypeCastEquiv
      (congrArg (canonicalInducedSubset A) hst)
      ((chosenInducedTransport A s).symm x)).val := by
  cases hst
  rfl

end EPPAReducts.TwoGraphs
