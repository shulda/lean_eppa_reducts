import EPPAReducts.TwoGraphs.CanonicalCoherentLift

/-!
# Composition of conjugated ambient extensions

The fixed ambient transporter assigned to the target subset of p
is the same transporter assigned to the source subset of q, whenever
their literal subsets agree. These adjacent factors cancel. The
remaining middle actions compose by the certified section law.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- Abstract cancellation of fixed outer transporters. The only
algebraic hypothesis beyond matching objects is composition of the
middle permutations. -/
theorem conjugatedPermutation_trans
    {W : Type}
    (source middle middle' target source' target' : Equiv.Perm W)
    (mp mq mr : Equiv.Perm W)
    (hmiddle : middle = middle')
    (hsource : source = source')
    (htarget : target = target')
    (hcomp : mp.trans mq = mr) :
    (((source.symm.trans mp).trans middle).trans
      ((middle'.symm.trans mq).trans target)) =
      ((source'.symm.trans mr).trans target') := by
  subst middle'
  subst source'
  subst target'
  subst mr
  apply Equiv.ext
  intro w
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]

/-- The same fixed conjugated ambient lifts respect the exact
author-approved partial-bijection composition relation. -/
theorem canonicalConjugatedLift_composition
    {V X : Type} [Fintype V] [Fintype X]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (hdiv : ∀ s : Finset V, s.Nonempty →
      Fintype.card {v : V // v ∈ s} ∣ Fintype.card X)
    (p q r : PartialBijection V)
    (hp : IsTwoGraphPartialAutomorphism A p)
    (hq : IsTwoGraphPartialAutomorphism A q)
    (hr : IsTwoGraphPartialAutomorphism A r)
    (h : IsComposition p q r) :
    (canonicalConjugatedLift A ι χ hind hdiv p hp).trans
      (canonicalConjugatedLift A ι χ hind hdiv q hq) =
    canonicalConjugatedLift A ι χ hind hdiv r hr := by
  exact conjugatedPermutation_trans
    (canonicalSubsetAmbientTransport A ι χ hind p.source)
    (canonicalSubsetAmbientTransport A ι χ hind p.target)
    (canonicalSubsetAmbientTransport A ι χ hind q.source)
    (canonicalSubsetAmbientTransport A ι χ hind q.target)
    (canonicalSubsetAmbientTransport A ι χ hind r.source)
    (canonicalSubsetAmbientTransport A ι χ hind r.target)
    (canonicalMiddleLift A ι χ hind hdiv p hp)
    (canonicalMiddleLift A ι χ hind hdiv q hq)
    (canonicalMiddleLift A ι χ hind hdiv r hr)
    (congrArg (canonicalSubsetAmbientTransport A ι χ hind) h.1)
    (congrArg (canonicalSubsetAmbientTransport A ι χ hind) h.2.1.symm)
    (congrArg (canonicalSubsetAmbientTransport A ι χ hind) h.2.2.1.symm)
    (canonicalMiddleLift_composition A ι χ hind hdiv p q r hp hq hr h)

/-- The identity partial map of any induced subset, including the
empty set, is sent to the identity ambient automorphism. -/
theorem canonicalConjugatedLift_identity
    {V X : Type} [Fintype V] [Fintype X]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (hdiv : ∀ s : Finset V, s.Nonempty →
      Fintype.card {v : V // v ∈ s} ∣ Fintype.card X)
    (s : Finset V) :
    canonicalConjugatedLift A ι χ hind hdiv
      (identityPartialBijection s)
      (identityPartialBijection_isTwoGraphPartialAutomorphism A s) =
    Equiv.refl (ValuationVertex X) := by
  apply Equiv.ext
  intro w
  simp only [canonicalConjugatedLift, Equiv.trans_apply,
    canonicalMiddleLift_identity, Equiv.refl_apply,
    Equiv.apply_symm_apply]

end EPPAReducts.TwoGraphs
