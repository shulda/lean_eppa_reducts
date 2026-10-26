import EPPAReducts.TwoGraphs.CanonicalMiddleLift

/-!
# Composition of middle ambient lifts

The normalized permutations of p, q and their composite r are first
viewed on one canonical representative (the source representative
of p). The previously certified cast-conjugation lemmas identify
the *same chosen* subgroup section on all three presentations.

The actual witness automorphisms consequently satisfy the exact
composition law: the chosen middle lift of r is the composition of
the middle lifts of p and q.  This is the homomorphic core of the
final coherentisation argument; outer ambient transporters remain.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- The fixed middle ambient lifts compose in exactly the manner
required by the author's literal partial-map composition predicate.
No representative-dependent section is selected anew during
composition. -/
theorem canonicalMiddleLift_composition
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
    (canonicalMiddleLift A ι χ hind hdiv p hp).trans
      (canonicalMiddleLift A ι χ hind hdiv q hq) =
    canonicalMiddleLift A ι χ hind hdiv r hr := by
  let s := canonicalInducedSubset A p.source
  have hmid : s = canonicalInducedSubset A q.source :=
    (canonicalInducedSubset_eq_of_partial A p hp).trans
      (congrArg (canonicalInducedSubset A) h.1)
  have hsrc : s = canonicalInducedSubset A r.source :=
    congrArg (canonicalInducedSubset A) h.2.1.symm
  let S := chosenInducedSubsetGroupSection A ι χ hind hdiv s
  let σp : Equiv.Perm {v : V // v ∈ s} :=
    normalizedPartialAutomorphism A p hp
  let σq : Equiv.Perm {v : V // v ∈ s} :=
    ((finsetSubtypeCastEquiv hmid).trans
      (normalizedPartialAutomorphism A q hq)).trans
        (finsetSubtypeCastEquiv hmid).symm
  let σr : Equiv.Perm {v : V // v ∈ s} :=
    ((finsetSubtypeCastEquiv hsrc).trans
      (normalizedPartialAutomorphism A r hr)).trans
        (finsetSubtypeCastEquiv hsrc).symm
  have hσp : PreservesInducedSubset A s σp :=
    normalizedPartialAutomorphism_preserves A p hp
  have hσq : PreservesInducedSubset A s σq :=
    preservesInducedSubset_cast A hmid
      (normalizedPartialAutomorphism A q hq)
      (normalizedPartialAutomorphism_preserves A q hq)
  have hσr : PreservesInducedSubset A s σr :=
    preservesInducedSubset_cast A hsrc
      (normalizedPartialAutomorphism A r hr)
      (normalizedPartialAutomorphism_preserves A r hr)
  have hpLift :
      S.lift σp hσp = canonicalMiddleLift A ι χ hind hdiv p hp := rfl
  have hqLift :
      S.lift σq hσq = canonicalMiddleLift A ι χ hind hdiv q hq :=
    chosenInducedSubsetGroupSection_cast A ι χ hind hdiv hmid
      (normalizedPartialAutomorphism A q hq)
      (normalizedPartialAutomorphism_preserves A q hq)
  have hrLift :
      S.lift σr hσr = canonicalMiddleLift A ι χ hind hdiv r hr :=
    chosenInducedSubsetGroupSection_cast A ι χ hind hdiv hsrc
      (normalizedPartialAutomorphism A r hr)
      (normalizedPartialAutomorphism_preserves A r hr)
  have hσ : σp.trans σq = σr :=
    normalizedPartialAutomorphism_composition_cast A p q r
      hp hq hr h hmid hsrc
  let gp : {g : Equiv.Perm {v : V // v ∈ s} //
      PreservesInducedSubset A s g} :=
    ⟨σp.trans σq, preservesInducedSubset_trans A s σp σq hσp hσq⟩
  let gr : {g : Equiv.Perm {v : V // v ∈ s} //
      PreservesInducedSubset A s g} := ⟨σr, hσr⟩
  have hgr : gp = gr := Subtype.ext hσ
  have hgroup :
      S.lift (σp.trans σq)
        (preservesInducedSubset_trans A s σp σq hσp hσq) =
      S.lift σr hσr :=
    congrArg
      (fun g : {g : Equiv.Perm {v : V // v ∈ s} //
          PreservesInducedSubset A s g} =>
        S.lift g.val g.property) hgr
  calc
    (canonicalMiddleLift A ι χ hind hdiv p hp).trans
        (canonicalMiddleLift A ι χ hind hdiv q hq) =
      (S.lift σp hσp).trans (S.lift σq hσq) := by
        rw [hpLift, hqLift]
    _ = S.lift (σp.trans σq)
        (preservesInducedSubset_trans A s σp σq hσp hσq) :=
          S.lift_trans σp σq hσp hσq
    _ = S.lift σr hσr := hgroup
    _ = canonicalMiddleLift A ι χ hind hdiv r hr := hrLift

end EPPAReducts.TwoGraphs
