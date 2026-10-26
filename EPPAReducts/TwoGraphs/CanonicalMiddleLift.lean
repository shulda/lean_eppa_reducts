import EPPAReducts.TwoGraphs.SubsetSectionCast

/-!
# Middle ambient action in the coherentisation construction

For each literal partial automorphism p:E→F of A, normalize it to
an automorphism of the chosen representative of E (which is equal
to the representative of F).  Apply the one fixed simultaneous
subgroup section for that representative.  This is the middle
factor of the final conjugation formula.

The resulting map is a genuine automorphism of the whole valuation
witness and its action on the embedded canonical representative is
exactly the normalized partial map. We verify its identity law here;
composition is kept as an independent groupoid-level obligation.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- The chosen ambient lift of the normalized middle automorphism. -/
noncomputable def canonicalMiddleLift
    {V X : Type} [Fintype V] [Fintype X]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (hdiv : ∀ s : Finset V, s.Nonempty →
      Fintype.card {v : V // v ∈ s} ∣ Fintype.card X)
    (p : PartialBijection V)
    (hp : IsTwoGraphPartialAutomorphism A p) :
    Equiv.Perm (ValuationVertex X) :=
  (chosenInducedSubsetGroupSection A ι χ hind hdiv
    (canonicalInducedSubset A p.source)).lift
      (normalizedPartialAutomorphism A p hp)
      (normalizedPartialAutomorphism_preserves A p hp)

/-- Every normalized middle lift preserves the literal valuation
two-graph relation on the full witness, not just on old vertices. -/
theorem canonicalMiddleLift_isAutomorphism
    {V X : Type} [Fintype V] [Fintype X]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (hdiv : ∀ s : Finset V, s.Nonempty →
      Fintype.card {v : V // v ∈ s} ∣ Fintype.card X)
    (p : PartialBijection V)
    (hp : IsTwoGraphPartialAutomorphism A p) :
    IsTwoGraphAutomorphism (valuationTwoGraph X)
      (canonicalMiddleLift A ι χ hind hdiv p hp) := by
  exact (chosenInducedSubsetGroupSection A ι χ hind hdiv
    (canonicalInducedSubset A p.source)).isAutomorphism
      (normalizedPartialAutomorphism A p hp)
      (normalizedPartialAutomorphism_preserves A p hp)

/-- The middle lift acts as the normalized permutation on
all old vertices belonging to its chosen canonical representative. -/
theorem canonicalMiddleLift_on_representative
    {V X : Type} [Fintype V] [Fintype X]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (hdiv : ∀ s : Finset V, s.Nonempty →
      Fintype.card {v : V // v ∈ s} ∣ Fintype.card X)
    (p : PartialBijection V)
    (hp : IsTwoGraphPartialAutomorphism A p)
    (x : {v : V // v ∈ canonicalInducedSubset A p.source}) :
    canonicalMiddleLift A ι χ hind hdiv p hp
      (indexedTransversalEmbedding ι χ x.val) =
    indexedTransversalEmbedding ι χ
      ((normalizedPartialAutomorphism A p hp) x).val := by
  exact (chosenInducedSubsetGroupSection A ι χ hind hdiv
    (canonicalInducedSubset A p.source)).extendsOld
      (normalizedPartialAutomorphism A p hp)
      (normalizedPartialAutomorphism_preserves A p hp) x

/-- The normalized middle lift of the identity partial map on any
induced subset is the identity automorphism of the whole witness. -/
theorem canonicalMiddleLift_identity
    {V X : Type} [Fintype V] [Fintype X]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (hdiv : ∀ s : Finset V, s.Nonempty →
      Fintype.card {v : V // v ∈ s} ∣ Fintype.card X)
    (s : Finset V) :
    canonicalMiddleLift A ι χ hind hdiv
      (identityPartialBijection s)
      (identityPartialBijection_isTwoGraphPartialAutomorphism A s) =
    Equiv.refl (ValuationVertex X) := by
  let S := chosenInducedSubsetGroupSection A ι χ hind hdiv
    (canonicalInducedSubset A s)
  let g₁ : {g : Equiv.Perm
      {v : V // v ∈ canonicalInducedSubset A s} //
      PreservesInducedSubset A (canonicalInducedSubset A s) g} :=
    ⟨normalizedPartialAutomorphism A (identityPartialBijection s)
        (identityPartialBijection_isTwoGraphPartialAutomorphism A s),
      normalizedPartialAutomorphism_preserves A (identityPartialBijection s)
        (identityPartialBijection_isTwoGraphPartialAutomorphism A s)⟩
  let g₂ : {g : Equiv.Perm
      {v : V // v ∈ canonicalInducedSubset A s} //
      PreservesInducedSubset A (canonicalInducedSubset A s) g} :=
    ⟨Equiv.refl _,
      preservesInducedSubset_refl A (canonicalInducedSubset A s)⟩
  have heq : g₁ = g₂ :=
    Subtype.ext (normalizedPartialAutomorphism_identity A s)
  calc
    canonicalMiddleLift A ι χ hind hdiv (identityPartialBijection s)
        (identityPartialBijection_isTwoGraphPartialAutomorphism A s) =
      S.lift g₁.val g₁.property := rfl
    _ = S.lift g₂.val g₂.property :=
      congrArg (fun g : {g : Equiv.Perm
        {v : V // v ∈ canonicalInducedSubset A s} //
        PreservesInducedSubset A (canonicalInducedSubset A s) g} =>
        S.lift g.val g.property) heq
    _ = Equiv.refl (ValuationVertex X) := S.lift_refl

end EPPAReducts.TwoGraphs
