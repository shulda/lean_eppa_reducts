import EPPAReducts.TwoGraphs.NormalizedPermutationComposition
import EPPAReducts.TwoGraphs.InducedSubsetGroupSections

/-!
# Equality casts for simultaneous subgroup sections

The coherentisation argument applies subgroup sections to normalized
automorphisms of canonical representative sub-two-graphs.  For
isomorphic source and target substructures, their representative
finite subsets are literally equal, but Lean retains their dependent
subtype carriers until an explicit cast is supplied.

This file proves that conjugating a permutation by such a cast
preserves induced two-graph automorphisms, and that the already chosen
subgroup section does not depend on whether the same finite subset
is presented as the source or target of an equality.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- An automorphism of an induced subset transported along equality
of the underlying finite subsets is still an automorphism. -/
theorem preservesInducedSubset_cast
    {V : Type} (A : TwoGraph V) {s t : Finset V}
    (h : s = t) (p : Equiv.Perm {v : V // v ∈ t})
    (hp : PreservesInducedSubset A t p) :
    PreservesInducedSubset A s
      (((finsetSubtypeCastEquiv h).trans p).trans
        (finsetSubtypeCastEquiv h).symm) := by
  cases h
  intro x y z
  simpa [finsetSubtypeCastEquiv] using hp x y z

/-- The fixed subgroup section for an induced finite subset is
invariant under equality-cast conjugation of a permutation of the
same subset.  This uses *one chosen section*, not two arbitrary
homomorphisms which could differ on the witness. -/
theorem chosenInducedSubsetGroupSection_cast
    {V X : Type} [Fintype V] [Fintype X]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (hdiv : ∀ s : Finset V, s.Nonempty →
      Fintype.card {v : V // v ∈ s} ∣ Fintype.card X)
    {s t : Finset V} (h : s = t)
    (p : Equiv.Perm {v : V // v ∈ t})
    (hp : PreservesInducedSubset A t p) :
    (chosenInducedSubsetGroupSection A ι χ hind hdiv s).lift
      (((finsetSubtypeCastEquiv h).trans p).trans
        (finsetSubtypeCastEquiv h).symm)
      (preservesInducedSubset_cast A h p hp) =
    (chosenInducedSubsetGroupSection A ι χ hind hdiv t).lift
      p hp := by
  cases h
  have hperm :
      (((finsetSubtypeCastEquiv (rfl : s = s)).trans p).trans
        (finsetSubtypeCastEquiv (rfl : s = s)).symm) = p := by
    apply Equiv.ext
    intro x
    rfl
  let g₁ : {g : Equiv.Perm {v : V // v ∈ s} //
      PreservesInducedSubset A s g} :=
    ⟨(((finsetSubtypeCastEquiv (rfl : s = s)).trans p).trans
      (finsetSubtypeCastEquiv (rfl : s = s)).symm),
      preservesInducedSubset_cast A (rfl : s = s) p hp⟩
  let g₂ : {g : Equiv.Perm {v : V // v ∈ s} //
      PreservesInducedSubset A s g} := ⟨p, hp⟩
  have heq : g₁ = g₂ := Subtype.ext hperm
  exact congrArg
    (fun g : {g : Equiv.Perm {v : V // v ∈ s} //
        PreservesInducedSubset A s g} =>
      (chosenInducedSubsetGroupSection A ι χ hind hdiv s).lift
        g.val g.property) heq

end EPPAReducts.TwoGraphs
