import EPPAReducts.BoundedEquivalence.UnorderedWitnessAPI
import Mathlib.Data.Fintype.EquivFin

/-!
# Reverse conversion from unlabelled unordered pairs to graphs modulo complementation

The frozen human target regards a graph modulo global complementation
as an equivalence on unordered pairs with *at most two* unnamed
classes. Its automorphisms may exchange the two classes. This module
also records the exact conditional reduction from the yet-to-be-proved
general unordered failure-of-EPPA theorem to the frozen target.
-/

namespace EPPAReducts.BoundedEquivalence

open EPPAReducts.HumanTargets

/-- Convert an arbitrary unlabelled pair equivalence with at most
two classes into the author-approved graph-modulo-complementation
API. The Boolean labels are mere witnesses of a propositional
cardinality bound, not named edge colours. -/
noncomputable def unorderedToGraph {V : Type}
    (A : UnorderedBoundedEquivalence V 2 2) :
    GraphModuloComplementation V where
  sameClass := A.sameClass
  atMostTwoClasses := by
    classical
    obtain ⟨f, hf⟩ := A.atMostClasses
    let e : Fin 2 ≃ Bool :=
      Fintype.equivOfCardEq (by decide)
    refine ⟨fun x => e (f x), ?_⟩
    intro x y
    constructor
    · exact fun h => congrArg e ((hf x y).mp h)
    · exact fun h => (hf x y).mpr (e.injective h)

/-- The reverse conversion keeps exactly the original induced
embeddings, rather than merely a chosen representative graph. -/
theorem unorderedToGraph_induced_iff
    {V W : Type} (A : UnorderedBoundedEquivalence V 2 2)
    (B : UnorderedBoundedEquivalence W 2 2) (ι : V ↪ W) :
    IsInducedPairEmbedding (unorderedToGraph A) (unorderedToGraph B) ι ↔
      IsInducedUnorderedBoundedEmbedding A B ι := Iff.rfl

theorem unorderedToGraph_partial_iff
    {V : Type} (A : UnorderedBoundedEquivalence V 2 2)
    (p : PartialBijection V) :
    IsPairPartialAutomorphism (unorderedToGraph A) p ↔
      IsUnorderedBoundedPartialAutomorphism A p := Iff.rfl

theorem unorderedToGraph_automorphism_iff
    {V : Type} (A : UnorderedBoundedEquivalence V 2 2)
    (g : Equiv.Perm V) :
    IsPairAutomorphism (unorderedToGraph A) g ↔
      IsUnorderedBoundedAutomorphism A g := Iff.rfl

theorem unorderedToGraph_EPPAWitness_iff
    {V W : Type} (A : UnorderedBoundedEquivalence V 2 2)
    (B : UnorderedBoundedEquivalence W 2 2) (ι : V ↪ W) :
    IsPairEPPAWitness (unorderedToGraph A) (unorderedToGraph B) ι ↔
      IsUnorderedBoundedEPPAWitness A B ι := Iff.rfl

/-- The universal negative statement still awaiting proof for
all unordered r-subsets, with no dependence on chosen colour names. -/
def unorderedBoundedEquivalencesFailEPPA : Prop :=
  ∀ (r m : ℕ), 2 ≤ r → 2 ≤ m →
    ∃ (V : Type), Finite V ∧
      ∃ (A : UnorderedBoundedEquivalence V r m),
        ∀ (W : Type), Finite W →
          ∀ (B : UnorderedBoundedEquivalence W r m)
            (ι : V ↪ W),
              ¬ IsUnorderedBoundedEPPAWitness A B ι

/-- Certification target bridge: the general unordered theorem, once
proved, IMPLIES the author's frozen graph-modulo-complementation
target with precisely its original quantification over every finite
induced EPPA witness. This is conditional, not the target's proof. -/
theorem graphsModuloComplementationFailEPPA_of_unordered
    (h : unorderedBoundedEquivalencesFailEPPA) :
    HumanTargets.graphsModuloComplementationFailEPPA := by
  obtain ⟨V, hfinite, A, hno⟩ :=
    h 2 2 (by decide) (by decide)
  refine ⟨V, hfinite, unorderedToGraph A, ?_⟩
  intro W hW B ι hpair
  have hgeneric : IsUnorderedBoundedEPPAWitness
      A (graphToUnordered B) ι := by
    exact (graphToUnordered_EPPAWitness_iff
      (unorderedToGraph A) B ι).mpr hpair
  exact hno W hW (graphToUnordered B) ι hgeneric

end EPPAReducts.BoundedEquivalence
