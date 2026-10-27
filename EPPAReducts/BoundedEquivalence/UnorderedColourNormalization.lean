import EPPAReducts.BoundedEquivalence.UnorderedWitnessAPI
import EPPAReducts.BoundedEquivalence.FiniteCoreLabels
import EPPAReducts.BoundedEquivalence.UnlabelledZModPresentation

/-!
# Normalizing the auxiliary class labels in an unordered induced extension

A core which already realizes all m unnamed equivalence classes
forces every at-most-m-class induced extension to have exactly the
same classes. Hence the auxiliary labels can be uniquely extended
from the old structure to the new one without naming colours in
the relational language.
-/

namespace EPPAReducts.BoundedEquivalence

/-- A fully realized colouring of an old unordered structure
determines the UNIQUE normalized ZMod m colouring on any
induced at-most-m-class extension. -/
theorem exists_unique_unordered_extension_colours
    {V W : Type} {r m : ℕ} (hm : 0 < m)
    (A : UnorderedBoundedEquivalence V r m)
    (B : UnorderedBoundedEquivalence W r m)
    (ι : V ↪ W)
    (fA : RSubsets V r → ZMod m)
    (hA : ∀ e f : RSubsets V r,
      A.sameClass.r e f ↔ fA e = fA f)
    (hSurj : Function.Surjective fA)
    (hind : IsInducedUnorderedBoundedEmbedding A B ι) :
    ∃! fB : RSubsets W r → ZMod m,
      (∀ e : RSubsets V r, fB (mapRSubset ι e) = fA e) ∧
      (∀ e f : RSubsets W r,
        B.sameClass.r e f ↔ fB e = fB f) := by
  classical
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  obtain ⟨f₀, hf₀⟩ :=
    (hasAtMostClasses_iff_zmod_presentation m hm B.sameClass).mp
      B.atMostClasses
  have hk : ∀ e f : RSubsets V r,
      fA e = fA f ↔
        f₀ (mapRSubset ι e) = f₀ (mapRSubset ι f) := by
    intro e f
    exact (hA e f).symm.trans ((hind e f).trans (hf₀ _ _))
  obtain ⟨fB, hfb, huniq⟩ :=
    unique_extension_colours_of_finite_realized_core
      (mapRSubset ι) fA f₀ hSurj hk
  refine ⟨fB, ⟨hfb.1, ?_⟩, ?_⟩
  · intro e f
    exact (hf₀ e f).trans (hfb.2 e f).symm
  · intro fB' h'
    apply huniq
    refine ⟨h'.1, ?_⟩
    intro e f
    exact (h'.2 e f).symm.trans (hf₀ e f)

/-- Existential version convenient for a hypothetical unordered
ordinary EPPA witness. -/
theorem exists_unordered_extension_colours
    {V W : Type} {r m : ℕ} (hm : 0 < m)
    (A : UnorderedBoundedEquivalence V r m)
    (B : UnorderedBoundedEquivalence W r m)
    (ι : V ↪ W)
    (fA : RSubsets V r → ZMod m)
    (hA : ∀ e f : RSubsets V r,
      A.sameClass.r e f ↔ fA e = fA f)
    (hSurj : Function.Surjective fA)
    (hind : IsInducedUnorderedBoundedEmbedding A B ι) :
    ∃ fB : RSubsets W r → ZMod m,
      (∀ e : RSubsets V r, fB (mapRSubset ι e) = fA e) ∧
      (∀ e f : RSubsets W r,
        B.sameClass.r e f ↔ fB e = fB f) := by
  obtain ⟨fB, hfb, _⟩ :=
    exists_unique_unordered_extension_colours hm A B ι fA hA hSurj hind
  exact ⟨fB, hfb⟩

end EPPAReducts.BoundedEquivalence
