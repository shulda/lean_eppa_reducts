import EPPAReducts.BoundedEquivalence.FiniteCoreLabels
import EPPAReducts.BoundedEquivalence.OrderedFiniteObstruction
import EPPAReducts.BoundedEquivalence.UnlabelledZModPresentation

/-!
# Recover the auxiliary colours of an arbitrary induced extension

An old ordered bounded-equivalence structure admits an auxiliary
colouring fA using all m possible values. Any induced extension B
has at most m (unlabelled) classes. Consequently B has exactly those
old classes and there is a unique auxiliary ZMod m colouring fB
presenting B which agrees with fA along the given vertex embedding.

The exact unlabelled class language is preserved; fB is chosen for
the proof and is not a distinguished structural relation.
-/

namespace EPPAReducts.BoundedEquivalence

/-- A vertex injection of two ordered bounded-equivalence structures
is induced precisely when it preserves and reflects equality of
classes of pairs of injective r-tuples. -/
def IsInducedOrderedBoundedEmbedding
    {V W : Type} {r m : ℕ}
    (A : OrderedBoundedEquivalence V r m)
    (B : OrderedBoundedEquivalence W r m)
    (ι : V ↪ W) : Prop :=
  ∀ t u : InjectiveTuples V r,
    A.sameClass.r t u ↔
      B.sameClass.r (mapInjectiveTuple ι t)
        (mapInjectiveTuple ι u)

/-- Once all m old colours are realized, every induced extension
with at most m unnamed classes admits a uniquely normalized
auxiliary ZMod m presentation extending the old labels. -/
theorem exists_unique_ordered_extension_colours
    {V W : Type} {r m : ℕ} (hm : 0 < m)
    (A : OrderedBoundedEquivalence V r m)
    (B : OrderedBoundedEquivalence W r m)
    (ι : V ↪ W)
    (fA : InjectiveTuples V r → ZMod m)
    (hA : ∀ t u : InjectiveTuples V r,
      A.sameClass.r t u ↔ fA t = fA u)
    (hSurj : Function.Surjective fA)
    (hind : IsInducedOrderedBoundedEmbedding A B ι) :
    ∃! fB : InjectiveTuples W r → ZMod m,
      (∀ t : InjectiveTuples V r,
        fB (mapInjectiveTuple ι t) = fA t) ∧
      (∀ t u : InjectiveTuples W r,
        B.sameClass.r t u ↔ fB t = fB u) := by
  classical
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  obtain ⟨f₀, hf₀⟩ :=
    (hasAtMostClasses_iff_zmod_presentation m hm B.sameClass).mp
      B.atMostClasses
  have hk : ∀ t u : InjectiveTuples V r,
      fA t = fA u ↔
        f₀ (mapInjectiveTuple ι t) =
          f₀ (mapInjectiveTuple ι u) := by
    intro t u
    exact (hA t u).symm.trans
      ((hind t u).trans (hf₀ _ _))
  obtain ⟨fB, hfb, huniq⟩ :=
    unique_extension_colours_of_finite_realized_core
      (mapInjectiveTuple ι) fA f₀ hSurj hk
  refine ⟨fB, ⟨hfb.1, ?_⟩, ?_⟩
  · intro t u
    exact (hf₀ t u).trans (hfb.2 t u).symm
  · intro fB' h'
    apply huniq
    refine ⟨h'.1, ?_⟩
    intro t u
    exact (h'.2 t u).symm.trans (hf₀ t u)

/-- Existential form, convenient when choosing a normalized
presentation of a hypothetical finite EPPA witness. -/
theorem exists_ordered_extension_colours
    {V W : Type} {r m : ℕ} (hm : 0 < m)
    (A : OrderedBoundedEquivalence V r m)
    (B : OrderedBoundedEquivalence W r m)
    (ι : V ↪ W)
    (fA : InjectiveTuples V r → ZMod m)
    (hA : ∀ t u : InjectiveTuples V r,
      A.sameClass.r t u ↔ fA t = fA u)
    (hSurj : Function.Surjective fA)
    (hind : IsInducedOrderedBoundedEmbedding A B ι) :
    ∃ fB : InjectiveTuples W r → ZMod m,
      (∀ t : InjectiveTuples V r,
        fB (mapInjectiveTuple ι t) = fA t) ∧
      (∀ t u : InjectiveTuples W r,
        B.sameClass.r t u ↔ fB t = fB u) := by
  obtain ⟨fB, hfb, _⟩ :=
    exists_unique_ordered_extension_colours hm A B ι fA hA hSurj hind
  exact ⟨fB, hfb⟩

end EPPAReducts.BoundedEquivalence
