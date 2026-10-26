import EPPAReducts.BoundedEquivalence.UnlabelledZModPresentation
import EPPAReducts.HumanTargets

/-!
# Literal partial automorphisms of unlabelled ordered-tuple equivalences

A colouring on injective ordered r-tuples is only an *auxiliary*
presentation: equality of its values is the entire structure. This
file defines the source/target induced partial-map condition exactly
using the existing HumanTargets.PartialBijection representation.

A uniform change of auxiliary colours implies preservation of the
unlabelled equivalence, independently of whether individual numerical
colour labels are fixed.
-/

namespace EPPAReducts.BoundedEquivalence

open EPPAReducts.HumanTargets

/-- An embedding on vertices acts on injective ordered tuples by
applying the embedding coordinatewise. -/
def mapInjectiveTuple
    {V W : Type} {r : ℕ}
    (ι : V ↪ W) (t : InjectiveTuples V r) :
    InjectiveTuples W r := by
  refine ⟨fun j => ι (t.val j), ?_⟩
  intro i j hij
  exact t.property (ι.injective hij)

/-- An auxiliary colouring of injective ordered tuples, interpreted
as the *unlabelled* equality-of-colours setoid. -/
def orderedTupleKernelSetoid
    {V κ : Type} {r : ℕ}
    (f : InjectiveTuples V r → κ) :
    Setoid (InjectiveTuples V r) :=
  colourKernelSetoid f

/-- The literal partial isomorphism condition on the equivalence
relation of ordered injective tuples. The colour values themselves
are not relation symbols and need not be preserved. -/
def IsOrderedTupleKernelPartialAutomorphism
    {V κ : Type} {r : ℕ}
    (f : InjectiveTuples V r → κ)
    (p : PartialBijection V) : Prop :=
  ∀ t u : InjectiveTuples {v : V // v ∈ p.source} r,
    f (mapInjectiveTuple (subtypeEmbedding p.source) t) =
      f (mapInjectiveTuple (subtypeEmbedding p.source) u) ↔
    f (mapInjectiveTuple
        (equivThenEmbedding p.bijection (subtypeEmbedding p.target)) t) =
      f (mapInjectiveTuple
        (equivThenEmbedding p.bijection (subtypeEmbedding p.target)) u)

/-- A common *uniform shift* of every auxiliary colour under a
partial vertex bijection guarantees an actual partial automorphism
of the unlabelled tuple equivalence. The theorem applies to every
finite source and target, including domains with no r-tuple. -/
theorem isOrderedTupleKernelPartialAutomorphism_of_shift
    {V κ : Type} [AddGroup κ] {r : ℕ}
    (f : InjectiveTuples V r → κ)
    (p : PartialBijection V) (δ : κ)
    (hshift : ∀ t : InjectiveTuples {v : V // v ∈ p.source} r,
      f (mapInjectiveTuple
        (equivThenEmbedding p.bijection (subtypeEmbedding p.target)) t) =
      f (mapInjectiveTuple (subtypeEmbedding p.source) t) + δ) :
    IsOrderedTupleKernelPartialAutomorphism f p := by
  intro t u
  constructor
  · intro h
    rw [hshift t, hshift u, h]
  · intro h
    rw [hshift t, hshift u] at h
    exact add_right_cancel h

/-- More generally, any injective re-labelling of all auxiliary
colour values under the partial map preserves and reflects their
equality, again without naming classes in the structure. -/
theorem isOrderedTupleKernelPartialAutomorphism_of_colour_injection
    {V κ : Type} {r : ℕ}
    (f : InjectiveTuples V r → κ)
    (p : PartialBijection V)
    (σ : κ → κ) (hσ : Function.Injective σ)
    (hact : ∀ t : InjectiveTuples {v : V // v ∈ p.source} r,
      f (mapInjectiveTuple
        (equivThenEmbedding p.bijection (subtypeEmbedding p.target)) t) =
        σ (f (mapInjectiveTuple (subtypeEmbedding p.source) t))) :
    IsOrderedTupleKernelPartialAutomorphism f p := by
  intro t u
  constructor
  · intro h
    rw [hact t, hact u, h]
  · intro h
    rw [hact t, hact u] at h
    exact hσ h

end EPPAReducts.BoundedEquivalence
