import EPPAReducts.BoundedEquivalence.OrderedInducedColours
import EPPAReducts.BoundedEquivalence.OrderedKernelAutGroup

/-!
# Exact ordinary EPPA witness interface for ordered bounded equivalences

The language is the unlabelled equivalence relation on injective
ordered r-tuples. An induced embedding preserves and reflects
equality of equivalence classes; neither an automorphism nor a
partial automorphism is required to fix numerical class labels.

These are precise specifications, not a claim that a witness exists
or that ordinary EPPA fails.
-/

namespace EPPAReducts.BoundedEquivalence

open EPPAReducts.HumanTargets

/-- An automorphism of the whole unlabelled equivalence structure. -/
def IsOrderedBoundedAutomorphism
    {W : Type} {r m : ℕ}
    (B : OrderedBoundedEquivalence W r m)
    (g : Equiv.Perm W) : Prop :=
  ∀ t u : InjectiveTuples W r,
    B.sameClass.r t u ↔
      B.sameClass.r (permuteOrderedTuple g t)
        (permuteOrderedTuple g u)

/-- A finite ordinary EPPA witness: one induced embedding into a
single extension whose automorphisms extend *every* literal partial
automorphism of the original structure. -/
def IsOrderedBoundedEPPAWitness
    {V W : Type} {r m : ℕ}
    (A : OrderedBoundedEquivalence V r m)
    (B : OrderedBoundedEquivalence W r m)
    (ι : V ↪ W) : Prop :=
  IsInducedOrderedBoundedEmbedding A B ι ∧
    ∀ (p : PartialBijection V),
      IsOrderedBoundedPartialAutomorphism A p →
      ∃ g : Equiv.Perm W,
        IsOrderedBoundedAutomorphism B g ∧ Extends ι p g

/-- The automorphism predicate is equivalent to membership in the
actual automorphism subgroup of any auxiliary presentation fB. -/
theorem orderedBoundedAutomorphism_iff_kernelAut
    {W κ : Type} {r m : ℕ}
    (B : OrderedBoundedEquivalence W r m)
    (fB : InjectiveTuples W r → κ)
    (hB : ∀ t u : InjectiveTuples W r,
      B.sameClass.r t u ↔ fB t = fB u)
    (g : Equiv.Perm W) :
    IsOrderedBoundedAutomorphism B g ↔
      g ∈ orderedTupleKernelAutSubgroup fB := by
  constructor
  · intro hg t u
    exact (hB t u).symm.trans
      ((hg t u).trans
        (hB (permuteOrderedTuple g t)
          (permuteOrderedTuple g u)))
  · intro hg t u
    exact (hB t u).trans
      ((hg t u).trans
        (hB (permuteOrderedTuple g t)
          (permuteOrderedTuple g u)).symm)

end EPPAReducts.BoundedEquivalence
