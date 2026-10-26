import EPPAReducts.BoundedEquivalence.OrderedTupleKernelPartial
import Mathlib.GroupTheory.Perm.Basic

/-!
# The genuine vertex-automorphism subgroup of an ordered tuple kernel

For any auxiliary colouring of injective ordered r-tuples, the
permutations preserving *equality of colours* (not colour names)
form a subgroup of the full vertex permutation group.

This subgroup is the automorphism group of the unlabelled relational
structure, and is the ambient group needed to form the pointwise
core stabilizer in the negative EPPA obstruction.
-/

namespace EPPAReducts.BoundedEquivalence

/-- The induced action of a vertex permutation on injective ordered
r-tuples. -/
def permuteOrderedTuple
    {V : Type} {r : ℕ}
    (g : Equiv.Perm V) (t : InjectiveTuples V r) :
    InjectiveTuples V r :=
  mapInjectiveTuple ⟨g, g.injective⟩ t

@[simp] theorem permuteOrderedTuple_one
    {V : Type} {r : ℕ} (t : InjectiveTuples V r) :
    permuteOrderedTuple (1 : Equiv.Perm V) t = t := by
  apply Subtype.ext
  funext j
  simp [permuteOrderedTuple, mapInjectiveTuple]

@[simp] theorem permuteOrderedTuple_mul
    {V : Type} {r : ℕ}
    (g h : Equiv.Perm V) (t : InjectiveTuples V r) :
    permuteOrderedTuple (g * h) t =
      permuteOrderedTuple g (permuteOrderedTuple h t) := by
  apply Subtype.ext
  funext j
  simp [permuteOrderedTuple, mapInjectiveTuple, Equiv.Perm.mul_apply]

@[simp] theorem permuteOrderedTuple_inv_left
    {V : Type} {r : ℕ}
    (g : Equiv.Perm V) (t : InjectiveTuples V r) :
    permuteOrderedTuple (g⁻¹) (permuteOrderedTuple g t) = t := by
  apply Subtype.ext
  funext j
  simp [permuteOrderedTuple, mapInjectiveTuple]

@[simp] theorem permuteOrderedTuple_inv_right
    {V : Type} {r : ℕ}
    (g : Equiv.Perm V) (t : InjectiveTuples V r) :
    permuteOrderedTuple g (permuteOrderedTuple (g⁻¹) t) = t := by
  apply Subtype.ext
  funext j
  simp [permuteOrderedTuple, mapInjectiveTuple]

/-- A vertex permutation is an automorphism of the actual unlabelled
tuple equivalence iff it preserves and reflects equality of
the auxiliary colours. -/
def PreservesOrderedTupleKernel
    {V κ : Type} {r : ℕ}
    (f : InjectiveTuples V r → κ) (g : Equiv.Perm V) : Prop :=
  ∀ t u : InjectiveTuples V r,
    f t = f u ↔
      f (permuteOrderedTuple g t) =
        f (permuteOrderedTuple g u)

/-- The automorphisms of the unlabelled tuple kernel form a subgroup,
without imposing any preservation of the auxiliary colour values. -/
def orderedTupleKernelAutSubgroup
    {V κ : Type} {r : ℕ}
    (f : InjectiveTuples V r → κ) :
    Subgroup (Equiv.Perm V) where
  carrier := {g | PreservesOrderedTupleKernel f g}
  one_mem' := by
    intro t u
    simp only [permuteOrderedTuple_one]
  mul_mem' := by
    intro g h hg hh t u
    simpa only [permuteOrderedTuple_mul] using
      (hh t u).trans
        (hg (permuteOrderedTuple h t)
          (permuteOrderedTuple h u))
  inv_mem' := by
    intro g hg t u
    have h := (hg
      (permuteOrderedTuple (g⁻¹) t)
      (permuteOrderedTuple (g⁻¹) u)).symm
    simpa only [permuteOrderedTuple_inv_right] using h

/-- Membership in the automorphism subgroup means exactly the
human-readable unlabelled kernel preservation predicate. -/
theorem mem_orderedTupleKernelAutSubgroup_iff
    {V κ : Type} {r : ℕ}
    (f : InjectiveTuples V r → κ) (g : Equiv.Perm V) :
    g ∈ orderedTupleKernelAutSubgroup f ↔
      PreservesOrderedTupleKernel f g := Iff.rfl

end EPPAReducts.BoundedEquivalence
