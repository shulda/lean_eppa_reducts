import EPPAReducts.BoundedEquivalence.UnorderedWitnessAPI
import Mathlib.GroupTheory.Perm.Basic

/-!
# The automorphism subgroup of an unlabelled unordered-subset kernel

An auxiliary colouring of r-subsets is just a presentation of the
equivalence classes. The full automorphism subgroup preserves and
reflects equality of colour values, not their numerical labels.
-/

namespace EPPAReducts.BoundedEquivalence

/-- The permutation action on unordered subsets sends identity to
identity. It is the existing action from ClassShiftFixed. -/
@[simp] theorem permuteRSubset_one
    {V : Type} {r : ℕ} (s : RSubsets V r) :
    permuteRSubset (1 : Equiv.Perm V) s = s := by
  apply Subtype.ext
  ext x
  simp [permuteRSubset]

/-- The action on r-subsets respects the genuine multiplication
of vertex permutations. -/
@[simp] theorem permuteRSubset_mul
    {V : Type} {r : ℕ} (g h : Equiv.Perm V)
    (s : RSubsets V r) :
    permuteRSubset (g * h) s =
      permuteRSubset g (permuteRSubset h s) := by
  apply Subtype.ext
  ext x
  simp [permuteRSubset, Equiv.Perm.mul_apply]

@[simp] theorem permuteRSubset_inv_left
    {V : Type} {r : ℕ} (g : Equiv.Perm V)
    (s : RSubsets V r) :
    permuteRSubset g⁻¹ (permuteRSubset g s) = s := by
  calc
    permuteRSubset g⁻¹ (permuteRSubset g s) =
      permuteRSubset (g⁻¹ * g) s :=
        (permuteRSubset_mul g⁻¹ g s).symm
    _ = s := by simp

@[simp] theorem permuteRSubset_inv_right
    {V : Type} {r : ℕ} (g : Equiv.Perm V)
    (s : RSubsets V r) :
    permuteRSubset g (permuteRSubset g⁻¹ s) = s := by
  calc
    permuteRSubset g (permuteRSubset g⁻¹ s) =
      permuteRSubset (g * g⁻¹) s :=
        (permuteRSubset_mul g g⁻¹ s).symm
    _ = s := by simp

/-- The full vertex automorphism condition for the unlabelled
kernel of an auxiliary r-subset colouring. -/
def PreservesUnorderedSubsetKernel
    {V κ : Type} {r : ℕ}
    (f : RSubsets V r → κ) (g : Equiv.Perm V) : Prop :=
  ∀ s t : RSubsets V r,
    f s = f t ↔
      f (permuteRSubset g s) = f (permuteRSubset g t)

/-- Genuine automorphisms of an unlabelled r-subset equivalence
form a subgroup of the vertex permutation group. -/
def unorderedSubsetKernelAutSubgroup
    {V κ : Type} {r : ℕ}
    (f : RSubsets V r → κ) :
    Subgroup (Equiv.Perm V) where
  carrier := {g | PreservesUnorderedSubsetKernel f g}
  one_mem' := by
    intro s t
    simp only [permuteRSubset_one]
  mul_mem' := by
    intro g h hg hh s t
    simpa only [permuteRSubset_mul] using
      (hh s t).trans
        (hg (permuteRSubset h s) (permuteRSubset h t))
  inv_mem' := by
    intro g hg s t
    have h := (hg
      (permuteRSubset g⁻¹ s)
      (permuteRSubset g⁻¹ t)).symm
    simpa only [permuteRSubset_inv_right] using h

/-- Full unlabelled automorphisms agree with the subgroup membership
predicate for every auxiliary colouring of their actual setoid. -/
theorem unorderedBoundedAutomorphism_iff_kernelAut
    {V κ : Type} {r m : ℕ}
    (B : UnorderedBoundedEquivalence V r m)
    (f : RSubsets V r → κ)
    (hB : ∀ s t : RSubsets V r,
      B.sameClass.r s t ↔ f s = f t)
    (g : Equiv.Perm V) :
    IsUnorderedBoundedAutomorphism B g ↔
      g ∈ unorderedSubsetKernelAutSubgroup f := by
  constructor
  · intro hg s t
    exact (hB s t).symm.trans
      ((hg s t).trans
        (hB (permuteRSubset g s)
          (permuteRSubset g t)))
  · intro hg s t
    exact (hB s t).trans
      ((hg s t).trans
        (hB (permuteRSubset g s)
          (permuteRSubset g t)).symm)

end EPPAReducts.BoundedEquivalence
