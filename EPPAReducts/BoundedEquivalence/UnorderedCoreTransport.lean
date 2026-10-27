import EPPAReducts.BoundedEquivalence.UnorderedCorePointwiseNormalizer

/-!
# Extensions of the same core permutation lie in one normalizing coset

Suppose the unlabelled tuple-kernel automorphisms g and h agree on
the embedded old cyclic core, where they induce a common core
permutation p. The inverse actions also preserve the core, so both
normalize its pointwise fixer L, and h*g⁻¹ belongs to L. In
particular, h is of the form l*g for some l in L.

The statement does not assume that the auxiliary colours are
named or fixed by any automorphism.
-/

namespace EPPAReducts.BoundedEquivalence

/-- An ambient permutation extending p on the embedded core also
extends p⁻¹ in the reverse direction. -/
theorem unorderedCoreExtension_inverse
    {V S : Type} (ι : S ↪ V)
    (p : Equiv.Perm S) (g : Equiv.Perm V)
    (hcore : ∀ s : S, g (ι s) = ι (p s))
    (s : S) :
    g⁻¹ (ι s) = ι (p⁻¹ s) := by
  calc
    g⁻¹ (ι s) = g⁻¹ (g (ι (p⁻¹ s))) := by
      rw [hcore (p⁻¹ s)]
      simp
    _ = ι (p⁻¹ s) := by simp

/-- An ambient automorphism extending a permutation of the
embedded old core normalizes its pointwise-fixer subgroup. -/
theorem unorderedCoreExtension_normalizes
    {V S κ : Type} {r : ℕ}
    (f : RSubsets V r → κ) (ι : S ↪ V)
    (p : Equiv.Perm S) (g : Equiv.Perm V)
    (hg : g ∈ unorderedSubsetKernelAutSubgroup f)
    (hcore : ∀ s : S, g (ι s) = ι (p s)) :
    g ∈ Subgroup.normalizer (unorderedKernelCorePointwiseFixer f ι) := by
  apply unorderedKernelCorePointwiseFixer_normalizer f ι g hg
  · intro s
    exact ⟨p s, hcore s⟩
  · intro s
    exact ⟨p⁻¹ s, unorderedCoreExtension_inverse ι p g hcore s⟩

/-- If two full unlabelled kernel automorphisms extend the SAME
permutation p of the old core, their quotient fixes the old core
pointwise and preserves the full equivalence. -/
theorem unorderedCoreExtensions_difference_mem
    {V S κ : Type} {r : ℕ}
    (f : RSubsets V r → κ) (ι : S ↪ V)
    (p : Equiv.Perm S)
    (g h : Equiv.Perm V)
    (hg : g ∈ unorderedSubsetKernelAutSubgroup f)
    (hh : h ∈ unorderedSubsetKernelAutSubgroup f)
    (hgcore : ∀ s : S, g (ι s) = ι (p s))
    (hhcore : ∀ s : S, h (ι s) = ι (p s)) :
    h * g⁻¹ ∈ unorderedKernelCorePointwiseFixer f ι := by
  constructor
  · exact (unorderedSubsetKernelAutSubgroup f).mul_mem hh
      ((unorderedSubsetKernelAutSubgroup f).inv_mem hg)
  · intro s
    calc
      (h * g⁻¹) (ι s) = h (g⁻¹ (ι s)) := rfl
      _ = h (ι (p⁻¹ s)) := by
        rw [unorderedCoreExtension_inverse ι p g hgcore s]
      _ = ι (p (p⁻¹ s)) := hhcore (p⁻¹ s)
      _ = ι s := by simp

/-- Two full automorphisms extending the same old-core permutation
are in the same left coset of the old-core pointwise stabilizer:
h = l*g for some l in L. -/
theorem unorderedCoreExtensions_same_coset
    {V S κ : Type} {r : ℕ}
    (f : RSubsets V r → κ) (ι : S ↪ V)
    (p : Equiv.Perm S)
    (g h : Equiv.Perm V)
    (hg : g ∈ unorderedSubsetKernelAutSubgroup f)
    (hh : h ∈ unorderedSubsetKernelAutSubgroup f)
    (hgcore : ∀ s : S, g (ι s) = ι (p s))
    (hhcore : ∀ s : S, h (ι s) = ι (p s)) :
    ∃ l : unorderedKernelCorePointwiseFixer f ι,
      l.val * g = h := by
  refine ⟨⟨h * g⁻¹,
    unorderedCoreExtensions_difference_mem f ι p g h
      hg hh hgcore hhcore⟩, ?_⟩
  change (h * g⁻¹) * g = h
  simp [mul_assoc]

end EPPAReducts.BoundedEquivalence
