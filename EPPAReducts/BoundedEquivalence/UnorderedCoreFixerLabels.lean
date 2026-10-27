import EPPAReducts.BoundedEquivalence.UnorderedCoreCosetCollision

/-!
# Core-pointwise automorphisms preserve every auxiliary class

An embedded core realizing all unlabelled equivalence classes
determines the global class action of an automorphism. A genuine
unlabelled automorphism fixing that core pointwise must therefore
fix all auxiliary classes, although no labels occur in the language.
-/

namespace EPPAReducts.BoundedEquivalence

theorem unorderedCoreFixer_preserves_all_colours
    {S W κ : Type} {r : ℕ}
    (fB : RSubsets W r → κ) (ι : S ↪ W)
    (hsurj : Function.Surjective
      (fun s : RSubsets S r => fB (mapRSubset ι s)))
    (l : unorderedKernelCorePointwiseFixer fB ι) :
    ∀ s : RSubsets W r,
      fB (permuteRSubset l.val s) = fB s := by
  apply core_pointwise_fixed_preserves_labels
    (mapRSubset ι) fB hsurj (permuteRSubset l.val)
  · intro s t h
    exact (l.property.1 s t).mp h
  · intro s
    have hh := permuteRSubset_map_core ι 1 l.val
      (by intro x; exact l.property.2 x) s
    simpa only [permuteRSubset_one] using hh

end EPPAReducts.BoundedEquivalence
