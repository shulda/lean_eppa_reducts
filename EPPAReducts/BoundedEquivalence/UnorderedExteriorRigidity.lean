import EPPAReducts.BoundedEquivalence.UnorderedExteriorInsertion
import EPPAReducts.BoundedEquivalence.UnorderedCoreFixerLabels

/-!
# Exterior types cannot merge under the core pointwise stabilizer

If every auxiliary equivalence class is realized already on an old
embedded core, a genuine automorphism fixing that core pointwise
preserves all class labels. The literal induced subset with one
exterior vertex then recovers that vertex's entire exterior type.
Thus injectively different exterior types lie in distinct orbits of
the pointwise core fixer in every induced extension.
-/

namespace EPPAReducts.BoundedEquivalence

/-- Embed the old cyclic core of a disjoint-union carrier into any
further extension, without choosing a complement or named colours. -/
def unorderedEmbeddedCore {S E W : Type}
    (ι : Sum S E ↪ W) : S ↪ W where
  toFun := fun s => ι (Sum.inl s)
  inj' := by
    intro s t h
    exact Sum.inl_injective (ι.injective h)

/-- In any ambient unlabelled equivalence structure, a fully
class-realizing embedded core separates every pair of exterior
vertices whose prescribed exterior colour functions differ. -/
theorem unorderedExterior_not_coreFixer_related
    {S E W κ : Type} {t : ℕ}
    (ι : Sum S E ↪ W)
    (fB : RSubsets W (t + 1) → κ)
    (hsurj : Function.Surjective
      (fun q : RSubsets S (t + 1) =>
        fB (mapRSubset (unorderedEmbeddedCore ι) q)))
    (types : E → RSubsets S t → κ)
    (hValues : ∀ (i : E) (q : RSubsets S t),
      fB (mapRSubset ι (unorderedInsertExterior q i)) =
        types i q)
    (htypes : Function.Injective types)
    (i j : E) (hij : i ≠ j)
    (l : unorderedKernelCorePointwiseFixer fB (unorderedEmbeddedCore ι)) :
    l.val (ι (Sum.inr i)) ≠ ι (Sum.inr j) := by
  intro hmap
  have hcol := unorderedCoreFixer_preserves_all_colours
    fB (unorderedEmbeddedCore ι) hsurj l
  have hcore (s : S) :
      l.val (ι (Sum.inl s)) = ι (Sum.inl s) :=
    l.property.2 s
  have hfun : types i = types j := by
    funext q
    have htransport := unorderedInsertExterior_transport
      ι l.val hcore i j hmap q
    calc
      types i q =
          fB (mapRSubset ι (unorderedInsertExterior q i)) :=
        (hValues i q).symm
      _ = fB (permuteRSubset l.val
          (mapRSubset ι (unorderedInsertExterior q i))) :=
        (hcol _).symm
      _ = fB (mapRSubset ι (unorderedInsertExterior q j)) := by
        rw [htransport]
      _ = types j q := hValues j q
  exact hij (htypes hfun)

end EPPAReducts.BoundedEquivalence
