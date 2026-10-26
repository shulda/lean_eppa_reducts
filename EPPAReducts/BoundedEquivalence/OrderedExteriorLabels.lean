import EPPAReducts.BoundedEquivalence.OrderedCorePointwiseNormalizer
import EPPAReducts.BoundedEquivalence.OrderedExteriorColourDistinction
import EPPAReducts.BoundedEquivalence.CoreLabelAction

/-!
# Different exterior vertices are in different core-fixer orbits

Given any induced extension of the explicit ordered cyclic colouring,
the old core realizes all auxiliary classes. Therefore every
automorphism fixing the old core pointwise fixes all classes. But
switching two distinct exterior vertices while leaving the old
core fixed changes the class of a suitable ordered tuple.

This excludes any such exterior-vertex switch in the automorphism
group of an arbitrary extension, not merely in the original finite
structure.
-/

namespace EPPAReducts.BoundedEquivalence

/-- The embedded cyclic core inside a further ambient embedding. -/
def orderedEmbeddedCore {S E W : Type}
    (ι : Sum S E ↪ W) : S ↪ W where
  toFun s := ι (Sum.inl s)
  inj' := by
    intro s t h
    exact Sum.inl_injective (ι.injective h)

/-- An automorphism of the unlabelled ordered kernel, fixing each
embedded core vertex, acts trivially on all auxiliary colour classes
when every class already occurs on tuples from that core. -/
theorem orderedCoreFixer_preserves_all_colours
    {S W κ : Type} {r : ℕ}
    (fB : InjectiveTuples W r → κ) (ι : S ↪ W)
    (hsurj : Function.Surjective
      (fun t : InjectiveTuples S r =>
        fB (mapInjectiveTuple ι t)))
    (l : orderedKernelCorePointwiseFixer fB ι) :
    ∀ t : InjectiveTuples W r,
      fB (permuteOrderedTuple l.val t) = fB t := by
  apply core_pointwise_fixed_preserves_labels
    (mapInjectiveTuple ι) fB hsurj
    (permuteOrderedTuple l.val)
  · intro t u h
    exact (l.property.1 t u).mp h
  · intro t
    apply Subtype.ext
    funext j
    exact l.property.2 (t.val j)

/-- The two exterior tuples with one vertex in the same position
are carried one to the other by an automorphism fixing the entire
embedded core if that automorphism carries their exterior labels
to one another. -/
theorem orderedExteriorTuple_image
    {S W : Type} {r : ℕ}
    (ι : Sum S (Fin r) ↪ W)
    (l : Equiv.Perm W)
    (hcore : ∀ s : S, l (ι (Sum.inl s)) = ι (Sum.inl s))
    (i j : Fin r)
    (hij : l (ι (Sum.inr i)) = ι (Sum.inr j))
    (core : InjectiveTuples S r) :
    permuteOrderedTuple l
      (mapInjectiveTuple ι (orderedInsertExterior core i i)) =
    mapInjectiveTuple ι (orderedInsertExterior core i j) := by
  apply Subtype.ext
  funext k
  change l (ι ((orderedInsertExterior core i i).val k)) =
    ι ((orderedInsertExterior core i j).val k)
  by_cases hk : k = i
  · subst k
    simpa only [orderedInsertExterior_at_slot] using hij
  · rw [orderedInsertExterior_at_ne core i i k hk,
        orderedInsertExterior_at_ne core i j k hk]
    exact hcore (core.val k)

/-- Distinct exterior labels cannot lie in the same orbit under
the group of unlabelled-kernel automorphisms fixing the embedded
old core pointwise. The proof needs one injected core r-tuple with
different positional corrections; it works also for r=2. -/
theorem orderedExterior_not_coreFixer_related
    (m N r : ℕ) (hmN : m ∣ N)
    (hm : 2 ≤ m) (hr : 1 < r)
    {W : Type} (ι : Sum (ZMod N) (Fin r) ↪ W)
    (fB : InjectiveTuples W r → ZMod m)
    (hext : ∀ t : InjectiveTuples (Sum (ZMod N) (Fin r)) r,
      fB (mapInjectiveTuple ι t) =
        orderedCoreExteriorColour m N r hmN hr t.val)
    (hsurj : Function.Surjective
      (fun t : InjectiveTuples (ZMod N) r =>
        fB (mapInjectiveTuple (orderedEmbeddedCore ι) t)))
    (core : InjectiveTuples (ZMod N) r)
    (i j : Fin r) (hij : i ≠ j)
    (l : orderedKernelCorePointwiseFixer fB (orderedEmbeddedCore ι)) :
    l.val (ι (Sum.inr i)) ≠ ι (Sum.inr j) := by
  intro hmap
  have hcol := orderedCoreFixer_preserves_all_colours
    fB (orderedEmbeddedCore ι) hsurj l
  have htuple := orderedExteriorTuple_image ι l.val
    (fun s => l.property.2 s) i j hmap core
  have heq :
      fB (mapInjectiveTuple ι (orderedInsertExterior core i i)) =
        fB (mapInjectiveTuple ι (orderedInsertExterior core i j)) := by
    calc
      fB (mapInjectiveTuple ι (orderedInsertExterior core i i)) =
        fB (permuteOrderedTuple l.val
          (mapInjectiveTuple ι (orderedInsertExterior core i i))) :=
        (hcol _).symm
      _ = fB (mapInjectiveTuple ι
          (orderedInsertExterior core i j)) := by rw [htuple]
  have hbad :
      orderedCoreExteriorColour m N r hmN hr
        (orderedInsertExterior core i i).val =
      orderedCoreExteriorColour m N r hmN hr
        (orderedInsertExterior core i j).val := by
    simpa only [hext] using heq
  exact orderedCoreExteriorColour_distinct_at_slot
    m N r hmN hm hr core i j hij hbad

end EPPAReducts.BoundedEquivalence
