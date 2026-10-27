import EPPAReducts.BoundedEquivalence.UnorderedFiniteObstructionData
import EPPAReducts.BoundedEquivalence.UnorderedTotalColourShift
import EPPAReducts.BoundedEquivalence.OrderedCoreOnePartialShift
import EPPAReducts.BoundedEquivalence.OrderedOldCoreShift

/-!
# The genuine partial automorphisms of the finite unordered obstruction

For each exterior vertex a_i, restrict the cyclic-core unit translation
to the induced domain consisting of the full core and a_i. The
resulting literal HumanTargets.PartialBijection increases every
auxiliary r-subset colour by one and hence preserves equality of
colours. The underlying structure still has UNNAMED classes.
-/

namespace EPPAReducts.BoundedEquivalence

open EPPAReducts.HumanTargets

/-- Every external coordinate appearing in an r-subset of the
core-plus-one-exterior induced domain is the designated exterior i. -/
theorem unorderedCoreOneSubset_support
    {N r : ℕ} [Fintype (ZMod N)] (i : Fin r)
    (q : RSubsets
      {v : Sum (ZMod N) (Fin r) //
        v ∈ (orderedCoreOnePartialShift i).source} r) :
    ∀ j ∈
      (mapRSubset
        (subtypeEmbedding (orderedCoreOnePartialShift i).source) q).val.toRight,
      j = i := by
  classical
  intro j hj
  have hin :
      (Sum.inr j : Sum (ZMod N) (Fin r)) ∈
        (mapRSubset
          (subtypeEmbedding (orderedCoreOnePartialShift i).source) q).val :=
    Finset.mem_toRight.mp hj
  obtain ⟨v, hv, heq⟩ := Finset.mem_map.mp hin
  have heqx : v.val = Sum.inr j := by
    simpa [subtypeEmbedding] using heq
  have hm : (Sum.inr j : Sum (ZMod N) (Fin r)) ∈ orderedCoreOne i := by
    rw [← heqx]
    exact v.property
  exact (mem_orderedCoreOne_inr i j).mp hm

/-- The literal restricted partial bijection is the restriction
of the genuine global permutation shifting the cyclic core and
fixing every exterior vertex, also on unordered r-subsets. -/
theorem unorderedCoreOnePartialShift_subset_action
    {N r : ℕ} [Fintype (ZMod N)]
    (i : Fin r)
    (q : RSubsets
      {v : Sum (ZMod N) (Fin r) //
        v ∈ (orderedCoreOnePartialShift i).source} r) :
    mapRSubset
      (equivThenEmbedding
        (orderedCoreOnePartialShift i).bijection
        (subtypeEmbedding (orderedCoreOnePartialShift i).target)) q =
      permuteRSubset
        (unorderedCoreShiftPerm (E := Fin r) (orderedUnitCorePerm N))
        (mapRSubset
          (subtypeEmbedding (orderedCoreOnePartialShift i).source) q) := by
  classical
  apply Subtype.ext
  change q.val.map
      (equivThenEmbedding
        (orderedCoreOnePartialShift i).bijection
        (subtypeEmbedding (orderedCoreOnePartialShift i).target)) =
    (q.val.map
      (subtypeEmbedding (orderedCoreOnePartialShift i).source)).map
        (⟨unorderedCoreShiftPerm (E := Fin r) (orderedUnitCorePerm N),
          (unorderedCoreShiftPerm (E := Fin r)
            (orderedUnitCorePerm N)).injective⟩ :
          Sum (ZMod N) (Fin r) ↪ Sum (ZMod N) (Fin r))
  rw [Finset.map_map]
  congr 1
  apply Function.Embedding.ext
  intro v
  change ((orderedCoreOnePartialShift i).bijection v).val =
    (unorderedCoreShiftPerm (E := Fin r) (orderedUnitCorePerm N)) v.val
  rw [orderedCoreOnePartialShift_apply]
  rfl

/-- The concrete partial cyclic-core shift increases the colour
of every unordered r-subset of its induced domain by one. -/
theorem unorderedCyclicObstruction_partial_colour_shift
    (m b : ℕ)
    [Fintype (ZMod (unorderedCommonCoreSize m (b + 1)))]
    (hm : 2 ≤ m) (hb : 1 ≤ b) (i : Fin (b + 1))
    (q : RSubsets
      {v : Sum (ZMod (unorderedCommonCoreSize m (b + 1))) (Fin (b + 1)) //
        v ∈ (orderedCoreOnePartialShift i).source} (b + 1)) :
    unorderedCyclicObstructionColour m b
      (mapRSubset
        (equivThenEmbedding (orderedCoreOnePartialShift i).bijection
          (subtypeEmbedding (orderedCoreOnePartialShift i).target)) q) =
      unorderedCyclicObstructionColour m b
        (mapRSubset
          (subtypeEmbedding (orderedCoreOnePartialShift i).source) q) + 1 := by
  classical
  let N := unorderedCommonCoreSize m (b + 1)
  let base : RSubsets (ZMod N) (b + 1) → ZMod m :=
    unorderedCyclicSumColour (unorderedCommonCoreSize_dvd_r m (b + 1))
  let exterior : Fin (b + 1) → RSubsets (ZMod N) b → ZMod m :=
    fun j => unorderedCommonCoreExteriorTypes m (b + 1)
      (Fin.cast (by omega : b + 1 = ((b + 1) - 1) + 1) j)
  have hbase : ∀ y : RSubsets (ZMod N) (b + 1),
      base (permuteRSubset (orderedUnitCorePerm N) y) = base y + 1 := by
    intro y
    exact unorderedCyclicSumColour_translate_one N m (b + 1)
      hm (by omega) (unorderedCommonCoreSize_dvd_r m (b + 1)) y
  have hext : ∀ y : RSubsets (ZMod N) b,
      exterior i (permuteRSubset (orderedUnitCorePerm N) y) =
        exterior i y + 1 := by
    intro y
    exact unorderedCommonCoreExteriorTypes_translate_one
      m (b + 1) hm (by omega)
      (Fin.cast (by omega : b + 1 = ((b + 1) - 1) + 1) i) y
  have hsupp :=
    unorderedCoreOneSubset_support i q
  have hshift := unorderedTotalColour_shift_on_coreOne
    base exterior (orderedUnitCorePerm N) i (1 : ZMod m)
    hbase hext
    (mapRSubset
      (subtypeEmbedding (orderedCoreOnePartialShift i).source) q)
    hsupp
  rw [unorderedCoreOnePartialShift_subset_action i q]
  exact hshift

/-- The designated core-plus-one-exterior maps are genuine
partial automorphisms of the *unlabelled* finite relation,
not merely automorphisms of a named-colour expansion. -/
theorem unorderedCyclicObstruction_partialAut
    (m b : ℕ)
    [Fintype (ZMod (unorderedCommonCoreSize m (b + 1)))]
    (hm : 2 ≤ m) (hb : 1 ≤ b) (i : Fin (b + 1)) :
    IsUnorderedBoundedPartialAutomorphism
      (unorderedCyclicObstruction m b hm hb)
      (orderedCoreOnePartialShift i) := by
  intro q s
  change unorderedCyclicObstructionColour m b
      (mapRSubset
        (subtypeEmbedding (orderedCoreOnePartialShift i).source) q) =
      unorderedCyclicObstructionColour m b
        (mapRSubset
          (subtypeEmbedding (orderedCoreOnePartialShift i).source) s) ↔
      unorderedCyclicObstructionColour m b
        (mapRSubset
          (equivThenEmbedding (orderedCoreOnePartialShift i).bijection
            (subtypeEmbedding (orderedCoreOnePartialShift i).target)) q) =
      unorderedCyclicObstructionColour m b
        (mapRSubset
          (equivThenEmbedding (orderedCoreOnePartialShift i).bijection
            (subtypeEmbedding (orderedCoreOnePartialShift i).target)) s)
  rw [unorderedCyclicObstruction_partial_colour_shift m b hm hb i q,
      unorderedCyclicObstruction_partial_colour_shift m b hm hb i s]
  constructor
  · intro h
    rw [h]
  · intro h
    exact add_right_cancel h

end EPPAReducts.BoundedEquivalence
