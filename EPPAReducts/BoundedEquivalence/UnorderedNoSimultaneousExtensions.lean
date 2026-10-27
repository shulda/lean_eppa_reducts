import EPPAReducts.BoundedEquivalence.UnorderedExteriorRigidity
import EPPAReducts.BoundedEquivalence.UnorderedFiniteObstructionData
import EPPAReducts.BoundedEquivalence.UnorderedCoreCosetCollision
import EPPAReducts.BoundedEquivalence.OrderedOldCoreShift

/-!
# The unordered cyclic obstruction forbids simultaneous full extensions

No finite induced extension of the explicit unlabelled cyclic-coloured
unordered r-subset structure can have r full automorphisms all shifting
the old cyclic core and each fixing its own exterior vertex. The
argument combines the certified normalizer-coset collision and
the separation of distinct exterior colour types by the core
pointwise-fixer. Numerical ZMod m colours are only proof data.
-/

namespace EPPAReducts.BoundedEquivalence

theorem unorderedCyclicCore_exterior_extensions_impossible
    (m b : ℕ) (hm : 2 ≤ m) (hb : 1 ≤ b)
    {W : Type} [Fintype W] [DecidableEq W]
    (ι : Sum (ZMod (unorderedCommonCoreSize m (b + 1)))
        (Fin (b + 1)) ↪ W)
    (fB : RSubsets W (b + 1) → ZMod m)
    (hOld : ∀ q : RSubsets
        (Sum (ZMod (unorderedCommonCoreSize m (b + 1))) (Fin (b + 1)))
        (b + 1),
      fB (mapRSubset ι q) =
        unorderedCyclicObstructionColour m b q)
    (g : Fin (b + 1) → Equiv.Perm W)
    (hg : ∀ i, g i ∈ unorderedSubsetKernelAutSubgroup fB)
    (hgcore : ∀ (i : Fin (b + 1))
        (s : ZMod (unorderedCommonCoreSize m (b + 1))),
      g i (ι (Sum.inl s)) = ι (Sum.inl (s + 1)))
    (hfix : ∀ (i : Fin (b + 1)),
      g i (ι (Sum.inr i)) = ι (Sum.inr i)) :
    False := by
  classical
  let N := unorderedCommonCoreSize m (b + 1)
  have hmpos : 0 < m := by omega
  letI : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  let coreIn : ZMod N ↪
      Sum (ZMod N) (Fin (b + 1)) :=
    unorderedCoreInclusion
  have hcoreMap (q : RSubsets (ZMod N) (b + 1)) :
      mapRSubset (unorderedEmbeddedCore ι) q =
      mapRSubset ι (mapRSubset coreIn q) := by
    apply Subtype.ext
    change q.val.map (unorderedEmbeddedCore ι) =
      (q.val.map coreIn).map ι
    rw [Finset.map_map]
    congr 1
  have hcoreColour (q : RSubsets (ZMod N) (b + 1)) :
      fB (mapRSubset (unorderedEmbeddedCore ι) q) =
        unorderedCyclicSumColour
          (unorderedCommonCoreSize_dvd_r m (b + 1)) q := by
    rw [hcoreMap]
    exact (hOld (mapRSubset coreIn q)).trans
      (unorderedCyclicObstructionColour_on_core m b q)
  have hsurjCore : Function.Surjective
      (fun q : RSubsets (ZMod N) (b + 1) =>
        fB (mapRSubset (unorderedEmbeddedCore ι) q)) := by
    intro c
    obtain ⟨q, hq⟩ :=
      unorderedCyclicObstruction_core_surjective m b hm hb c
    exact ⟨q, (hcoreColour q).trans
      ((unorderedCyclicObstructionColour_on_core m b q).symm.trans hq)⟩
  have hshiftCore (q : RSubsets (ZMod N) (b + 1)) :
      fB (mapRSubset (unorderedEmbeddedCore ι)
        (permuteRSubset (orderedUnitCorePerm N) q)) =
        fB (mapRSubset (unorderedEmbeddedCore ι) q) +
          (1 : ZMod m) := by
    calc
      fB (mapRSubset (unorderedEmbeddedCore ι)
          (permuteRSubset (orderedUnitCorePerm N) q)) =
        unorderedCyclicSumColour
          (unorderedCommonCoreSize_dvd_r m (b + 1))
          (permuteRSubset (orderedUnitCorePerm N) q) :=
        hcoreColour _
      _ = unorderedCyclicSumColour
          (unorderedCommonCoreSize_dvd_r m (b + 1)) q + 1 :=
        unorderedCyclicSumColour_translate_one
          N m (b + 1) hm (by omega)
          (unorderedCommonCoreSize_dvd_r m (b + 1)) q
      _ = fB (mapRSubset (unorderedEmbeddedCore ι) q) + 1 := by
        rw [hcoreColour q]
  have hOne : (1 : ZMod m) ≠ 0 := by
    intro h
    have hOneEq : m = 1 := ZMod.one_eq_zero_iff.mp h
    omega
  have hcore (i : Fin (b + 1)) (s : ZMod N) :
      g i (unorderedEmbeddedCore ι s) =
        unorderedEmbeddedCore ι ((orderedUnitCorePerm N) s) := by
    change g i (ι (Sum.inl s)) = ι (Sum.inl (s + 1))
    exact hgcore i s
  let a : Fin (b + 1) ↪ W :=
    ⟨fun i => ι (Sum.inr i), by
      intro i j h
      exact Sum.inr_injective (ι.injective h)⟩
  have ha (i : Fin (b + 1)) : g i (a i) = a i :=
    hfix i
  obtain ⟨i, j, hij, ⟨l, hl⟩⟩ :=
    unorderedKernel_core_extension_orbit_collision b fB
      (unorderedEmbeddedCore ι) (orderedUnitCorePerm N)
      (1 : ZMod m) hOne hsurjCore hshiftCore a g hg hcore ha
  let types : Fin (b + 1) → RSubsets (ZMod N) b → ZMod m :=
    fun i => unorderedCommonCoreExteriorTypes m (b + 1)
      (Fin.cast (by omega : b + 1 = ((b + 1) - 1) + 1) i)
  have htypes : Function.Injective types :=
    unorderedCommonCoreExteriorTypes_fin_r_injective
      m (b + 1) hm (by omega)
  have hValues (i : Fin (b + 1))
      (q : RSubsets (ZMod N) b) :
      fB (mapRSubset ι (unorderedInsertExterior q i)) =
        types i q := by
    exact (hOld (unorderedInsertExterior q i)).trans
      (unorderedCyclicObstructionColour_on_exterior m b q i)
  exact (unorderedExterior_not_coreFixer_related
    ι fB hsurjCore types hValues htypes i j hij l) hl

end EPPAReducts.BoundedEquivalence
