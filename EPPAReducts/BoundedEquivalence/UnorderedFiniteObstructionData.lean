import EPPAReducts.BoundedEquivalence.UnorderedTotalColour
import EPPAReducts.BoundedEquivalence.UnorderedCommonCoreExteriorTypes
import EPPAReducts.BoundedEquivalence.UnlabelledZModPresentation

/-!
# Finite unlabelled unordered r-subset obstruction: the concrete data

The carrier is a cyclic core of cardinality m*r*(r-1) together with
r distinguishable exterior vertices. An auxiliary ZMod m colouring
is prescribed on ALL r-subsets: the certified cyclic-sum colour on
core subsets, the i-th equivariant exterior type on core-plus-a_i,
and zero whenever at least two exterior vertices occur.

The actual structure is the equivalence relation of equal auxiliary
colours. The colours are not named relations. This module constructs
a finite candidate and verifies all classes occur already on its
old core; the EPPA contradiction requires further steps.
-/

namespace EPPAReducts.BoundedEquivalence

/-- One auxiliary colouring of all (b+1)-subsets of the disjoint
union of the cyclic core and its (b+1) exterior vertices. -/
noncomputable def unorderedCyclicObstructionColour
    (m b : ℕ) :
    RSubsets
      (Sum (ZMod (unorderedCommonCoreSize m (b + 1))) (Fin (b + 1)))
      (b + 1) → ZMod m :=
  unorderedTotalColour (t := b)
    (unorderedCyclicSumColour (unorderedCommonCoreSize_dvd_r m (b + 1)))
    (fun i : Fin (b + 1) =>
      unorderedCommonCoreExteriorTypes m (b + 1)
        (Fin.cast (by omega : b + 1 = ((b + 1) - 1) + 1) i))

/-- The actual finite unlabelled relation, with no distinguished
colour names and at most m unnamed equivalence classes. -/
noncomputable def unorderedCyclicObstruction
    (m b : ℕ) (hm : 2 ≤ m) (hb : 1 ≤ b) :
    UnorderedBoundedEquivalence
      (Sum (ZMod (unorderedCommonCoreSize m (b + 1))) (Fin (b + 1)))
      (b + 1) m where
  sameClass := colourKernelSetoid (unorderedCyclicObstructionColour m b)
  atMostClasses := colourKernelSetoid_hasAtMostClasses m (by omega)
    (unorderedCyclicObstructionColour m b)

/-- The candidate's vertex carrier is finite even at the smallest
allowed parameters (m=2 and b=1). -/
theorem unorderedCyclicObstruction_carrierFinite
    (m b : ℕ) (hm : 2 ≤ m) (hb : 1 ≤ b) :
    Finite
      (Sum (ZMod (unorderedCommonCoreSize m (b + 1))) (Fin (b + 1))) := by
  have hN : 0 < unorderedCommonCoreSize m (b + 1) :=
    unorderedCommonCoreSize_pos m (b + 1) hm (by omega)
  letI : NeZero (unorderedCommonCoreSize m (b + 1)) :=
    ⟨Nat.ne_of_gt hN⟩
  infer_instance

/-- Exact value on every embedded core subset. -/
theorem unorderedCyclicObstructionColour_on_core
    (m b : ℕ)
    (q : RSubsets (ZMod (unorderedCommonCoreSize m (b + 1))) (b + 1)) :
    unorderedCyclicObstructionColour m b
      (mapRSubset (unorderedCoreInclusion (E := Fin (b + 1))) q) =
        unorderedCyclicSumColour
          (unorderedCommonCoreSize_dvd_r m (b + 1)) q := by
  unfold unorderedCyclicObstructionColour
  exact unorderedTotalColour_on_core _ _ q

/-- Exact value on an r-subset with precisely one exterior vertex. -/
theorem unorderedCyclicObstructionColour_on_exterior
    (m b : ℕ)
    (q : RSubsets (ZMod (unorderedCommonCoreSize m (b + 1))) b)
    (i : Fin (b + 1)) :
    unorderedCyclicObstructionColour m b
      (unorderedInsertExterior q i) =
        unorderedCommonCoreExteriorTypes m (b + 1)
          (Fin.cast (by omega : b + 1 = ((b + 1) - 1) + 1) i) q := by
  unfold unorderedCyclicObstructionColour
  exact unorderedTotalColour_on_exterior _ _ q i

/-- All m colour classes of the actual finite old structure are
already realized by (b+1)-subsets entirely in the cyclic core. -/
theorem unorderedCyclicObstruction_core_surjective
    (m b : ℕ) (hm : 2 ≤ m) (hb : 1 ≤ b) :
    Function.Surjective
      (fun q : RSubsets (ZMod (unorderedCommonCoreSize m (b + 1))) (b + 1) =>
        unorderedCyclicObstructionColour m b
          (mapRSubset (unorderedCoreInclusion (E := Fin (b + 1))) q)) := by
  have hbase :=
    (unorderedCommonCore_two_surjective_colours
      m (b + 1) hm (by omega)).1
  intro c
  obtain ⟨q, hq⟩ := hbase c
  exact ⟨q, (unorderedCyclicObstructionColour_on_core m b q).trans hq⟩

end EPPAReducts.BoundedEquivalence
