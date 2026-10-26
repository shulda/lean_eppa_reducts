import EPPAReducts.BoundedEquivalence.OrderedCoreOnePartialShift
import EPPAReducts.BoundedEquivalence.OrderedCoreColourClasses
import EPPAReducts.BoundedEquivalence.OrderedExteriorColourDistinction

/-!
# A finite ordered bounded-equivalence obstruction candidate

This is an honest (unlabelled) equivalence relation on injective
ordered r-tuples, with at most m classes, together with a specified
literal family of partial automorphisms.

The construction is the input for the subsequent non-EPPA
contradiction.  This file proves the finite combinatorial *data*,
not the nonexistence of a finite EPPA witness.
-/

namespace EPPAReducts.BoundedEquivalence

open EPPAReducts.HumanTargets

/-- An equivalence relation on ordered injective r-tuples of a vertex
set V with at most m (unnamed) classes. -/
structure OrderedBoundedEquivalence (V : Type) (r m : ℕ) where
  sameClass : Setoid (InjectiveTuples V r)
  atMostClasses : HasAtMostClasses sameClass m

/-- Preservation and reflection of the unlabelled tuple-equivalence
relation by a literal partial bijection of the vertex carrier. -/
def IsOrderedBoundedPartialAutomorphism
    {V : Type} {r m : ℕ}
    (A : OrderedBoundedEquivalence V r m)
    (p : PartialBijection V) : Prop :=
  ∀ t u : InjectiveTuples {v : V // v ∈ p.source} r,
    A.sameClass.r
      (mapInjectiveTuple (subtypeEmbedding p.source) t)
      (mapInjectiveTuple (subtypeEmbedding p.source) u) ↔
    A.sameClass.r
      (mapInjectiveTuple
        (equivThenEmbedding p.bijection (subtypeEmbedding p.target)) t)
      (mapInjectiveTuple
        (equivThenEmbedding p.bijection (subtypeEmbedding p.target)) u)

/-- The explicit cyclic ordered obstruction is the unlabelled kernel
of the total core/exterior colouring. It satisfies the at-most-m
condition, not merely an exactly-m named colouring assumption. -/
noncomputable def orderedCyclicObstruction
    (m r : ℕ) (hm : 2 ≤ m) (hr : 2 ≤ r) :
    OrderedBoundedEquivalence (Sum (ZMod (m * r)) (Fin r)) r m where
  sameClass := orderedCoreExteriorKernel m (m * r) r
    (show m ∣ m * r from ⟨r, rfl⟩)
    (lt_of_lt_of_le (by decide : 1 < 2) hr)
  atMostClasses :=
    orderedCoreExteriorKernel_hasAtMostClasses m (m * r) r
      (lt_of_lt_of_le (by decide : 0 < 2) hm)
      (show m ∣ m * r from ⟨r, rfl⟩)
      (lt_of_lt_of_le (by decide : 1 < 2) hr)

/-- The cyclic core plus r exterior labels is genuinely finite
whenever m,r >= 2. -/
theorem orderedCyclicObstruction_carrierFinite
    (m r : ℕ) (hm : 2 ≤ m) (hr : 2 ≤ r) :
    Finite (Sum (ZMod (m * r)) (Fin r)) := by
  have hpos : 0 < m * r :=
    Nat.mul_pos (lt_of_lt_of_le (by decide : 0 < 2) hm)
      (lt_of_lt_of_le (by decide : 0 < 2) hr)
  letI : NeZero (m * r) := ⟨Nat.ne_of_gt hpos⟩
  infer_instance

/-- For each exterior vertex a_i, the actual cyclic-core shift
fixing a_i is a partial automorphism of the *unlabelled* tuple
equivalence relation. -/
theorem orderedCyclicObstruction_partialAut
    (m r : ℕ) [Fintype (ZMod (m * r))]
    (hm : 2 ≤ m) (hr : 2 ≤ r) (i : Fin r) :
    IsOrderedBoundedPartialAutomorphism
      (orderedCyclicObstruction m r hm hr)
      (orderedCoreOnePartialShift i) := by
  have hpos : 0 < m * r :=
    Nat.mul_pos (lt_of_lt_of_le (by decide : 0 < 2) hm)
      (lt_of_lt_of_le (by decide : 0 < 2) hr)
  letI : NeZero (m * r) := ⟨Nat.ne_of_gt hpos⟩
  change IsOrderedTupleKernelPartialAutomorphism
    (fun t : InjectiveTuples (Sum (ZMod (m * r)) (Fin r)) r =>
      orderedCoreExteriorColour m (m * r) r
        (show m ∣ m * r from ⟨r, rfl⟩)
        (lt_of_lt_of_le (by decide : 1 < 2) hr) t.val)
    (orderedCoreOnePartialShift i)
  exact orderedCoreOnePartialShift_isPartialAutomorphism
    m (m * r) r (show m ∣ m * r from ⟨r, rfl⟩)
    (lt_of_lt_of_le (by decide : 1 < 2) hr) i

/-- Packaging theorem: for every r,m>=2 there is one common finite
unlabelled ordered-tuple structure and r designated partial
automorphisms of that SAME structure. -/
theorem orderedCyclicObstruction_hasPartials
    (m r : ℕ) (hm : 2 ≤ m) (hr : 2 ≤ r) :
    ∃ (V : Type), Finite V ∧
      ∃ (A : OrderedBoundedEquivalence V r m)
        (p : Fin r → PartialBijection V),
        ∀ i : Fin r, IsOrderedBoundedPartialAutomorphism A (p i) := by
  have hpos : 0 < m * r :=
    Nat.mul_pos (lt_of_lt_of_le (by decide : 0 < 2) hm)
      (lt_of_lt_of_le (by decide : 0 < 2) hr)
  letI : NeZero (m * r) := ⟨Nat.ne_of_gt hpos⟩
  exact ⟨Sum (ZMod (m * r)) (Fin r),
    orderedCyclicObstruction_carrierFinite m r hm hr,
    orderedCyclicObstruction m r hm hr,
    fun i => orderedCoreOnePartialShift i,
    orderedCyclicObstruction_partialAut m r hm hr⟩

end EPPAReducts.BoundedEquivalence
