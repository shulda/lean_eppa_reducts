import EPPAReducts.BoundedEquivalence.OrderedTupleFirstCoordinateColour
import Mathlib.Data.Fintype.EquivFin

/-!
# A concrete cyclic core and r distinguishable ordered exterior types

The ordered-tuple obstruction uses the core ZMod (m*r). Every tuple
length at most r has an injective realization on this core when both
parameters are positive. Consequently the explicit first-coordinate
colouring is surjective, and for m,r >= 2 there are r distinct
shift-equivariant exterior types, distinguished by insertion position.

These statements construct only auxiliary colours, not the
unlabelled equivalence relation or the final non-EPPA contradiction.
-/

namespace EPPAReducts.BoundedEquivalence

/-- Every tuple length up to r can be realized injectively on
the cyclic core of size m*r (m and r positive). -/
theorem cyclicCoreInjectiveTuple_nonempty
    (m r t : ℕ) (hm : 0 < m) (hr : 0 < r)
    (ht : t ≤ r) :
    Nonempty (InjectiveTuples (ZMod (m * r)) t) := by
  classical
  have hprod : m * r ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hm hr)
  letI : NeZero (m * r) := ⟨hprod⟩
  have hm1 : 1 ≤ m := hm
  have hmul : r ≤ m * r := by
    simpa only [one_mul] using (Nat.mul_le_mul_right r hm1)
  have hcard : Fintype.card (Fin t) ≤
      Fintype.card (ZMod (m * r)) := by
    simpa only [Fintype.card_fin, ZMod.card] using ht.trans hmul
  obtain ⟨e⟩ :
      Nonempty (Fin t ↪ ZMod (m * r)) :=
    Function.Embedding.nonempty_of_card_le hcard
  exact ⟨⟨e, e.injective⟩⟩

/-- On the cyclic core ZMod (m*r), every residue class appears
as the auxiliary first-coordinate colour of an injective ordered
r-tuple. No choice of translation-orbit representatives is needed. -/
theorem orderedCyclicCoreColour_surjective
    (m r : ℕ) (hm : 0 < m) (hr : 0 < r) :
    Function.Surjective
      (orderedTupleFirstCoordinateColour
        (show m ∣ m * r from ⟨r, rfl⟩) hr) := by
  letI : Nonempty (InjectiveTuples (ZMod (m * r)) r) :=
    cyclicCoreInjectiveTuple_nonempty m r r hm hr (le_refl r)
  exact orderedTupleFirstCoordinateColour_surjective _ _

/-- For m,r >= 2 there are r pairwise distinct exterior auxiliary
colour functions on (r-1)-tuples. The colour functions are indexed by
the external vertex label and depend on the insertion position.
Their shift-equivariance was established in the generic module. -/
theorem orderedCyclicExteriorTypes_injective
    (m r : ℕ) (hm : 2 ≤ m) (hr : 2 ≤ r) :
    Function.Injective
      (fun i : Fin r =>
        fun position : Fin r =>
          fun t : InjectiveTuples (ZMod (m * r)) (r - 1) =>
            orderedExteriorPositionColour
              (show m ∣ m * r from ⟨r, rfl⟩)
              (lt_of_lt_of_le (by decide : 1 < 2) hr)
              i position t) := by
  classical
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have hrpos : 0 < r := lt_of_lt_of_le (by decide : 0 < 2) hr
  have hrone : 1 < r := lt_of_lt_of_le (by decide : 1 < 2) hr
  let t : InjectiveTuples (ZMod (m * r)) (r - 1) :=
    Classical.choice
      (cyclicCoreInjectiveTuple_nonempty m r (r - 1)
        hmpos hrpos (Nat.sub_le r 1))
  intro i j heq
  by_contra hij
  have hpoint := congrFun (congrFun heq i) t
  exact (orderedExteriorPositionColour_distinct
    (show m ∣ m * r from ⟨r, rfl⟩) hrone hm i j hij t) hpoint

end EPPAReducts.BoundedEquivalence
