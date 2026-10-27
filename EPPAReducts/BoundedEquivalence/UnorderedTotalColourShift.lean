import EPPAReducts.BoundedEquivalence.UnorderedTotalColour
import Mathlib.Data.Finset.Sum

/-!
# Partial-shift compatible total colourings of unordered subsets

A subset supported on a core plus one distinguished exterior vertex
is either a pure-core subset or a unique inserted-exterior subset.
Consequently a core permutation which increases the corresponding
base and exterior auxiliary colours by one increases the total
colour by one on every such subset. Other exterior types are
irrelevant to the induced partial automorphism.
-/

namespace EPPAReducts.BoundedEquivalence

/-- Permute a core and fix every exterior vertex. -/
def unorderedCoreShiftPerm {S E : Type}
    (p : Equiv.Perm S) : Equiv.Perm (Sum S E) :=
  Equiv.sumCongr p (Equiv.refl E)

/-- A (t+1)-subset containing no exterior vertices besides a
designated i has one of the two required canonical forms. -/
theorem unorderedCoreOne_decomposition
    {S E : Type} {t : ℕ} (i : E)
    (q : RSubsets (Sum S E) (t + 1))
    (hsupp : ∀ j ∈ q.val.toRight, j = i) :
    (∃ y : RSubsets S (t + 1),
      q = mapRSubset (unorderedCoreInclusion (S := S) (E := E)) y) ∨
    (∃ y : RSubsets S t, q = unorderedInsertExterior y i) := by
  classical
  by_cases h0 : q.val.toRight = ∅
  · have hc : q.val.toLeft.card = t + 1 := by
      have h := Finset.card_toLeft_add_card_toRight (u := q.val)
      simpa [h0, q.property] using h
    let y : RSubsets S (t + 1) := ⟨q.val.toLeft, hc⟩
    left
    refine ⟨y, ?_⟩
    apply Subtype.ext
    have hy := unorderedCoreImage_parts (E := E) y
    calc
      q.val = q.val.toLeft.disjSum q.val.toRight :=
        (Finset.toLeft_disjSum_toRight).symm
      _ = y.val.disjSum (∅ : Finset E) := by
        simp only [y, h0]
      _ = (mapRSubset (unorderedCoreInclusion (S := S) (E := E)) y).val := by
        have h := Finset.toLeft_disjSum_toRight
          (u := (mapRSubset (unorderedCoreInclusion (S := S) (E := E)) y).val)
        rw [hy.1, hy.2] at h
        exact h
  · obtain ⟨j, hj⟩ : q.val.toRight.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr h0
    have hji : j = i := hsupp j hj
    have hr : q.val.toRight = {i} := by
      ext x
      constructor
      · intro hx
        simpa only [Finset.mem_singleton] using hsupp x hx
      · intro hx
        have hxi : x = i := Finset.mem_singleton.mp hx
        subst x
        simpa only [hji] using hj
    have hc : q.val.toLeft.card = t := by
      have h := Finset.card_toLeft_add_card_toRight (u := q.val)
      rw [hr, Finset.card_singleton, q.property] at h
      omega
    let y : RSubsets S t := ⟨q.val.toLeft, hc⟩
    right
    refine ⟨y, ?_⟩
    apply Subtype.ext
    have hy := unorderedInsertExterior_parts y i
    calc
      q.val = q.val.toLeft.disjSum q.val.toRight :=
        (Finset.toLeft_disjSum_toRight).symm
      _ = y.val.disjSum ({i} : Finset E) := by
        simp only [y, hr]
      _ = (unorderedInsertExterior y i).val := by
        have h := Finset.toLeft_disjSum_toRight
          (u := (unorderedInsertExterior y i).val)
        rw [hy.1, hy.2] at h
        exact h

/-- Core permutations act naturally on embedded pure-core subsets. -/
theorem unorderedCoreShiftPerm_on_core
    {S E : Type} {t : ℕ}
    (p : Equiv.Perm S) (y : RSubsets S t) :
    permuteRSubset (unorderedCoreShiftPerm (E := E) p)
      (mapRSubset (unorderedCoreInclusion (S := S) (E := E)) y) =
      mapRSubset (unorderedCoreInclusion (S := S) (E := E))
        (permuteRSubset p y) := by
  classical
  apply Subtype.ext
  change (y.val.map (unorderedCoreInclusion (S := S) (E := E))).map
      (⟨unorderedCoreShiftPerm p, (unorderedCoreShiftPerm p).injective⟩ :
        Sum S E ↪ Sum S E) =
    (y.val.map (⟨p, p.injective⟩ : S ↪ S)).map
      (unorderedCoreInclusion (S := S) (E := E))
  rw [Finset.map_map, Finset.map_map]
  congr 1
  apply Function.Embedding.ext
  intro x
  rfl

/-- The core action transports a single exterior subset, while
fixing its exterior vertex. -/
theorem unorderedCoreShiftPerm_on_exterior
    {S E : Type} {t : ℕ}
    (p : Equiv.Perm S) (y : RSubsets S t) (i : E) :
    permuteRSubset (unorderedCoreShiftPerm (E := E) p)
      (unorderedInsertExterior y i) =
      unorderedInsertExterior (permuteRSubset p y) i := by
  classical
  apply Subtype.ext
  change ((unorderedInsertExterior y i).val).map
      (⟨unorderedCoreShiftPerm p, (unorderedCoreShiftPerm p).injective⟩ :
        Sum S E ↪ Sum S E) =
    (unorderedInsertExterior (permuteRSubset p y) i).val
  rw [unorderedInsertExterior_val y i,
    unorderedInsertExterior_val (permuteRSubset p y) i]
  simp only [Finset.map_insert]
  change insert (Sum.inr i)
      ((y.val.map (unorderedCoreInclusion (S := S) (E := E))).map
        (⟨unorderedCoreShiftPerm p, (unorderedCoreShiftPerm p).injective⟩ :
          Sum S E ↪ Sum S E)) =
    insert (Sum.inr i)
      ((y.val.map (⟨p, p.injective⟩ : S ↪ S)).map
        (unorderedCoreInclusion (S := S) (E := E)))
  congr 1
  rw [Finset.map_map, Finset.map_map]
  congr 1
  apply Function.Embedding.ext
  intro x
  rfl

/-- The finite obstruction's total colouring is shifted by one
on all subsets supported in the old core plus one exterior i. -/
theorem unorderedTotalColour_shift_on_coreOne
    {S E κ : Type} [AddGroup κ] {t : ℕ}
    (base : RSubsets S (t + 1) → κ)
    (exterior : E → RSubsets S t → κ)
    (p : Equiv.Perm S) (i : E)
    (hbase : ∀ y : RSubsets S (t + 1),
      base (permuteRSubset p y) = base y + 1)
    (hext : ∀ y : RSubsets S t,
      exterior i (permuteRSubset p y) = exterior i y + 1)
    (q : RSubsets (Sum S E) (t + 1))
    (hsupp : ∀ j ∈ q.val.toRight, j = i) :
    unorderedTotalColour base exterior
        (permuteRSubset (unorderedCoreShiftPerm p) q) =
      unorderedTotalColour base exterior q + 1 := by
  rcases unorderedCoreOne_decomposition i q hsupp with
    ⟨y, rfl⟩ | ⟨y, rfl⟩
  · calc
      unorderedTotalColour base exterior
          (permuteRSubset (unorderedCoreShiftPerm p)
            (mapRSubset unorderedCoreInclusion y)) =
        unorderedTotalColour base exterior
          (mapRSubset unorderedCoreInclusion (permuteRSubset p y)) := by
          rw [unorderedCoreShiftPerm_on_core]
      _ = base (permuteRSubset p y) :=
        unorderedTotalColour_on_core base exterior _
      _ = base y + 1 := hbase y
      _ = unorderedTotalColour base exterior
          (mapRSubset unorderedCoreInclusion y) + 1 := by
          rw [unorderedTotalColour_on_core]
  · calc
      unorderedTotalColour base exterior
          (permuteRSubset (unorderedCoreShiftPerm p)
            (unorderedInsertExterior y i)) =
        unorderedTotalColour base exterior
          (unorderedInsertExterior (permuteRSubset p y) i) := by
          rw [unorderedCoreShiftPerm_on_exterior]
      _ = exterior i (permuteRSubset p y) :=
        unorderedTotalColour_on_exterior base exterior _ i
      _ = exterior i y + 1 := hext y
      _ = unorderedTotalColour base exterior
          (unorderedInsertExterior y i) + 1 := by
          rw [unorderedTotalColour_on_exterior]

end EPPAReducts.BoundedEquivalence
