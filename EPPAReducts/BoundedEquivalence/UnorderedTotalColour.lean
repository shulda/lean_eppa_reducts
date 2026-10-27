import EPPAReducts.BoundedEquivalence.UnorderedExteriorInsertion
import Mathlib.Data.Finset.Sum

/-!
# An honest total colouring of unordered subsets of a core plus exterior vertices

Each (t+1)-subset of S ⊕ E has a canonical pair of left/right
parts. An auxiliary colour may be prescribed separately on pure core
subsets and on subsets containing exactly one exterior vertex,
without requiring named colours in the eventual equivalence language.
All subsets containing at least two exterior vertices receive zero.
-/

namespace EPPAReducts.BoundedEquivalence

/-- A total colouring extending a base colouring on (t+1)-subsets of
S and a family of exterior colours on t-subsets of S. No restriction
on S or E being finite, and no restriction on the colour type other
than a default zero for subsets with multiple exterior vertices. -/
noncomputable def unorderedTotalColour
    {S E κ : Type} [Zero κ] {t : ℕ}
    (base : RSubsets S (t + 1) → κ)
    (exterior : E → RSubsets S t → κ)
    (q : RSubsets (Sum S E) (t + 1)) : κ := by
  classical
  if hzero : q.val.toRight = ∅ then
    have hsize : q.val.toLeft.card = t + 1 := by
      have hc := Finset.card_toLeft_add_card_toRight (u := q.val)
      simpa [hzero, q.property] using hc
    exact base ⟨q.val.toLeft, hsize⟩
  else if hsingle : ∃ i : E, q.val.toRight = {i} then
    let i := Classical.choose hsingle
    have hi : q.val.toRight = {i} := Classical.choose_spec hsingle
    have hsize : q.val.toLeft.card = t := by
      have hc := Finset.card_toLeft_add_card_toRight (u := q.val)
      rw [hi, Finset.card_singleton, q.property] at hc
      omega
    exact exterior i ⟨q.val.toLeft, hsize⟩
  else
    exact 0

/-- Core inclusion as an induced image has no exterior vertices. -/
theorem unorderedCoreImage_parts
    {S E : Type} {n : ℕ} (core : RSubsets S n) :
    (mapRSubset (unorderedCoreInclusion (S := S) (E := E)) core).val.toLeft =
        core.val ∧
      (mapRSubset (unorderedCoreInclusion (S := S) (E := E)) core).val.toRight =
        (∅ : Finset E) := by
  classical
  have heq :
      (mapRSubset (unorderedCoreInclusion (S := S) (E := E)) core).val =
        core.val.disjSum (∅ : Finset E) := by
    change core.val.map (unorderedCoreInclusion (S := S) (E := E)) =
      core.val.disjSum (∅ : Finset E)
    exact (Finset.disjSum_empty core.val).symm
  constructor
  · rw [heq]
    simp only [Finset.toLeft_disjSum]
  · rw [heq]
    simp only [Finset.toRight_disjSum]

/-- The exterior insertion contains exactly that exterior vertex;
its left part is literally the originally prescribed core subset. -/
theorem unorderedInsertExterior_parts
    {S E : Type} {t : ℕ} (core : RSubsets S t) (i : E) :
    (unorderedInsertExterior core i).val.toLeft = core.val ∧
    (unorderedInsertExterior core i).val.toRight = ({i} : Finset E) := by
  classical
  have heq : (unorderedInsertExterior core i).val =
      core.val.disjSum ({i} : Finset E) := by
    rw [unorderedInsertExterior_val]
    ext x
    cases x <;> simp [Finset.mem_disjSum, unorderedCoreInclusion, eq_comm]
  rw [heq]
  simp

/-- On embedded pure core subsets, the total colour is exactly the
base colour. -/
theorem unorderedTotalColour_on_core
    {S E κ : Type} [Zero κ] {t : ℕ}
    (base : RSubsets S (t + 1) → κ)
    (exterior : E → RSubsets S t → κ)
    (core : RSubsets S (t + 1)) :
    unorderedTotalColour base exterior
      (mapRSubset (unorderedCoreInclusion (S := S) (E := E)) core) =
        base core := by
  classical
  have hp := unorderedCoreImage_parts (E := E) core
  unfold unorderedTotalColour
  simp only [dif_pos hp.2]
  congr 1
  exact Subtype.ext hp.1

/-- On an inserted single-exterior subset, the total colour is
exactly the corresponding exterior type. -/
theorem unorderedTotalColour_on_exterior
    {S E κ : Type} [Zero κ] {t : ℕ}
    (base : RSubsets S (t + 1) → κ)
    (exterior : E → RSubsets S t → κ)
    (core : RSubsets S t) (i : E) :
    unorderedTotalColour base exterior (unorderedInsertExterior core i) =
      exterior i core := by
  classical
  have hp := unorderedInsertExterior_parts core i
  have hne : (unorderedInsertExterior core i).val.toRight ≠
      (∅ : Finset E) := by
    rw [hp.2]
    simp
  have hsingle : ∃ j : E,
      (unorderedInsertExterior core i).val.toRight = {j} :=
    ⟨i, hp.2⟩
  unfold unorderedTotalColour
  simp only [dif_neg hne, dif_pos hsingle]
  have hchosen : Classical.choose hsingle = i := by
    have hmem : i ∈ (unorderedInsertExterior core i).val.toRight := by
      rw [hp.2]
      simp
    rw [Classical.choose_spec hsingle] at hmem
    exact (Finset.mem_singleton.mp hmem).symm
  rw [hchosen]
  congr 1
  exact Subtype.ext hp.1

end EPPAReducts.BoundedEquivalence
