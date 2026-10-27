import EPPAReducts.BoundedEquivalence.UnorderedAllExteriorTypes
import EPPAReducts.BoundedEquivalence.UnorderedResidueSurjectivity

/-!
# All r equivariant exterior types on the common cyclic core

The core of size N=m*r*(r-1) supports surjective equivariant
colourings of r-subsets and (r-1)-subsets, as well as an injective
family of r distinct equivariant exterior (r-1)-subset types.
The case r=2 is included by the base type and its sole residue indicator.
-/

namespace EPPAReducts.BoundedEquivalence

theorem unorderedCommonCore_dvd_pred (m r : ℕ) :
    r - 1 ∣ unorderedCommonCoreSize m r := by
  refine ⟨m * r, ?_⟩
  simp [unorderedCommonCoreSize, mul_comm, mul_left_comm, mul_assoc]

theorem unorderedCommonCore_bound_pred
    (m r : ℕ) (hm : 2 ≤ m) (hr : 2 ≤ r) :
    2 * (r - 1) ≤ unorderedCommonCoreSize m r := by
  have hmr : 2 ≤ m * r := by
    calc
      2 ≤ m := hm
      _ = m * 1 := by simp
      _ ≤ m * r := Nat.mul_le_mul_left m (by omega)
  exact Nat.mul_le_mul_right (r - 1) hmr

theorem unorderedCommonCore_residue_surjective
    (m r : ℕ) (hm : 2 ≤ m) (hr : 2 ≤ r) :
    Function.Surjective
      (unorderedSubsetResidue (unorderedCommonCore_dvd_pred m r)) :=
  unorderedSubsetResidue_surjective
    (unorderedCommonCoreSize m r) (r - 1) (by omega)
    (unorderedCommonCore_bound_pred m r hm hr)
    (unorderedCommonCore_dvd_pred m r)

/-- The explicit family of r exterior types on the same core. -/
def unorderedCommonCoreExteriorTypes
    (m r : ℕ) :
    Fin ((r - 1) + 1) →
      (RSubsets (ZMod (unorderedCommonCoreSize m r)) (r - 1) → ZMod m) :=
  unorderedAllExteriorTypes
    (unorderedCommonCore_dvd_pred m r)
    (unorderedCyclicSumColour (unorderedCommonCoreSize_dvd_pred m r))

theorem unorderedCommonCoreExteriorTypes_injective
    (m r : ℕ) (hm : 2 ≤ m) (hr : 2 ≤ r) :
    Function.Injective (unorderedCommonCoreExteriorTypes m r) :=
  unorderedAllExteriorTypes_injective
    (unorderedCommonCoreSize m r) (r - 1) m hm
    (unorderedCommonCore_dvd_pred m r)
    (unorderedCyclicSumColour (unorderedCommonCoreSize_dvd_pred m r))
    (unorderedCommonCore_residue_surjective m r hm hr)

theorem unorderedCommonCoreExteriorTypes_translate_one
    (m r : ℕ) (hm : 2 ≤ m) (hr : 2 ≤ r)
    (i : Fin ((r - 1) + 1))
    (s : RSubsets (ZMod (unorderedCommonCoreSize m r)) (r - 1)) :
    unorderedCommonCoreExteriorTypes m r i
        (permuteRSubset
          (orderedColourTranslationPerm (1 : ZMod (unorderedCommonCoreSize m r))) s) =
      unorderedCommonCoreExteriorTypes m r i s + 1 := by
  exact unorderedAllExteriorTypes_translate_one
    (unorderedCommonCoreSize m r) (r - 1) m
    (unorderedCommonCore_dvd_pred m r)
    (unorderedCyclicSumColour (unorderedCommonCoreSize_dvd_pred m r))
    (unorderedCyclicSumColour_translate_one
      (unorderedCommonCoreSize m r) m (r - 1)
      hm (by omega) (unorderedCommonCoreSize_dvd_pred m r))
    i s

/-- The same injective family, indexed by Fin r. -/
theorem unorderedCommonCoreExteriorTypes_fin_r_injective
    (m r : ℕ) (hm : 2 ≤ m) (hr : 2 ≤ r) :
    Function.Injective
      (fun i : Fin r =>
        unorderedCommonCoreExteriorTypes m r
          (Fin.cast (by omega : r = (r - 1) + 1) i)) := by
  intro i j h
  have hh := unorderedCommonCoreExteriorTypes_injective m r hm hr h
  apply Fin.ext
  exact congrArg Fin.val hh

end EPPAReducts.BoundedEquivalence
