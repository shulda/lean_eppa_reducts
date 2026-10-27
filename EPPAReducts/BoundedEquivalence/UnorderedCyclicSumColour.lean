import EPPAReducts.BoundedEquivalence.UnorderedWitnessAPI
import EPPAReducts.BoundedEquivalence.OrderedColourTranslationFixed
import Mathlib.Data.ZMod.Basic

/-!
# A constructive alternative to choosing cyclic-subset orbit representatives

When the modulus is m*t, translation by t increments the quotient
of the canonical residue by t, modulo m. This arithmetic lemma is
a first step toward an explicit equivariant colouring of unordered
t-subsets via their sum, avoiding abstract orbit selectors.
-/

namespace EPPAReducts.BoundedEquivalence

/-- The quotient of a canonical residue by t is a ZMod m colour.
Translation by t shifts that colour by exactly one. -/
theorem zmod_quotient_colour_shift
    (m t : ℕ) (hm : 2 ≤ m) (ht : 0 < t)
    (z : ZMod (m * t)) :
    ((z + (t : ZMod (m * t))).val / t : ZMod m) =
      (z.val / t : ZMod m) + 1 := by
  have hmpos : 0 < m := by omega
  letI : NeZero (m * t) := ⟨Nat.ne_of_gt (Nat.mul_pos hmpos ht)⟩
  have hlt : t < m * t := by
    simpa only [one_mul] using
      (Nat.mul_lt_mul_of_pos_right (by omega : 1 < m) ht)
  have hcast : (t : ZMod (m * t)).val = t :=
    ZMod.val_natCast_of_lt hlt
  have hmod :
      ((z.val + t) % (m * t)) / t =
        ((z.val + t) / t) % m := by
    simpa only [Nat.mul_comm m t] using
      (Nat.mod_mul_right_div_self (z.val + t) t m)
  calc
    ((z + (t : ZMod (m * t))).val / t : ZMod m) =
        (((z.val + t) % (m * t)) / t : ZMod m) := by
      rw [ZMod.val_add, hcast]
    _ = (((z.val + t) / t) % m : ZMod m) := by rw [hmod]
    _ = ((z.val / t + 1) % m : ZMod m) := by
      rw [Nat.add_div_right _ ht]
    _ = (z.val / t : ZMod m) + 1 := by simp

/-- The sum of the elements of an unordered subset, computed in
the ambient cyclic additive group. -/
def unorderedSubsetSum {N t : ℕ} (s : RSubsets (ZMod N) t) : ZMod N :=
  s.val.sum id

/-- A unit translation of every vertex adds precisely the
cardinality of the subset to its cyclic sum. -/
theorem unorderedSubsetSum_translate_one
    (N t : ℕ) (s : RSubsets (ZMod N) t) :
    unorderedSubsetSum
        (permuteRSubset (orderedColourTranslationPerm (1 : ZMod N)) s) =
      unorderedSubsetSum s + (t : ZMod N) := by
  simp [unorderedSubsetSum, permuteRSubset,
    orderedColourTranslationPerm, Finset.sum_map,
    Finset.sum_add_distrib, s.property]

end EPPAReducts.BoundedEquivalence
