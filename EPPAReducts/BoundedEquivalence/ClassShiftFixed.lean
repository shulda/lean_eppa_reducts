import EPPAReducts.BoundedEquivalence.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Finset.Card

/-!
# A fixed-point-free permutation of equivalence classes forces few fixed vertices

This is the finite combinatorial implication needed in the coset-obstruction
argument. The auxiliary labels are not part of the structural language:
an automorphism is allowed to permute them. If its induced permutation
of labels has no fixed points, it cannot fix an entire r-subset.
-/

namespace EPPAReducts.BoundedEquivalence

universe u v
variable {α : Type u} {κ : Type v} {r : ℕ}

/-- Transport an unordered r-subset through a vertex permutation. -/
def permuteRSubset (g : Equiv.Perm α) (s : RSubsets α r) : RSubsets α r :=
  ⟨s.val.map ⟨g, g.injective⟩, by simpa using s.property⟩

/-- Any r-subset whose vertices are all fixed is itself fixed. -/
theorem permuteRSubset_eq_of_fixed
    (g : Equiv.Perm α) (s : RSubsets α r)
    (hfix : ∀ x ∈ s.val, g x = x) :
    permuteRSubset g s = s := by
  apply Subtype.ext
  ext x
  change x ∈ s.val.map (⟨g, g.injective⟩ : α ↪ α) ↔ x ∈ s.val
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx
    have heq : y = x := by
      simpa [hfix y hy] using hxy
    exact heq ▸ hy
  · intro hx
    apply Finset.mem_map.mpr
    exact ⟨x, hx, hfix x hx⟩

/-- If a vertex permutation shifts every auxiliary class name by a
fixed-point-free permutation, it cannot fix all vertices of an r-subset. -/
theorem no_fixed_rSubset_of_class_shift
    (labels : RSubsets α r → κ)
    (g : Equiv.Perm α) (shift : Equiv.Perm κ)
    (hshift : ∀ c : κ, shift c ≠ c)
    (hcompat : ∀ s, labels (permuteRSubset g s) = shift (labels s))
    (s : RSubsets α r) :
    ¬ (∀ x ∈ s.val, g x = x) := by
  intro hfix
  have heq : permuteRSubset g s = s :=
    permuteRSubset_eq_of_fixed g s hfix
  have hc : labels s = shift (labels s) := by
    simpa only [heq] using hcompat s
  exact hshift (labels s) hc.symm

end EPPAReducts.BoundedEquivalence
