import EPPAReducts.BoundedEquivalence.CosetOrbitBound
import Mathlib.Tactic.Omega

/-!
# The coset obstruction for one more fixed point than the bound

The quantitative coset-orbit lemma says at most b pairwise
orbit-inequivalent points can be fixed somewhere in a normalizer
coset. In an EPPA obstruction we have b+1 *distinct* exterior
vertices, individually fixed by possibly different coset members.
Consequently two of these vertices are carried to one another by
an element of the subgroup. This is the exact pigeonhole step.
-/

namespace EPPAReducts.BoundedEquivalence

universe u

/-- Given b+1 distinct vertices, each fixed by a member of the
normalizer coset Lg, two different vertices lie in the same L-orbit
whenever every member of that coset has at most b fixed points.

This theorem imposes no structure-specific conditions on the vertices
other than distinctness. It can therefore be used identically for
unordered subsets and ordered injective tuples. -/
theorem coset_fixed_vertices_orbit_collision
    {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    (L : Subgroup (Equiv.Perm Ω))
    (g : Equiv.Perm Ω)
    (hg : g ∈ Subgroup.normalizer L)
    (b : ℕ)
    (hcap : ∀ l : L,
      (Finset.univ.filter (fun x : Ω => l.val (g x) = x)).card ≤ b)
    (a : Fin (b + 1) ↪ Ω)
    (hfixed : ∀ i : Fin (b + 1),
      ∃ l : L, l.val (g (a i)) = a i) :
    ∃ i j : Fin (b + 1), i ≠ j ∧
      ∃ l : L, l.val (a i) = a j := by
  classical
  by_contra hnone
  let R : Finset Ω := (Finset.univ : Finset (Fin (b + 1))).image a
  have hcard : R.card = b + 1 := by
    simpa only [R, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_of_injective
        (Finset.univ : Finset (Fin (b + 1))) a.injective)
  have hsep : ∀ x y : Ω, x ∈ R → y ∈ R →
      (∃ l : L, l.val x = y) → x = y := by
    intro x y hx hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    have hij : i = j := by
      by_contra hne
      exact hnone ⟨i, j, hne, hxy⟩
    exact congrArg a hij
  have hfixR : ∀ x : Ω, x ∈ R →
      ∃ l : L, l.val (g x) = x := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hfixed i
  have hbound : R.card ≤ b :=
    coset_fixable_orbit_representatives_card_le
      L g hg b hcap R hsep hfixR
  omega

end EPPAReducts.BoundedEquivalence
