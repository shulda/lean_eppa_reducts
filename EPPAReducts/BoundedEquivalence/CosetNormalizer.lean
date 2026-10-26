import EPPAReducts.BoundedEquivalence.TwistedTransporter
import Mathlib.GroupTheory.Perm.Basic

/-!
# Normalizers and the orbitwise coset fixed-point condition

For a subgroup of the full permutation group, an element of its
normalizer intertwines the subgroup action with itself. Consequently,
whether a point can be fixed by *some* element of the corresponding
normalizer coset is constant on each subgroup orbit.

This is the structural prerequisite for the exact coset-orbit
counting bound, which will be formalized separately.
-/

namespace EPPAReducts.BoundedEquivalence

universe u

/-- Conjugating a member of a permutation subgroup by a normalizer
element gives another member of the same subgroup, in a form that
expressly intertwines the actions on individual vertices. -/
theorem normalizer_intertwines_permutations
    {Ω : Type u} (L : Subgroup (Equiv.Perm Ω))
    (g : Equiv.Perm Ω)
    (hg : g ∈ Subgroup.normalizer L)
    (l : L) :
    ∃ k : L, ∀ x : Ω, g (l.val x) = k.val (g x) := by
  let k : Equiv.Perm Ω := g * l.val * g⁻¹
  have hk : k ∈ L :=
    ((Subgroup.mem_normalizer_iff.mp hg) l.val).mp l.property
  refine ⟨⟨k, hk⟩, ?_⟩
  intro x
  change g (l.val x) = (g * l.val * g⁻¹) (g x)
  simp [Equiv.Perm.mul_apply]

/-- The normalizer carries pairs belonging to one subgroup orbit
to pairs belonging to another subgroup orbit. -/
theorem normalizer_maps_subgroup_orbits
    {Ω : Type u} (L : Subgroup (Equiv.Perm Ω))
    (g : Equiv.Perm Ω)
    (hg : g ∈ Subgroup.normalizer L)
    (x y : Ω)
    (hxy : ∃ l : L, l.val x = y) :
    ∃ k : L, k.val (g x) = g y := by
  obtain ⟨l, hl⟩ := hxy
  obtain ⟨k, hk⟩ :=
    normalizer_intertwines_permutations L g hg l
  refine ⟨k, ?_⟩
  exact (hk x).symm.trans (congrArg g hl)

/-- If one point in an orbit can be fixed by a member of `L*g`,
then every point in that orbit can be fixed by some member of the
*same coset*. The coset element is allowed to depend on the point. -/
theorem coset_fixability_orbit_invariant
    {Ω : Type u} (L : Subgroup (Equiv.Perm Ω))
    (g : Equiv.Perm Ω)
    (hg : g ∈ Subgroup.normalizer L)
    (x y : Ω)
    (hxy : ∃ a : L, a.val x = y)
    (hx : ∃ l : L, l.val (g x) = x) :
    ∃ k : L, k.val (g y) = y := by
  obtain ⟨a, ha⟩ := hxy
  obtain ⟨l, hl⟩ := hx
  obtain ⟨b, hb⟩ :=
    normalizer_intertwines_permutations L g hg a
  refine ⟨a * l * b⁻¹, ?_⟩
  have hby : g y = b.val (g x) := by
    calc
      g y = g (a.val x) := congrArg g ha.symm
      _ = b.val (g x) := hb x
  change (a.val * l.val * b.val⁻¹) (g y) = y
  simp only [Equiv.Perm.mul_apply]
  rw [hby]
  simp [hl, ha]

end EPPAReducts.BoundedEquivalence
