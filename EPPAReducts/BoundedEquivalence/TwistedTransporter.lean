import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Fibers of a twisted group-action fixed-point equation

An elementary transporter--stabilizer bijection. It is the local
counting input for the normalizer-coset orbit bound used in the
negative EPPA construction.
-/

namespace EPPAReducts.BoundedEquivalence

universe u v
variable {G : Type u} {X : Type v} [Group G] [MulAction G X]

/-- Transporters from `u • x` to `x` are in bijection with
the stabilizer of `x`. This is an actual equivalence of types,
not only a numerical orbit-stabilizer formula. -/
noncomputable def twistedTransporterEquivStabilizer (u : G) (x : X) :
    {h : G // h • (u • x) = x} ≃ MulAction.stabilizer G x where
  toFun h := ⟨h.val * u, by
    change (h.val * u) • x = x
    simpa only [mul_smul] using h.property⟩
  invFun k := ⟨k.val * u⁻¹, by
    change (k.val * u⁻¹) • (u • x) = x
    simpa only [mul_smul, inv_smul_smul] using k.property⟩
  left_inv h := by
    apply Subtype.ext
    change (h.val * u) * u⁻¹ = h.val
    simp only [mul_assoc, mul_inv_cancel_right]
  right_inv k := by
    apply Subtype.ext
    change (k.val * u⁻¹) * u = k.val
    simp only [mul_assoc, inv_mul_cancel_right]

/-- In particular, for a finite group the transporter fiber has
exactly the cardinality of the stabilizer. -/
theorem card_twistedTransporters [Fintype G] (u : G) (x : X) :
    Fintype.card {h : G // h • (u • x) = x} =
      Fintype.card (MulAction.stabilizer G x) := by
  classical
  exact Fintype.card_congr (twistedTransporterEquivStabilizer u x)

/-- An equation `h • y = x` is solvable precisely when `y`
belongs to the orbit of `x`. -/
theorem exists_transporter_iff_mem_orbit (x y : X) :
    (∃ h : G, h • y = x) ↔ y ∈ MulAction.orbit G x := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h⁻¹, ?_⟩
    rw [← hh, inv_smul_smul]
  · rintro ⟨u, hu⟩
    refine ⟨u⁻¹, ?_⟩
    rw [← hu, inv_smul_smul]

end EPPAReducts.BoundedEquivalence
