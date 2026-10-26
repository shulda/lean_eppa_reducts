import EPPAReducts.BoundedEquivalence.CosetNormalizer

/-!
# Exactly one group-sized fiber over each fixed coset orbit

The incidence pairs `(y,l)` with `y` in a fixed subgroup orbit
and `l * g` fixing `y` form a type equivalent to the subgroup
itself. The construction uses the transporter--stabilizer
equivalence and the canonical orbit--stabilizer equivalence.

This is the exact orbitwise counting identity needed before the
global finite coset-orbit bound.
-/

namespace EPPAReducts.BoundedEquivalence

universe u

/-- If the normalizer coset has a fixed point in the orbit of
`x`, then all incidence pairs over that orbit are in bijection
with the acting subgroup. No cardinality or choice of orbit
representatives is involved in the statement. -/
noncomputable def cosetOrbitIncidenceEquivGroup
    {Ω : Type u} (L : Subgroup (Equiv.Perm Ω))
    (g : Equiv.Perm Ω)
    (hg : g ∈ Subgroup.normalizer L)
    (x : Ω)
    (hx : ∃ l : L, l.val (g x) = x) :
    (Σ y : MulAction.orbit L x,
      {l : L // l.val (g y.val) = y.val}) ≃ L := by
  classical
  have eFiber (y : MulAction.orbit L x) :
      {l : L // l.val (g y.val) = y.val} ≃
        MulAction.stabilizer L x := by
    have hxy : ∃ a : L, a.val x = y.val := by
      obtain ⟨a, ha⟩ := y.property
      refine ⟨a, ?_⟩
      change a.val x = y.val at ha
      exact ha
    obtain ⟨a, ha⟩ :=
      coset_fixability_orbit_invariant L g hg x y.val hxy hx
    have ha' : a • (g y.val) = y.val := by
      change a.val (g y.val) = y.val
      exact ha
    have hyorbit : g y.val ∈ MulAction.orbit L y.val :=
      (exists_transporter_iff_mem_orbit y.val (g y.val)).mp ⟨a, ha'⟩
    obtain ⟨u, hu⟩ := hyorbit
    have eLocal :
        {l : L // l.val (g y.val) = y.val} ≃
          MulAction.stabilizer L y.val := by
      change {l : L // l • (g y.val) = y.val} ≃
        MulAction.stabilizer L y.val
      rw [← hu]
      exact twistedTransporterEquivStabilizer u y.val
    exact eLocal.trans
      (MulAction.stabilizerEquivStabilizerOfOrbitRel y.property).symm.toEquiv
  exact (Equiv.sigmaCongrRight eFiber).trans
    ((Equiv.sigmaEquivProd _ _).trans
      (MulAction.orbitProdStabilizerEquivGroup L x))

end EPPAReducts.BoundedEquivalence
