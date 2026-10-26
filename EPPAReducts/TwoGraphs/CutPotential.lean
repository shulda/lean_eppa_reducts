import Mathlib.Data.Bool.Basic

/-!
# A triangle cocycle on a complete simplex is a Boolean cut

This abstract algebraic lemma is the cut-potential step in the
transversal extension proof. It does not assume finiteness and works
also on singleton and two-point domains.

The hypothesis includes all ordered triples; the later application
will obtain repeated-point cases from the diagonal and symmetry of
the valuation discrepancy.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {D : Type u}

/-- The Boolean triangle sum (XOR) vanishes. -/
def IsBooleanTriangleCocycle (δ : D → D → Bool) : Prop :=
  ∀ x y z, Bool.xor (Bool.xor (δ x y) (δ x z)) (δ y z) = false

/-- Every complete-graph Boolean triangle cocycle on a nonempty domain
is a cut, with potential obtained by selecting a root. -/
theorem exists_cutPotential [Nonempty D]
    (δ : D → D → Bool)
    (htri : IsBooleanTriangleCocycle δ) :
    ∃ c : D → Bool, ∀ x y, δ x y = Bool.xor (c x) (c y) := by
  classical
  obtain ⟨root⟩ := ‹Nonempty D›
  refine ⟨(fun x => δ root x), ?_⟩
  intro x y
  have h := htri root x y
  change Bool.xor (Bool.xor (δ root x) (δ root y)) (δ x y) = false at h
  cases hx : δ root x <;> cases hy : δ root y <;>
    cases hxy : δ x y <;> simp_all

/-- A Boolean cut always satisfies the triangle equation. -/
theorem cut_isBooleanTriangleCocycle
    (c : D → Bool) :
    IsBooleanTriangleCocycle
      (fun x y => Bool.xor (c x) (c y)) := by
  intro x y z
  cases hx : c x <;> cases hy : c y <;>
    cases hz : c z <;> decide

/-- On nonempty domains, the triangle cocycle equation is exactly
existence of a cut potential. -/
theorem isBooleanTriangleCocycle_iff_cut [Nonempty D]
    (δ : D → D → Bool) :
    IsBooleanTriangleCocycle δ ↔
      ∃ c : D → Bool, ∀ x y, δ x y = Bool.xor (c x) (c y) := by
  constructor
  · exact exists_cutPotential δ
  · rintro ⟨c, hc⟩
    have heq : δ = fun x y => Bool.xor (c x) (c y) := by
      funext x y
      exact hc x y
    rw [heq]
    exact cut_isBooleanTriangleCocycle c

end EPPAReducts.TwoGraphs
