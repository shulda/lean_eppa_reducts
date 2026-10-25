import Mathlib.Tactic.Abel

/-!
# Rooting a triangle cocycle

The algebraic backbone of the rooted-graph representation of a two-graph.
For any additive abelian coefficient group, the four-point cocycle
condition implies that the triangle cochain is a coboundary of its
restriction at any chosen vertex. The two-graph specialization will
take the coefficient group to be F₂.
-/

namespace EPPAReducts.TwoGraphs

universe u v
variable {V : Type u} {A : Type v} [AddCommGroup A]

/-- The triangle coboundary of an (oriented) edge cochain. -/
def triangleBoundary (edge : V → V → A) (x y z : V) : A :=
  edge y z - edge x z + edge x y

/-- The four-point cocycle equation on a complete simplex. -/
def IsTriangleCocycle (t : V → V → V → A) : Prop :=
  ∀ w x y z, t x y z - t w y z + t w x z - t w x y = 0

/-- The coboundary of an edge cochain satisfies the four-point equation. -/
theorem triangleBoundary_isCocycle (edge : V → V → A) :
    IsTriangleCocycle (triangleBoundary edge) := by
  intro w x y z
  dsimp [triangleBoundary]
  abel

/-- A cocycle on a complete simplex is the coboundary of its restriction
at any fixed root vertex. -/
theorem cocycle_eq_rooted_boundary (t : V → V → V → A)
    (h : IsTriangleCocycle t) (root : V) :
    t = triangleBoundary (fun x y => t root x y) := by
  funext x y z
  apply sub_eq_zero.mp
  change t x y z - (t root y z - t root x z + t root x y) = 0
  convert h root x y z using 1 <;> abel

/-- On a nonempty complete simplex, being a cocycle is equivalent to
being a triangle boundary. -/
theorem isCocycle_iff_exists_boundary [Nonempty V]
    (t : V → V → V → A) :
    IsTriangleCocycle t ↔
      ∃ edge : V → V → A, t = triangleBoundary edge := by
  constructor
  · intro h
    obtain ⟨root⟩ := ‹Nonempty V›
    exact ⟨fun x y => t root x y, cocycle_eq_rooted_boundary t h root⟩
  · rintro ⟨edge, rfl⟩
    exact triangleBoundary_isCocycle edge

end EPPAReducts.TwoGraphs
