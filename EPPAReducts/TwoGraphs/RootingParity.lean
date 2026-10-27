import EPPAReducts.TwoGraphs.RawFourPointParity

/-!
# Pair-to-triple parity: algebraic part of the rooting reduction

An edge colouring over F₂ defines a ternary cocycle by summing the
three pair colours. Every four vertices have even total triple colour.
This is the algebraic fact behind the reduction from unlabelled pair
equivalences to two-graphs modulo global complementation.
-/

namespace EPPAReducts.TwoGraphs

/-- Pair-to-triple parity, before passing to unordered subsets. -/
def triangleOfPairs {V : Type} (c : V → V → ZMod 2)
    (x y z : V) : ZMod 2 :=
  c x y + c x z + c y z

/-- The four triples on a quadruple have total parity zero. -/
theorem triangleOfPairs_fourPoint {V : Type}
    (c : V → V → ZMod 2) (a b d e : V) :
    triangleOfPairs c a b d +
      triangleOfPairs c a b e +
      triangleOfPairs c a d e +
      triangleOfPairs c b d e = 0 := by
  dsimp [triangleOfPairs]
  have htwo : (2 : ZMod 2) = 0 := by decide
  ring_nf
  simp [htwo]

/-- Symmetric pair colours give a symmetric triangle colour. -/
theorem triangleOfPairs_swap {V : Type}
    (c : V → V → ZMod 2)
    (h : ∀ x y, c x y = c y x) (x y z : V) :
    triangleOfPairs c x y z = triangleOfPairs c y x z := by
  simp only [triangleOfPairs, ← h x y]
  ring

/-- An isolated root adjoined to an old pair colouring. -/
def isolatedRootEdge {V : Type} (c : V → V → ZMod 2) :
    Option V → Option V → ZMod 2
  | some x, some y => c x y
  | _, _ => 0

/-- Rooted triples are the original old pair colours. -/
@[simp] theorem triangleOfPairs_root {V : Type}
    (c : V → V → ZMod 2) (x y : V) :
    triangleOfPairs (isolatedRootEdge c) none (some x) (some y) =
      c x y := by
  simp [triangleOfPairs, isolatedRootEdge]

/-- On old vertices the resulting triple is the parity of the
three old edges. -/
@[simp] theorem triangleOfPairs_old {V : Type}
    (c : V → V → ZMod 2) (x y z : V) :
    triangleOfPairs (isolatedRootEdge c) (some x) (some y) (some z) =
      c x y + c x z + c y z := rfl

end EPPAReducts.TwoGraphs
