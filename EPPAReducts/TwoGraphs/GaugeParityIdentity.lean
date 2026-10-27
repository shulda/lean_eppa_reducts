import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Gauge-corrected uniform edge shifts on triangle parity

The sum of three pair colours in characteristic two transforms
by a single global delta under a uniform edge shift combined
with an arbitrary vertex gauge. The vertex gauge disappears:
each of the three vertices occurs twice among the three edges.

This algebraic lemma is independent of rooted Option carriers,
unlabelled-class presentations and the EPPA witness construction.
-/

namespace EPPAReducts.TwoGraphs

variable {U : Type}

/-- The unoriented sum of three pair colours (algebraically). -/
def pairTriangleSum (c : U → U → ZMod 2) (a b d : U) : ZMod 2 :=
  c a b + c a d + c b d

/-- If a pair colouring changes by a uniform `delta` and by a
vertex-dependent gauge `f(u)+f(v)`, then every triple colour
changes by precisely `delta`. -/
theorem pairTriangleSum_gaugeShift
    (c c' : U → U → ZMod 2) (δ : ZMod 2) (f : U → ZMod 2)
    (h : ∀ x y : U, x ≠ y →
      c' x y = c x y + δ + f x + f y)
    (a b d : U) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    pairTriangleSum c' a b d = pairTriangleSum c a b d + δ := by
  dsimp [pairTriangleSum]
  rw [h a b hab, h a d had, h b d hbd]
  have htwo : (2 : ZMod 2) = 0 := by decide
  ring_nf
  simp [htwo]

end EPPAReducts.TwoGraphs
