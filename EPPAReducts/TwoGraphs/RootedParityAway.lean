import EPPAReducts.TwoGraphs.TwoGraphFourPointXor

/-!
# Rooted two-graph reconstruction away from the distinguished vertex

The exact four-point XOR identity forces the indicator of a triple
disjoint from a chosen root to be the XOR of the three rooted triples.
This is the essential nondegenerate case of the rooted graph
representative.  Degenerate triples and those containing the root are
handled in the next bridge.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- A triple of distinct vertices, all different from the root, is
determined by the three edges of the rooted representative.
In particular, this is not an extra assumption on the two-graph. -/
theorem twoGraph_rootedParity_away
    {V : Type} (A : TwoGraph V)
    (o x y z : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hoz : o ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    A.isTriple (triple x y z) =
      Bool.xor
        (Bool.xor (A.isTriple (triple o x y))
          (A.isTriple (triple o y z)))
        (A.isTriple (triple o z x)) := by
  classical
  have h := twoGraph_fourPointXor A o x y z hox hoy hoz hxy hxz hyz
  rw [triple_swap_last o x z] at h
  cases h₁ : A.isTriple (triple o x y) <;>
    cases h₂ : A.isTriple (triple o y z) <;>
    cases h₃ : A.isTriple (triple o z x) <;>
    cases h₄ : A.isTriple (triple x y z) <;>
    simp_all [Bool.xor]

end EPPAReducts.TwoGraphs
