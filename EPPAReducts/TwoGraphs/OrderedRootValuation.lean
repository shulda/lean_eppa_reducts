import EPPAReducts.TwoGraphs.RootedGraphRepresentative
import EPPAReducts.TwoGraphs.RawTripleParity

/-!
# Oriented rooted graph edges as valuation coordinates

On any linearly ordered carrier V, assign each rooted edge {x,y}
to its smaller endpoint.  The resulting valuation χ_x(y) has the
property χ_x(y) XOR χ_y(x) = the rooted edge bit.  Combining
this with the certified rooted parity lemma proves that raw
valuation parity reconstructs every distinguished triple with
distinct vertices.

The order is auxiliary and will later be chosen on any finite V.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- A directed-half representation of the rooted graph adjacency
of an arbitrary two-graph. -/
noncomputable def orderedRootValuation
    {V : Type} [LinearOrder V] (A : TwoGraph V) (o x : V) :
    Valuation V :=
  fun y => if x < y then A.isTriple (triple o x y) else false

/-- The sum of the two opposite valuation entries recovers the
rooted edge indicator, independently of the chosen vertex order. -/
theorem orderedRootValuation_pairXor
    {V : Type} [LinearOrder V] (A : TwoGraph V)
    (o x y : V) (hxy : x ≠ y) :
    Bool.xor ((orderedRootValuation A o x) y)
      ((orderedRootValuation A o y) x) =
      A.isTriple (triple o x y) := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have hn : ¬ y < x := not_lt.mpr (le_of_lt hlt)
    simp [orderedRootValuation, hlt, hn]
  · have hn : ¬ x < y := not_lt.mpr (le_of_lt hgt)
    have hs : A.isTriple (triple o y x) =
        A.isTriple (triple o x y) :=
      congrArg A.isTriple (triple_swap_last o y x)
    simpa [orderedRootValuation, hn, hgt] using hs

/-- Every triple of distinct vertices in the original two-graph
has exactly the parity induced by the corresponding ordered rooted
valuations. -/
theorem orderedRootValuation_rawTripleParity
    {V : Type} [LinearOrder V] (A : TwoGraph V)
    (o x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    rawTripleParity x y z
      (orderedRootValuation A o x)
      (orderedRootValuation A o y)
      (orderedRootValuation A o z) =
        A.isTriple (triple x y z) := by
  have hxyE := orderedRootValuation_pairXor A o x y hxy
  have hxzE := orderedRootValuation_pairXor A o x z hxz
  have hyzE := orderedRootValuation_pairXor A o y z hyz
  change Bool.xor
    (Bool.xor
      (Bool.xor ((orderedRootValuation A o x) y)
        ((orderedRootValuation A o y) x))
      (Bool.xor ((orderedRootValuation A o x) z)
        ((orderedRootValuation A o z) x)))
    (Bool.xor ((orderedRootValuation A o y) z)
      ((orderedRootValuation A o z) y)) =
    A.isTriple (triple x y z)
  rw [hxyE, hxzE, hyzE]
  have hp := twoGraph_rootedParity_distinct A o x y z hxy hxz hyz
  have hs : A.isTriple (triple o z x) =
      A.isTriple (triple o x z) :=
    congrArg A.isTriple (triple_swap_last o z x)
  rw [hs] at hp
  cases h₁ : A.isTriple (triple o x y) <;>
    cases h₂ : A.isTriple (triple o x z) <;>
    cases h₃ : A.isTriple (triple o y z) <;>
    simp_all [Bool.xor]

end EPPAReducts.TwoGraphs
