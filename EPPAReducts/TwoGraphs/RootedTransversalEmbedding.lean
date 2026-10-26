import EPPAReducts.TwoGraphs.OrderedRootValuation
import EPPAReducts.TwoGraphs.TransversalLiteralExtension

/-!
# Induced embedding of an arbitrary ordered two-graph into C_V

The canonical graph representative at a chosen root gives a family of
ordered valuations χ_x.  Sending x to (x, [χ_x]) is injective because
the first coordinate is x.

The previously certified raw parity formula covers triples of distinct
vertices.  Repeated vertices are handled by the independent onlyTriples
axiom and the actual valuation relation's duplicate-vertex lemmas.

The conclusion is the EXACT human-facing induced-embedding predicate,
not a raw or merely one-way ternary preservation condition.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- The original vertices embedded as a full valuation transversal. -/
noncomputable def orderedRootTransversalEmbedding
    {V : Type} [LinearOrder V] (A : TwoGraph V) (o : V) :
    V ↪ ValuationVertex V where
  toFun := fun x => (x, valuationClass (orderedRootValuation A o x))
  inj' := by
    intro x y h
    exact congrArg Prod.fst h

/-- Every two-graph on a linearly ordered type is induced in the
actual valuation two-graph C_V, for every choice of root. This
covers ALL triples, including repeats. -/
theorem orderedRootTransversalEmbedding_induced
    {V : Type} [LinearOrder V] [DecidableEq (ValuationVertex V)]
    (A : TwoGraph V) (o : V) :
    IsInducedTwoGraphEmbedding A (valuationTwoGraph V)
      (orderedRootTransversalEmbedding A o) := by
  intro x y z
  rw [valuationTwoGraph_triple_eq_vertexParity]
  change A.isTriple (triple x y z) =
    rawTripleParity x y z
      (orderedRootValuation A o x)
      (orderedRootValuation A o y)
      (orderedRootValuation A o z)
  by_cases hxy : x = y
  · subst y
    rw [twoGraph_triple_false_of_repeat A x x z (Or.inl rfl)]
    exact (rawTripleParity_duplicate_first x z
      (orderedRootValuation A o x)
      (orderedRootValuation A o z)).symm
  by_cases hxz : x = z
  · subst z
    rw [twoGraph_triple_false_of_repeat A x y x
      (Or.inr (Or.inl rfl))]
    calc
      false = rawTripleParity x x y
        (orderedRootValuation A o x)
        (orderedRootValuation A o x)
        (orderedRootValuation A o y) :=
          (rawTripleParity_duplicate_first x y
            (orderedRootValuation A o x)
            (orderedRootValuation A o y)).symm
      _ = rawTripleParity x y x
        (orderedRootValuation A o x)
        (orderedRootValuation A o y)
        (orderedRootValuation A o x) :=
          (rawTripleParity_swap_last_two x y x
            (orderedRootValuation A o x)
            (orderedRootValuation A o y)
            (orderedRootValuation A o x)).symm
  by_cases hyz : y = z
  · subst z
    rw [twoGraph_triple_false_of_repeat A x y y
      (Or.inr (Or.inr rfl))]
    have h :
        rawTripleParity x y y
          (orderedRootValuation A o x)
          (orderedRootValuation A o y)
          (orderedRootValuation A o y) =
        rawTripleParity y y x
          (orderedRootValuation A o y)
          (orderedRootValuation A o y)
          (orderedRootValuation A o x) := by
      calc
        rawTripleParity x y y
          (orderedRootValuation A o x)
          (orderedRootValuation A o y)
          (orderedRootValuation A o y) =
        rawTripleParity y x y
          (orderedRootValuation A o y)
          (orderedRootValuation A o x)
          (orderedRootValuation A o y) :=
            rawTripleParity_swap_first_two x y y
              (orderedRootValuation A o x)
              (orderedRootValuation A o y)
              (orderedRootValuation A o y)
        _ = rawTripleParity y y x
          (orderedRootValuation A o y)
          (orderedRootValuation A o y)
          (orderedRootValuation A o x) :=
            rawTripleParity_swap_last_two y x y
              (orderedRootValuation A o y)
              (orderedRootValuation A o x)
              (orderedRootValuation A o y)
    rw [h, rawTripleParity_duplicate_first]
  exact (orderedRootValuation_rawTripleParity A o x y z
    hxy hxz hyz).symm

end EPPAReducts.TwoGraphs
