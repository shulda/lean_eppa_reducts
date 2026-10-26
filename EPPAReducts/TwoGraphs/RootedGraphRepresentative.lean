import EPPAReducts.TwoGraphs.RootedParityAll

/-!
# The rooted Mathlib SimpleGraph represents any two-graph

This file identifies the actual adjacency relation in the previously
constructed rooted SimpleGraph with the two-graph's root triples and
proves that odd-triangle parity recovers the input two-graph on every
genuine unordered three-element set.

No existence of a graph representative is postulated.  It is the
already defined rootedGraph, on the very same carrier V.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- For distinct endpoints, the root triples are precisely the
edges of the rooted representative, even when an endpoint is the
root (when the triple is necessarily false). -/
theorem rootedGraph_adj_iff_triple
    {V : Type} (A : TwoGraph V) (o x y : V)
    (hxy : x ≠ y) :
    (rootedGraph A o).Adj x y ↔
      A.isTriple (triple o x y) = true := by
  constructor
  · intro h
    exact h.2.2.2
  · intro ht
    have hxo : x ≠ o := by
      intro hx
      subst x
      have hf := twoGraph_triple_false_of_repeat A o o y (Or.inl rfl)
      rw [hf] at ht
      cases ht
    have hyo : y ≠ o := by
      intro hy
      subst y
      have hf := twoGraph_triple_false_of_repeat A o x o
        (Or.inr (Or.inl rfl))
      rw [hf] at ht
      cases ht
    exact (rootedGraph_adj_iff A o x y).mpr
      ⟨hxy, hxo, hyo, ht⟩

/-- A fixed classical Boolean indicator of a graph edge.
Using a noncomputable definition avoids an implicit decidability
assumption on arbitrary SimpleGraph adjacency. -/
noncomputable def graphEdgeBit {V : Type} (G : SimpleGraph V)
    (x y : V) : Bool := by
  classical
  exact decide (G.Adj x y)

/-- The indicator of adjacency in the rooted SimpleGraph equals
the indicator of the corresponding root triple for distinct endpoints. -/
theorem rootedGraph_edgeBit_eq_rootTriple
    {V : Type} (A : TwoGraph V) (o x y : V)
    (hxy : x ≠ y) :
    graphEdgeBit (rootedGraph A o) x y =
      A.isTriple (triple o x y) := by
  classical
  unfold graphEdgeBit
  cases ht : A.isTriple (triple o x y) with
  | false =>
    have hn : ¬ (rootedGraph A o).Adj x y := by
      intro h
      have htrue := (rootedGraph_adj_iff_triple A o x y hxy).mp h
      rw [ht] at htrue
      cases htrue
    simp [hn, ht]
  | true =>
    have hp : (rootedGraph A o).Adj x y :=
      (rootedGraph_adj_iff_triple A o x y hxy).mpr ht
    simp [hp, ht]

/-- The Boolean odd-edge predicate of a triangle in a SimpleGraph. -/
noncomputable def graphOddTriple {V : Type} (G : SimpleGraph V)
    (x y z : V) : Bool :=
  Bool.xor
    (Bool.xor (graphEdgeBit G x y) (graphEdgeBit G y z))
    (graphEdgeBit G z x)

/-- The rooted graph G_o recovers the literal input two-graph on all
three-element subsets: its triangle has an odd number of edges iff
the input triple is distinguished. This holds on the same vertex set,
with no nonempty or cardinality hypothesis. -/
theorem rootedGraph_represents_twoGraph
    {V : Type} (A : TwoGraph V) (o x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    A.isTriple (triple x y z) =
      graphOddTriple (rootedGraph A o) x y z := by
  classical
  change A.isTriple (triple x y z) =
    Bool.xor
      (Bool.xor
        (graphEdgeBit (rootedGraph A o) x y)
        (graphEdgeBit (rootedGraph A o) y z))
      (graphEdgeBit (rootedGraph A o) z x)
  rw [rootedGraph_edgeBit_eq_rootTriple A o x y hxy,
    rootedGraph_edgeBit_eq_rootTriple A o y z hyz,
    rootedGraph_edgeBit_eq_rootTriple A o z x hxz.symm]
  exact twoGraph_rootedParity_distinct A o x y z hxy hxz hyz

end EPPAReducts.TwoGraphs
