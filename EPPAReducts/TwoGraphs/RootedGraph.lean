import EPPAReducts.HumanTargets
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The graph representative rooted at a vertex

This module builds an actual mathlib SimpleGraph from the author's
unmodified human-readable TwoGraph specification. Its defining edges
encode precisely the triples containing the chosen root.

The substantive four-point parity ⇒ reconstruction of all triples
is the next bridge lemma, not a premise built into this definition.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- A triple is unchanged when the last two vertices are exchanged. -/
theorem triple_swap_last {V : Type} (o x y : V) :
    triple o x y = triple o y x := by
  classical
  apply Finset.ext
  intro v
  simp only [triple, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- Rooted adjacency, with distinct endpoints and no edge at the root. -/
noncomputable def rootedAdj {V : Type}
    (A : TwoGraph V) (o x y : V) : Prop :=
  x ≠ y ∧ x ≠ o ∧ y ≠ o ∧ A.isTriple (triple o x y) = true

theorem rootedAdj_symm {V : Type}
    (A : TwoGraph V) (o x y : V) :
    rootedAdj A o x y → rootedAdj A o y x := by
  rintro ⟨hxy, hxo, hyo, ht⟩
  refine ⟨hxy.symm, hyo, hxo, ?_⟩
  simpa only [triple_swap_last] using ht

/-- Every two-graph has a canonical graph representative upon
choosing one root. Its edge relation is defined without choosing
any external graph or a switching-class representative. -/
noncomputable def rootedGraph {V : Type}
    (A : TwoGraph V) (o : V) : SimpleGraph V where
  Adj := rootedAdj A o
  symm := by
    intro x y h
    exact rootedAdj_symm A o x y h
  loopless := by
    intro x h
    exact h.1 rfl

theorem rootedGraph_adj_iff {V : Type}
    (A : TwoGraph V) (o x y : V) :
    (rootedGraph A o).Adj x y ↔
      x ≠ y ∧ x ≠ o ∧ y ≠ o ∧
        A.isTriple (triple o x y) = true :=
  Iff.rfl

/-- The distinguished root is isolated in the rooted representative. -/
theorem rootedGraph_root_isolated {V : Type}
    (A : TwoGraph V) (o x : V) :
    ¬ (rootedGraph A o).Adj o x := by
  intro h
  exact h.2.1 rfl

/-- Away from the root and diagonal, adjacency is exactly the triple
indicator of the original two-graph. -/
theorem rootedGraph_adj_iff_rootTriple {V : Type}
    (A : TwoGraph V) (o x y : V)
    (hxy : x ≠ y) (hxo : x ≠ o) (hyo : y ≠ o) :
    (rootedGraph A o).Adj x y ↔
      A.isTriple (triple o x y) = true := by
  simp [rootedGraph_adj_iff, hxy, hxo, hyo]

end EPPAReducts.TwoGraphs
