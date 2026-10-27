import EPPAReducts.Classification.GraphSymmetrization

/-!
# Automorphisms of normalized binary graph witnesses

Every automorphism of a one-symbol binary-relational structure preserves
the symmetric, loopless part of the relation. This module upgrades
that observation to the literal typed automorphism API,
without quotienting permutations or introducing any new axioms.
-/

namespace EPPAReducts.Classification

open AllThoseEPPA
open AllThoseEPPA.Graph

/-- Total relational automorphisms preserve the edge predicate on
each ordered pair. -/
theorem binaryRelAut_edge_iff
    {W : Type}
    (B : Structure Graph.language W)
    (g : Structure.Automorphism Graph.action B)
    (x y : W) :
    B.rel Graph.RelSymbol.edge (![g x, g y] : Fin 2 → W) ↔
      B.rel Graph.RelSymbol.edge (![x, y] : Fin 2 → W) := by
  have hsrc :
      ∀ i : Fin 2, (![x, y] : Fin 2 → W) i ∈
        g.toPartialIsomorphism.source := by
    intro i
    rw [g.source_eq_univ]
    exact Set.mem_univ _
  have h := g.toPartialIsomorphism.map_rel_iff
    Graph.RelSymbol.edge (![x, y] : Fin 2 → W) hsrc
  have hlang : g.toPartialIsomorphism.lang = 1 :=
    Subsingleton.elim _ _
  have htuple :
      (g.toPartialIsomorphism.toPartialEquiv ∘
        (![x, y] : Fin 2 → W)) =
      (![g x, g y] : Fin 2 → W) := by
    funext i
    fin_cases i <;> rfl
  have hs : Graph.action.onRel g.toPartialIsomorphism.lang
      Graph.RelSymbol.edge = Graph.RelSymbol.edge := by
    simp [hlang, Graph.action, Language.Action.trivial,
      Language.Action.onRel] <;> rfl
  rw [hs, htuple] at h
  exact h

/-- An automorphism is injective on its full carrier, not only on
the partial-equiv source. -/
theorem binaryRelAut_injective
    {W : Type}
    (B : Structure Graph.language W)
    (g : Structure.Automorphism Graph.action B) :
    Function.Injective (fun x : W => g x) := by
  intro x y h
  apply g.toPartialIsomorphism.toPartialEquiv.injOn
  · change x ∈ g.toPartialIsomorphism.source
    rw [g.source_eq_univ]
    exact Set.mem_univ _
  · change y ∈ g.toPartialIsomorphism.source
    rw [g.source_eq_univ]
    exact Set.mem_univ _
  · exact h

/-- Every actual binary-relational automorphism induces an actual
automorphism of the canonically normalized simple-graph structure.
Its vertex action and language component are unchanged. -/
noncomputable def symmetrizedGraphAutomorphism
    {W : Type}
    (B : Structure Graph.language W)
    (g : Structure.Automorphism Graph.action B) :
    Structure.Automorphism Graph.action
      (Graph.toStructure (symmetrizedSimpleGraph B)) where
  toPartialIsomorphism := {
    lang := g.toPartialIsomorphism.lang
    toPartialEquiv := g.toPartialIsomorphism.toPartialEquiv
    source_closed := by
      intro n F xs hxs
      exact Empty.elim F
    target_closed := by
      intro n F xs hxs
      exact Empty.elim F
    map_rel_iff := by
      intro n R xs hxs
      cases R with
      | edge =>
        have hne :
            g (xs 0) ≠ g (xs 1) ↔ xs 0 ≠ xs 1 := by
          constructor
          · intro hneq heq
            exact hneq (congrArg (fun z => g z) heq)
          · intro hneq heq
            exact hneq (binaryRelAut_injective B g heq)
        have hlang : g.toPartialIsomorphism.lang = 1 :=
          Subsingleton.elim _ _
        have hs : Graph.action.onRel g.toPartialIsomorphism.lang
            Graph.RelSymbol.edge = Graph.RelSymbol.edge := by
          simp [hlang, Graph.action, Language.Action.trivial,
            Language.Action.onRel] <;> rfl
        rw [hs]
        have ht :
            (g.toPartialIsomorphism.toPartialEquiv ∘ xs) =
              (![g (xs 0), g (xs 1)] : Fin 2 → W) := by
          funext i
          fin_cases i <;> rfl
        rw [ht]
        change (g (xs 0) ≠ g (xs 1) ∧
          B.rel Graph.RelSymbol.edge
            (![g (xs 0), g (xs 1)] : Fin 2 → W) ∧
          B.rel Graph.RelSymbol.edge
            (![g (xs 1), g (xs 0)] : Fin 2 → W)) ↔
          (xs 0 ≠ xs 1 ∧
            B.rel Graph.RelSymbol.edge
              (![xs 0, xs 1] : Fin 2 → W) ∧
            B.rel Graph.RelSymbol.edge
              (![xs 1, xs 0] : Fin 2 → W))
        exact and_congr hne
          (and_congr
            (binaryRelAut_edge_iff B g (xs 0) (xs 1))
            (binaryRelAut_edge_iff B g (xs 1) (xs 0)))
    map_func := by
      intro n F xs hxs
      exact Empty.elim F
  }
  source_eq_univ := g.source_eq_univ
  target_eq_univ := g.target_eq_univ

@[simp] theorem symmetrizedGraphAutomorphism_apply
    {W : Type}
    (B : Structure Graph.language W)
    (g : Structure.Automorphism Graph.action B)
    (x : W) :
    symmetrizedGraphAutomorphism B g x = g x :=
  rfl

@[simp] theorem symmetrizedGraphAutomorphism_lang
    {W : Type}
    (B : Structure Graph.language W)
    (g : Structure.Automorphism Graph.action B) :
    (symmetrizedGraphAutomorphism B g).lang = g.lang :=
  rfl

end EPPAReducts.Classification
