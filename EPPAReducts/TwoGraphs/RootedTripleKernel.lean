import EPPAReducts.TwoGraphs.RootingPairColours

/-!
# Exact pair-kernel embedding into the rooted two-graph reduct

An unordered old pair is identified with the unordered triple formed
by adjoining the new root. The equivalence of these triples is
definitionally that of the original pair labels, even though the
class labels are not named relations in either reduct.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets
open EPPAReducts.BoundedEquivalence

variable {V : Type}

private def oldEmbedding : V ↪ Option V :=
  ⟨some, by intro a b h; exact Option.some.inj h⟩

/-- Adjoin the new root to an unordered old pair. -/
noncomputable def rootedTripleOfPair (e : UnorderedPairs V) :
    UnorderedTriples (Option V) := by
  classical
  let old : Finset (Option V) := e.val.map oldEmbedding
  have hnone : none ∉ old := by
    simp [old, oldEmbedding]
  refine ⟨insert none old, ?_⟩
  simp [hnone, old, e.property]

/-- Evaluation of the root triangle is precisely the old edge label. -/
theorem rootedTripleOfPair_colour
    (c : UnorderedPairs V → Bool) (e : UnorderedPairs V) :
    (rootedTwoGraph c).isTriple (rootedTripleOfPair e).val = c e := by
  classical
  rcases e with ⟨s, hs⟩
  obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.mp hs
  subst s
  have h := rootedTwoGraph_on_root c x y hxy
  simpa [rootedTripleOfPair, oldEmbedding, triple] using h

/-- The class equivalence on triples induced by the rooted two-graph.
A representative exists but is not named in the relational language. -/
noncomputable def rootedModuloGraph
    (c : UnorderedPairs V → Bool) :
    TwoGraphModuloComplementation (Option V) := by
  classical
  let T := rootedTwoGraph c
  refine {
    sameClass := {
      r := fun e f => T.isTriple e.val = T.isTriple f.val
      iseqv := ⟨(by intro e; rfl),
        (by intro e f h; exact h.symm),
        (by intro e f g h1 h2; exact h1.trans h2)⟩
    }
    representative := ?_
  }
  exact ⟨T, by intro e f; rfl⟩

/-- On triples containing the root, the triple-class kernel and the
original pair-class kernel coincide. -/
theorem rootedModulo_pairKernel
    (c : UnorderedPairs V → Bool)
    (e f : UnorderedPairs V) :
    (rootedModuloGraph c).sameClass.r
      (rootedTripleOfPair e) (rootedTripleOfPair f) ↔ c e = c f := by
  change
    (rootedTwoGraph c).isTriple (rootedTripleOfPair e).val =
      (rootedTwoGraph c).isTriple (rootedTripleOfPair f).val ↔
      c e = c f
  rw [rootedTripleOfPair_colour, rootedTripleOfPair_colour]

end EPPAReducts.TwoGraphs
