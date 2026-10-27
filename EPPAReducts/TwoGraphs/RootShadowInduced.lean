import EPPAReducts.TwoGraphs.RootingShadow
import EPPAReducts.TwoGraphs.RootedTripleKernel

/-!
# Root-shadow compatibility with the original unlabelled pair reduct

This module connects the exact induced-equivalence predicates on
unordered old pairs and rooted triples. All colours are existential
presentations, never names in the structure.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets
open EPPAReducts.BoundedEquivalence

variable {V W : Type}

/-- Attach a new root to an arbitrary unlabelled pair-equivalence structure. -/
noncomputable def rootedOfPairClasses
    (A : GraphModuloComplementation V) :
    TwoGraphModuloComplementation (Option V) :=
  rootedModuloGraph (Classical.choose A.atMostTwoClasses)

/-- The root triples of the constructed object encode exactly the
original *unlabelled* class equality, not any named edge colour. -/
theorem rootedOfPairClasses_pairKernel
    (A : GraphModuloComplementation V)
    (e f : UnorderedPairs V) :
    (rootedOfPairClasses A).sameClass.r
      (rootedTripleOfPair e) (rootedTripleOfPair f) ↔
    A.sameClass.r e f := by
  let c := Classical.choose A.atMostTwoClasses
  have hc : ∀ u v : UnorderedPairs V,
      A.sameClass.r u v ↔ c u = c v :=
    Classical.choose_spec A.atMostTwoClasses
  exact (rootedModulo_pairKernel c e f).trans (hc e f).symm

/-- Mapping an old pair into the root shadow and then adjoining the
root equals mapping its rooted triple through the original embedding. -/
theorem tripleAboveRoot_shadowEmbedding
    (ι : Option V ↪ W) (e : UnorderedPairs V) :
    tripleAboveRoot (ι none) (mapPair (shadowEmbedding ι) e) =
      mapRSubset ι (rootedTripleOfPair e) := by
  classical
  rcases e with ⟨s, hs⟩
  obtain ⟨x, y, hxy, hxyset⟩ := Finset.card_eq_two.mp hs
  subst s
  apply Subtype.ext
  simp [tripleAboveRoot, shadowEmbedding, mapPair,
    rootedTripleOfPair, mapRSubset, hxy]

/-- Any induced extension of the rooted triple-class object induces
a genuine induced extension of the original pair-class structure
by deleting the distinguished root. -/
theorem inducedPairShadow_of_inducedRootedTriples
    (A : GraphModuloComplementation V)
    (C : TwoGraphModuloComplementation W)
    (ι : Option V ↪ W)
    (hι : IsInducedTripleClassEmbedding (rootedOfPairClasses A) C ι) :
    IsInducedPairEmbedding A (shadowAtRoot C (ι none))
      (shadowEmbedding ι) := by
  intro e f
  change A.sameClass.r e f ↔
    C.sameClass.r
      (tripleAboveRoot (ι none) (mapPair (shadowEmbedding ι) e))
      (tripleAboveRoot (ι none) (mapPair (shadowEmbedding ι) f))
  rw [tripleAboveRoot_shadowEmbedding,
    tripleAboveRoot_shadowEmbedding]
  exact (rootedOfPairClasses_pairKernel A e f).symm.trans
    (hι (rootedTripleOfPair e) (rootedTripleOfPair f))

end EPPAReducts.TwoGraphs
