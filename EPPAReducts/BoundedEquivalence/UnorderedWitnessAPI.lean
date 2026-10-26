import EPPAReducts.BoundedEquivalence.Basic
import EPPAReducts.HumanTargets

/-!
# Exact ordinary EPPA witness semantics for unordered r-subsets

The carrier of the relation is the set of all subsets of cardinality r.
The actual structure remembers only the equivalence relation, with
at most m *unlabelled* classes. Auxiliary numerical colourings are
not named in the language; automorphisms may permute the classes.

At r=m=2 this uses literally the same carrier and induced
embedding/partial automorphism notions as the frozen
HumanTargets.GraphModuloComplementation API.
-/

namespace EPPAReducts.BoundedEquivalence

open EPPAReducts.HumanTargets

/-- The action of an injective vertex map on unordered r-subsets. -/
def mapRSubset {V W : Type} {r : ℕ}
    (ι : V ↪ W) (s : RSubsets V r) : RSubsets W r :=
  ⟨s.val.map ι, by simpa using s.property⟩

/-- The action of a vertex permutation on unordered r-subsets. -/
def permuteRSubset {V : Type} {r : ℕ}
    (g : Equiv.Perm V) (s : RSubsets V r) : RSubsets V r :=
  mapRSubset (embeddingOfEquiv g) s

/-- An unlabelled equivalence relation on r-element subsets of V,
with at most m classes. -/
structure UnorderedBoundedEquivalence (V : Type) (r m : ℕ) where
  sameClass : Setoid (RSubsets V r)
  atMostClasses : HasAtMostClasses sameClass m

/-- An induced embedding preserves and reflects the equivalence of
classes of every two unordered r-subsets. -/
def IsInducedUnorderedBoundedEmbedding
    {V W : Type} {r m : ℕ}
    (A : UnorderedBoundedEquivalence V r m)
    (B : UnorderedBoundedEquivalence W r m)
    (ι : V ↪ W) : Prop :=
  ∀ e f : RSubsets V r,
    A.sameClass.r e f ↔
      B.sameClass.r (mapRSubset ι e) (mapRSubset ι f)

/-- A literal partial vertex bijection preserving and reflecting
the unlabelled r-subset equivalence on its induced domains. -/
def IsUnorderedBoundedPartialAutomorphism
    {V : Type} {r m : ℕ}
    (A : UnorderedBoundedEquivalence V r m)
    (p : PartialBijection V) : Prop :=
  ∀ e f : RSubsets {v : V // v ∈ p.source} r,
    A.sameClass.r
      (mapRSubset (subtypeEmbedding p.source) e)
      (mapRSubset (subtypeEmbedding p.source) f) ↔
    A.sameClass.r
      (mapRSubset (equivThenEmbedding p.bijection
        (subtypeEmbedding p.target)) e)
      (mapRSubset (equivThenEmbedding p.bijection
        (subtypeEmbedding p.target)) f)

/-- A genuine automorphism of the unlabelled r-subset equivalence:
there are no named numerical class colours. -/
def IsUnorderedBoundedAutomorphism
    {V : Type} {r m : ℕ}
    (A : UnorderedBoundedEquivalence V r m)
    (g : Equiv.Perm V) : Prop :=
  ∀ e f : RSubsets V r,
    A.sameClass.r e f ↔
      A.sameClass.r (permuteRSubset g e) (permuteRSubset g f)

/-- An ordinary EPPA witness is a common finite induced extension
whose full automorphisms extend *every* partial automorphism. -/
def IsUnorderedBoundedEPPAWitness
    {V W : Type} {r m : ℕ}
    (A : UnorderedBoundedEquivalence V r m)
    (B : UnorderedBoundedEquivalence W r m)
    (ι : V ↪ W) : Prop :=
  IsInducedUnorderedBoundedEmbedding A B ι ∧
    ∀ (p : PartialBijection V),
      IsUnorderedBoundedPartialAutomorphism A p →
      ∃ g : Equiv.Perm W,
        IsUnorderedBoundedAutomorphism B g ∧ Extends ι p g

/-- The specialization to unordered pairs is literally the
transport used in the frozen human-facing target. -/
theorem mapRSubset_two_eq_mapPair
    {V W : Type} (ι : V ↪ W) (e : UnorderedPairs V) :
    mapRSubset ι e = mapPair ι e := rfl

/-- Convert the approved graph-modulo-complementation structure to
the generic arity-2 unlabelled subset-equivalence structure. -/
noncomputable def graphToUnordered {V : Type}
    (A : GraphModuloComplementation V) :
    UnorderedBoundedEquivalence V 2 2 where
  sameClass := A.sameClass
  atMostClasses := by
    obtain ⟨label, hlabel⟩ := A.atMostTwoClasses
    refine ⟨fun e => if label e = true then (1 : Fin 2) else 0, ?_⟩
    intro e f
    rw [hlabel e f]
    cases hE : label e <;> cases hF : label f <;> simp [hE, hF]

/-- Generic induced embeddings at arity 2 mean exactly the approved
unlabelled pair induced embeddings. -/
theorem graphToUnordered_induced_iff
    {V W : Type} (A : GraphModuloComplementation V)
    (B : GraphModuloComplementation W) (ι : V ↪ W) :
    IsInducedUnorderedBoundedEmbedding
      (graphToUnordered A) (graphToUnordered B) ι ↔
      IsInducedPairEmbedding A B ι := Iff.rfl

/-- Generic partial automorphisms at arity 2 mean exactly the
approved unlabelled pair partial automorphisms. -/
theorem graphToUnordered_partial_iff
    {V : Type} (A : GraphModuloComplementation V)
    (p : PartialBijection V) :
    IsUnorderedBoundedPartialAutomorphism (graphToUnordered A) p ↔
      IsPairPartialAutomorphism A p := Iff.rfl

/-- Likewise for full vertex automorphisms. -/
theorem graphToUnordered_automorphism_iff
    {V : Type} (A : GraphModuloComplementation V)
    (g : Equiv.Perm V) :
    IsUnorderedBoundedAutomorphism (graphToUnordered A) g ↔
      IsPairAutomorphism A g := Iff.rfl

/-- Consequently the two ordinary EPPA witness predicates coincide
at r=m=2, including their full quantifier order. -/
theorem graphToUnordered_EPPAWitness_iff
    {V W : Type} (A : GraphModuloComplementation V)
    (B : GraphModuloComplementation W) (ι : V ↪ W) :
    IsUnorderedBoundedEPPAWitness
      (graphToUnordered A) (graphToUnordered B) ι ↔
      IsPairEPPAWitness A B ι := Iff.rfl

end EPPAReducts.BoundedEquivalence
