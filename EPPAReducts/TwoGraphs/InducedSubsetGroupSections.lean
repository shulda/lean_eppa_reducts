import EPPAReducts.TwoGraphs.CanonicalAmbientTransport
import EPPAReducts.TwoGraphs.InducedSubtypeSection

/-!
# Simultaneous subgroup sections for every induced sub-two-graph

This reusable structure records an extension of Aut(A|s) into the
automorphism group of a common witness, together with the exact
identity and composition laws. It is formulated in the literal
HumanTargets two-graph language, independent of valuation encodings.

For the valuation witness C_X, every nonempty subset satisfying the
cardinality divisibility condition has such a section by the already
certified divisible-transversal theorem. The empty subset has the
trivial section, so a single family can be chosen for ALL subsets.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- A permutation of the induced vertex set s preserves all its
original distinguished triples. -/
def PreservesInducedSubset {V : Type} (A : TwoGraph V)
    (s : Finset V) (p : Equiv.Perm {v : V // v ∈ s}) : Prop :=
  ∀ x y z : {v : V // v ∈ s},
    A.isTriple (triple x.val y.val z.val) =
      A.isTriple (triple (p x).val (p y).val (p z).val)

theorem preservesInducedSubset_refl {V : Type}
    (A : TwoGraph V) (s : Finset V) :
    PreservesInducedSubset A s (Equiv.refl _) := by
  intro x y z
  rfl

theorem preservesInducedSubset_trans {V : Type}
    (A : TwoGraph V) (s : Finset V)
    (p q : Equiv.Perm {v : V // v ∈ s})
    (hp : PreservesInducedSubset A s p)
    (hq : PreservesInducedSubset A s q) :
    PreservesInducedSubset A s (p.trans q) := by
  intro x y z
  exact (hp x y z).trans (hq (p x) (p y) (p z))

/-- All requirements for a homomorphic lift of the full automorphism
group of one induced substructure to genuine automorphisms of B. -/
structure InducedSubsetGroupSection {V W : Type}
    (A : TwoGraph V) (B : TwoGraph W)
    (ψ : V ↪ W) (s : Finset V) where
  lift : (p : Equiv.Perm {v : V // v ∈ s}) →
    PreservesInducedSubset A s p → Equiv.Perm W
  isAutomorphism : ∀ p hp, IsTwoGraphAutomorphism B (lift p hp)
  extendsOld : ∀ p hp (x : {v : V // v ∈ s}),
    lift p hp (ψ x.val) = ψ (p x).val
  lift_refl :
    lift (Equiv.refl _) (preservesInducedSubset_refl A s) = Equiv.refl W
  lift_trans : ∀ p q
      (hp : PreservesInducedSubset A s p)
      (hq : PreservesInducedSubset A s q),
    (lift p hp).trans (lift q hq) =
      lift (p.trans q) (preservesInducedSubset_trans A s p q hp hq)

/-- Every induced subset of A has a group section on C_X once its
nonempty size divides |X|. The empty case requires no divisibility
hypothesis and uses the identity automorphism. -/
theorem exists_inducedSubsetGroupSection
    {V X : Type} [Fintype V] [Fintype X]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (s : Finset V)
    (hdiv : s.Nonempty →
      Fintype.card {v : V // v ∈ s} ∣ Fintype.card X) :
    Nonempty (InducedSubsetGroupSection A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ) s) := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨lift, hauto, hmap, hid, hcomp⟩ :=
      exists_inducedSubtype_coherentLift A ι χ hind s hs (hdiv hs)
    exact ⟨{
      lift := lift
      isAutomorphism := hauto
      extendsOld := hmap
      lift_refl := hid
      lift_trans := hcomp
    }⟩
  · refine ⟨{
      lift := fun _ _ => Equiv.refl (ValuationVertex X)
      isAutomorphism := ?_
      extendsOld := ?_
      lift_refl := ?_
      lift_trans := ?_
    }⟩
    · intro p hp x y z
      rfl
    · intro p hp x
      exact False.elim (hs ⟨x.val, x.property⟩)
    · rfl
    · intro p q hp hq
      rfl

/-- Fix a complete family of subgroup sections simultaneously,
including the empty subset. All chosen actions live on the SAME C_X. -/
noncomputable def chosenInducedSubsetGroupSection
    {V X : Type} [Fintype V] [Fintype X]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (hdiv : ∀ s : Finset V, s.Nonempty →
      Fintype.card {v : V // v ∈ s} ∣ Fintype.card X)
    (s : Finset V) :
    InducedSubsetGroupSection A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ) s :=
  Classical.choice (exists_inducedSubsetGroupSection A ι χ hind s (hdiv s))

end EPPAReducts.TwoGraphs
