import EPPAReducts.TwoGraphs.CanonicalCoherentLiftComposition
import EPPAReducts.TwoGraphs.FiniteValuationEPPA

/-!
# Finite coherent EPPA witness for every two-graph

The concrete valuation witness simultaneously realizes every
partial automorphism and a single coherent extension map.
The factorial index set makes every nonempty induced-subset
cardinality divide the witness index cardinality. The empty
input is handled by the same already certified representation lemma.

The final declaration proves the exact previously approved,
standalone HumanTargets proposition.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- An induced valuation transversal with the simultaneous subgroup
section divisibility property is a genuine coherent EPPA witness.
Both ambient preservation and literal composition are required. -/
theorem valuationTwoGraph_coherentEPPAWitness
    {V X : Type} [Fintype V] [Fintype X]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X) (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (hdiv : ∀ s : Finset V, s.Nonempty →
      Fintype.card {v : V // v ∈ s} ∣ Fintype.card X) :
    Nonempty (CoherentTwoGraphWitness A) := by
  refine ⟨{
    W := ValuationVertex X
    finiteW := inferInstance
    B := valuationTwoGraph X
    inclusion := indexedTransversalEmbedding ι χ
    induced := hind
    extension := fun p hp => canonicalConjugatedLift A ι χ hind hdiv p hp
    isAutomorphism := ?_
    extendsOld := ?_
    coherent := ?_
  }⟩
  · intro p hp
    exact canonicalConjugatedLift_isAutomorphism A ι χ hind hdiv p hp
  · intro p hp
    exact canonicalConjugatedLift_extendsOld A ι χ hind hdiv p hp
  · intro p q r hp hq hr h w
    have hc := canonicalConjugatedLift_composition
      A ι χ hind hdiv p q r hp hq hr h
    have hw := congrArg (fun g : Equiv.Perm (ValuationVertex X) => g w) hc
    simpa only [Equiv.trans_apply] using hw.symm

/-- Every finite input two-graph, including the empty one, has a
common finite coherent witness of valuation type over Fin (|V|!).
No extra assumptions are placed on the input two-graph. -/
theorem allFiniteTwoGraphsHaveCoherentEPPA
    {V : Type} [Fintype V] (A : TwoGraph V) :
    Nonempty (CoherentTwoGraphWitness A) := by
  classical
  obtain ⟨χ, hind, _⟩ := exists_factorialValuation_EPPA A
  have hdiv : ∀ s : Finset V, s.Nonempty →
      Fintype.card {v : V // v ∈ s} ∣
        Fintype.card (Fin (Nat.factorial (Fintype.card V))) := by
    intro s hs
    exact card_nonempty_subtype_dvd_index s hs
  exact valuationTwoGraph_coherentEPPAWitness A
    factorialIndexEmbedding χ hind hdiv

/-- The exact human-approved standalone coherent EPPA target for
all finite two-graphs, without chosen orders, roots, or nonemptiness
assumptions. -/
theorem humanTwoGraphsHaveCoherentEPPA :
    EPPAReducts.HumanTargets.twoGraphsHaveCoherentEPPA := by
  intro V hfinite A
  letI : Finite V := hfinite
  classical
  letI : Fintype V := Fintype.ofFinite V
  exact allFiniteTwoGraphsHaveCoherentEPPA A

end EPPAReducts.TwoGraphs
