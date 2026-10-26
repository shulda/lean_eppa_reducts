import EPPAReducts.TwoGraphs.PartialAutomorphismExtension
import EPPAReducts.TwoGraphs.FactorialRootedWitness

/-!
# Ordinary EPPA for all finite two-graphs

The certified rooted representation embeds any nonempty finite input
two-graph into C_X for X = Fin (|V|!). The certified indexed-transversal
extension supplies actual automorphisms of C_X extending every
literal partial automorphism of the original input.

An empty input also embeds over the same factorial index type:
its unique map into the valuation witness is induced, and the
general partial-automorphism extension theorem handles it.

The final statement supplies one common finite witness and extensions
for all partial automorphisms. It does NOT yet make a coherent choice.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- A fixed factorial-size valuation witness extends all partial
automorphisms of any nonempty finite two-graph in the exact
human-approved partial-bijection API. -/
theorem exists_factorialValuation_EPPA_nonempty
    {V : Type} [Fintype V] [Nonempty V]
    (A : TwoGraph V) :
    ∃ χ : V → Valuation (Fin (Nat.factorial (Fintype.card V))),
      IsInducedTwoGraphEmbedding A
        (valuationTwoGraph (Fin (Nat.factorial (Fintype.card V))))
        (indexedTransversalEmbedding factorialIndexEmbedding χ) ∧
      ∀ (p : PartialBijection V),
        IsTwoGraphPartialAutomorphism A p →
        ∃ g : Equiv.Perm
          (ValuationVertex (Fin (Nat.factorial (Fintype.card V)))),
          IsTwoGraphAutomorphism
            (valuationTwoGraph (Fin (Nat.factorial (Fintype.card V)))) g ∧
          Extends (indexedTransversalEmbedding
            factorialIndexEmbedding χ) p g := by
  classical
  obtain ⟨χ, hind, _⟩ := exists_factorialRootedTransversal A
  refine ⟨χ, hind, ?_⟩
  intro p hp
  exact exists_valuationTwoGraph_extension_of_partial
    A factorialIndexEmbedding χ hind p hp

/-- Empty input handled without picking a nonexisting root; no
extra cardinality assumptions appear in the EPPA statement. -/
theorem exists_factorialValuation_EPPA
    {V : Type} [Fintype V] (A : TwoGraph V) :
    ∃ χ : V → Valuation (Fin (Nat.factorial (Fintype.card V))),
      IsInducedTwoGraphEmbedding A
        (valuationTwoGraph (Fin (Nat.factorial (Fintype.card V))))
        (indexedTransversalEmbedding factorialIndexEmbedding χ) ∧
      ∀ (p : PartialBijection V),
        IsTwoGraphPartialAutomorphism A p →
        ∃ g : Equiv.Perm
          (ValuationVertex (Fin (Nat.factorial (Fintype.card V)))),
          IsTwoGraphAutomorphism
            (valuationTwoGraph (Fin (Nat.factorial (Fintype.card V)))) g ∧
          Extends (indexedTransversalEmbedding
            factorialIndexEmbedding χ) p g := by
  classical
  by_cases hV : Nonempty V
  · letI : Nonempty V := hV
    exact exists_factorialValuation_EPPA_nonempty A
  · let χ : V → Valuation (Fin (Nat.factorial (Fintype.card V))) :=
      fun v => False.elim (hV ⟨v⟩)
    have hind : IsInducedTwoGraphEmbedding A
        (valuationTwoGraph (Fin (Nat.factorial (Fintype.card V))))
        (indexedTransversalEmbedding factorialIndexEmbedding χ) := by
      intro x y z
      exact False.elim (hV ⟨x⟩)
    refine ⟨χ, hind, ?_⟩
    intro p hp
    exact exists_valuationTwoGraph_extension_of_partial
      A factorialIndexEmbedding χ hind p hp

/-- Ordinary EPPA for EVERY finite two-graph: there exists one common
finite induced extension extending every literal partial automorphism.
This is weaker than the requested coherent EPPA theorem. -/
theorem allFiniteTwoGraphsHaveOrdinaryEPPA
    {V : Type} [Fintype V] (A : TwoGraph V) :
    ∃ (W : Type) (B : TwoGraph W) (ι : V ↪ W),
      Finite W ∧
      IsInducedTwoGraphEmbedding A B ι ∧
      ∀ (p : PartialBijection V),
        IsTwoGraphPartialAutomorphism A p →
        ∃ g : Equiv.Perm W,
          IsTwoGraphAutomorphism B g ∧ Extends ι p g := by
  classical
  obtain ⟨χ, hind, hext⟩ := exists_factorialValuation_EPPA A
  exact ⟨ValuationVertex (Fin (Nat.factorial (Fintype.card V))),
    valuationTwoGraph (Fin (Nat.factorial (Fintype.card V))),
    indexedTransversalEmbedding factorialIndexEmbedding χ,
    inferInstance, hind, hext⟩

end EPPAReducts.TwoGraphs
