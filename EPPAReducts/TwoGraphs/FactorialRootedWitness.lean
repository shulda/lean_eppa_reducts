import EPPAReducts.TwoGraphs.FiniteCommonIndex

/-!
# One finite valuation witness carrier for all induced subsets

Take X := Fin (|V|!).  For every nonempty finite two-graph A on V,
the canonical factorial index injection is induced by a family of
X-valuations, by the previously certified indexed embedding theorem.

At the same time, the cardinality of every nonempty induced subset
of V divides |X|.  This is precisely the global cardinal arithmetic
needed to apply the already-certified subgroup section separately
to any such subset, always inside the same valuation two-graph C_X.

No ordinary or coherent EPPA extension assertion is made here.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- A common finite valuation carrier with an induced copy of A
and the divisibility condition for every nonempty induced subset.
The chosen index size is factorial rather than the paper's smaller
LCM bound; the approved final theorem has no size requirement. -/
theorem exists_factorialRootedTransversal
    {V : Type} [Fintype V] [Nonempty V]
    [DecidableEq
      (ValuationVertex (Fin (Nat.factorial (Fintype.card V))))]
    (A : TwoGraph V) :
    ∃ χ : V → Valuation (Fin (Nat.factorial (Fintype.card V))),
      IsInducedTwoGraphEmbedding A
        (valuationTwoGraph (Fin (Nat.factorial (Fintype.card V))))
        (indexedTransversalEmbedding factorialIndexEmbedding χ) ∧
      ∀ (s : Finset V), s.Nonempty →
        Fintype.card {v : V // v ∈ s} ∣
          Fintype.card (Fin (Nat.factorial (Fintype.card V))) := by
  classical
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  have hdiv : Fintype.card V ∣
      Fintype.card (Fin (Nat.factorial (Fintype.card V))) := by
    simpa using Nat.dvd_factorial hpos (le_refl (Fintype.card V))
  obtain ⟨χ, hχ⟩ :=
    exists_indexed_rootedTransversal A factorialIndexEmbedding hdiv
  exact ⟨χ, hχ, fun s hs => card_nonempty_subtype_dvd_index s hs⟩

end EPPAReducts.TwoGraphs
