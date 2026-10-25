import EPPAReducts.TwoGraphs.UnorderedTripleRelation
import EPPAReducts.TwoGraphs.FourTripleDistinct
import EPPAReducts.TwoGraphs.FourBoolCount
import EPPAReducts.HumanTargets

/-!
# A genuine finite two-graph structure on the valuation carrier

This theorem combines the verified quotient parity, independent
triple enumeration, the four-subset enumeration, and Boolean
filter-cardinality arithmetic. It constructs a structure in the
EXACT approved human-facing TwoGraph API, rather than replacing that
specification with a technical weakening.

This is a two-graph witness *carrier and relation*, not yet any
EPPA or coherent extension of partial automorphisms.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u} [DecidableEq (ValuationVertex X)]

/-- The literal four-point even-cardinality condition for the
unordered valuation triple predicate. -/
theorem unorderedTripleParity_fourPointEven
    (q : Finset (ValuationVertex X)) (hq : q.card = 4) :
    (q.powerset.filter
      (fun s => unorderedTripleParity s = true)).card % 2 = 0 := by
  classical
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ :=
    Finset.card_eq_four.mp hq
  have hfiltered :
      (({a, b, c, d} : Finset (ValuationVertex X)).powerset.filter
        (fun s => unorderedTripleParity s = true)) =
      (({a, b, c, d} : Finset (ValuationVertex X)).powersetCard 3).filter
        (fun s => unorderedTripleParity s = true) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨hs, htriple⟩
      exact ⟨⟨hs, unorderedTripleParity_onlyTriples s htriple⟩, htriple⟩
    · rintro ⟨⟨hs, _⟩, htriple⟩
      exact ⟨hs, htriple⟩
  rw [hfiltered, powersetCard_three_of_quadruple
    a b c d hab hac had hbc hbd hcd]
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ :=
    four_triple_subsets_distinct a b c d hab hac had hbc hbd hcd
  apply (four_filter_even_iff_xor
    (f := unorderedTripleParity)
    ({a, b, c} : Finset (ValuationVertex X))
    ({a, b, d} : Finset (ValuationVertex X))
    ({a, c, d} : Finset (ValuationVertex X))
    ({b, c, d} : Finset (ValuationVertex X))
    h12 h13 h14 h23 h24 h34).2
  simpa only [
    unorderedTripleParity_on_three a b c hab hac hbc,
    unorderedTripleParity_on_three a b d hab had hbd,
    unorderedTripleParity_on_three a c d hac had hcd,
    unorderedTripleParity_on_three b c d hbc hbd hcd] using
      vertexFourPointParityXor a b c d

/-- The valuation construction is a two-graph in the EXACT
independent, author-approved HumanTargets.TwoGraph specification. -/
noncomputable def valuationTwoGraph (X : Type) :
    HumanTargets.TwoGraph (ValuationVertex X) := by
  classical
  exact {
    isTriple := unorderedTripleParity
    onlyTriples := fun s h => unorderedTripleParity_onlyTriples s h
    fourPointEven := fun q hq => unorderedTripleParity_fourPointEven q hq
  }

end EPPAReducts.TwoGraphs
