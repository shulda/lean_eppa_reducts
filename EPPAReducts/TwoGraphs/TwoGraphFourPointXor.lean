import EPPAReducts.TwoGraphs.RootedGraph
import EPPAReducts.TwoGraphs.FourBoolCount
import EPPAReducts.TwoGraphs.FourTripleDistinct

/-!
# Four-point Boolean parity for any actual two-graph

The independent HumanTargets specification counts the distinguished
three-element subsets of each four-set.  This module converts that
literal finite-set cardinality condition into the equivalent Boolean
four-term XOR equation for four pairwise distinct vertices.

No representation or EPPA conclusion is assumed.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- The literal even-cardinality axiom gives the four-term XOR equation
on any four distinct vertices of any two-graph, not just the constructed
valuation witness. -/
theorem twoGraph_fourPointXor
    {V : Type} (A : TwoGraph V)
    (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Bool.xor
      (Bool.xor
        (Bool.xor (A.isTriple (triple a b c))
          (A.isTriple (triple a b d)))
        (A.isTriple (triple a c d)))
      (A.isTriple (triple b c d)) = false := by
  classical
  let q : Finset V := {a, b, c, d}
  have hcard : q.card = 4 := by
    dsimp [q]
    simp [hab, hac, had, hbc, hbd, hcd]
  have hfiltered :
      (q.powerset.filter (fun s => A.isTriple s = true)) =
      (({a, b, c, d} : Finset V).powersetCard 3).filter
        (fun s => A.isTriple s = true) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨hs, ht⟩
      exact ⟨⟨hs, A.onlyTriples s ht⟩, ht⟩
    · rintro ⟨⟨hs, _⟩, ht⟩
      exact ⟨hs, ht⟩
  have hfour := A.fourPointEven q hcard
  rw [hfiltered, powersetCard_three_of_quadruple
    a b c d hab hac had hbc hbd hcd] at hfour
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ :=
    four_triple_subsets_distinct a b c d hab hac had hbc hbd hcd
  have hx := (four_filter_even_iff_xor (f := A.isTriple)
    ({a, b, c} : Finset V) ({a, b, d} : Finset V)
    ({a, c, d} : Finset V) ({b, c, d} : Finset V)
    h12 h13 h14 h23 h24 h34).mp hfour
  simpa only [triple] using hx

end EPPAReducts.TwoGraphs
