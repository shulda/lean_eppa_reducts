import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card

/-!
# The four unordered triples on four distinct vertices

A small combinatorial bridge from ordered four-point identities to the
literal powerset-filter cardinality used in HumanTargets.TwoGraph.
The general parity-on-four-sets bridge will reuse this enumeration.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {V : Type u} [DecidableEq V]

/-- The two singleton subsets of a two-element set. -/
theorem powersetCard_one_of_pair
    (c d : V) (hcd : c ≠ d) :
    ({c, d} : Finset V).powersetCard 1 = {{c}, {d}} := by
  calc
    ({c, d} : Finset V).powersetCard 1 =
        ({d} : Finset V).powersetCard 1 ∪
          (({d} : Finset V).powersetCard 0).image (Finset.insert c) := by
      apply Finset.powersetCard_succ_insert
      simpa using hcd
    _ = {{c}, {d}} := by simp [Finset.powersetCard_self]

/-- Exactly three two-element subsets of a three-element set. -/
theorem powersetCard_two_of_triple
    (b c d : V) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({b, c, d} : Finset V).powersetCard 2 =
      {{b, c}, {b, d}, {c, d}} := by
  have hc : ({c, d} : Finset V).card = 2 := by simp [hcd]
  calc
    ({b, c, d} : Finset V).powersetCard 2 =
        ({c, d} : Finset V).powersetCard 2 ∪
          (({c, d} : Finset V).powersetCard 1).image (Finset.insert b) := by
      apply Finset.powersetCard_succ_insert
      simp [hbc, hbd]
    _ = {{b, c}, {b, d}, {c, d}} := by
      rw [← hc, Finset.powersetCard_self, powersetCard_one_of_pair c d hcd]
      simp

/-- Exactly four unordered triples occur on four distinct vertices. -/
theorem powersetCard_three_of_quadruple
    (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset V).powersetCard 3 =
      {{a, b, c}, {a, b, d}, {a, c, d}, {b, c, d}} := by
  have hc : ({b, c, d} : Finset V).card = 3 := by simp [hbc, hbd, hcd]
  calc
    ({a, b, c, d} : Finset V).powersetCard 3 =
        ({b, c, d} : Finset V).powersetCard 3 ∪
          (({b, c, d} : Finset V).powersetCard 2).image (Finset.insert a) := by
      apply Finset.powersetCard_succ_insert
      simp [hab, hac, had]
    _ = {{a, b, c}, {a, b, d}, {a, c, d}, {b, c, d}} := by
      rw [← hc, Finset.powersetCard_self,
        powersetCard_two_of_triple b c d hbc hbd hcd]
      simp

end EPPAReducts.TwoGraphs
