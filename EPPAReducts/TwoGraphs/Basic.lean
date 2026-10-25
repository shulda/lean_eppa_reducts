import Mathlib.Data.Finset.Card

/-!
# Finite two-graphs

The positive development will formalize coherent EPPA via quotient valuations.
This module starts with the four-point parity predicate, independently of
any particular witness construction.
-/

namespace EPPAReducts.TwoGraphs

/-- A predicate on unordered finite subsets; only its values on triples matter. -/
abbrev TriplePredicate (α : Type*) := Finset α → Prop

/-- Every four-element set contains an even number of distinguished triples. -/
def IsTwoGraph {α : Type*} (T : TriplePredicate α) : Prop := by
  classical
  exact ∀ Q : Finset α, Q.card = 4 →
    ((Q.powerset.filter (fun s => s.card = 3 ∧ T s)).card % 2 = 0)

end EPPAReducts.TwoGraphs
