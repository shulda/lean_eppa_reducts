import EPPAReducts.TwoGraphs.UnorderedTriplePermutation
import Mathlib.Data.Finset.Card

/-!
# The valuation triple relation on unordered three-element sets

A three-element Finset has an arbitrary enumeration. The already proved
permutation-invariance theorem ensures that its parity does not depend
on that choice. False is assigned to sets of every other cardinality.

The eventual HumanTargets.TwoGraph packages this relation together
with the four-point cardinality condition, which is still a separate
proof obligation here.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u} [DecidableEq (ValuationVertex X)]

private theorem exists_three_tuple
    (s : Finset (ValuationVertex X)) (hs : s.card = 3) :
    ∃ t : ValuationVertex X × (ValuationVertex X × ValuationVertex X),
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
      s = {t.1, t.2.1, t.2.2} := by
  obtain ⟨a, b, c, hab, hac, hbc, heq⟩ := Finset.card_eq_three.mp hs
  exact ⟨⟨a, ⟨b, c⟩⟩, hab, hac, hbc, heq⟩

/-- Choose an enumeration of an unordered three-element subset. -/
private noncomputable def chosenThree
    (s : Finset (ValuationVertex X)) (hs : s.card = 3) :
    ValuationVertex X × (ValuationVertex X × ValuationVertex X) :=
  Classical.choose (exists_three_tuple s hs)

private theorem chosenThree_spec
    (s : Finset (ValuationVertex X)) (hs : s.card = 3) :
    (chosenThree s hs).1 ≠ (chosenThree s hs).2.1 ∧
    (chosenThree s hs).1 ≠ (chosenThree s hs).2.2 ∧
    (chosenThree s hs).2.1 ≠ (chosenThree s hs).2.2 ∧
    s = {(chosenThree s hs).1, (chosenThree s hs).2.1,
         (chosenThree s hs).2.2} :=
  Classical.choose_spec (exists_three_tuple s hs)

/-- The unlabelled valuation triple predicate, false on non-triples. -/
noncomputable def unorderedTripleParity
    (s : Finset (ValuationVertex X)) : Bool := by
  classical
  exact if hs : s.card = 3 then
    let t := chosenThree s hs
    vertexTripleParity t.1 t.2.1 t.2.2
  else false

/-- Only genuine three-element sets are distinguished. -/
theorem unorderedTripleParity_onlyTriples
    (s : Finset (ValuationVertex X))
    (h : unorderedTripleParity s = true) : s.card = 3 := by
  classical
  by_contra hn
  simp [unorderedTripleParity, hn] at h

/-- For distinct vertices the unordered predicate agrees exactly
with the original symmetric ternary valuation formula. -/
theorem unorderedTripleParity_on_three
    (a b c : ValuationVertex X)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    unorderedTripleParity ({a, b, c} : Finset (ValuationVertex X)) =
      vertexTripleParity a b c := by
  classical
  have hs : ({a, b, c} : Finset (ValuationVertex X)).card = 3 := by
    simp [hab, hac, hbc]
  obtain ⟨h₁, h₂, h₃, hset⟩ :=
    chosenThree_spec ({a, b, c} : Finset (ValuationVertex X)) hs
  have hchoice :=
    (vertexTripleParity_eq_of_same_finset
      a b c (chosenThree {a, b, c} hs).1
        (chosenThree {a, b, c} hs).2.1
        (chosenThree {a, b, c} hs).2.2
      hab hac hbc h₁ h₂ h₃ hset).symm
  simpa [unorderedTripleParity, hs] using hchoice

end EPPAReducts.TwoGraphs
