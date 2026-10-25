import EPPAReducts.TwoGraphs.ValuationTernaryExtras
import Mathlib.Data.Finset.Card

/-!
# Invariance under arbitrary enumerations of an unordered triple

The previously certified adjacent-swap identities imply that the
ternary valuation parity depends only on the underlying three-element
Finset, not on its chosen ordering. This is needed before defining
the actual HumanTargets.TwoGraph relation.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u} [DecidableEq (ValuationVertex X)]

/-- The ternary parity agrees on any two distinct enumerations of
the same unordered triple of valuation vertices. -/
theorem vertexTripleParity_eq_of_same_finset
    (a b c a' b' c' : ValuationVertex X)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha'b' : a' ≠ b') (ha'c' : a' ≠ c') (hb'c' : b' ≠ c')
    (hsets : ({a, b, c} : Finset (ValuationVertex X)) = {a', b', c'}) :
    vertexTripleParity a b c = vertexTripleParity a' b' c' := by
  classical
  have hmemA : a' ∈ ({a, b, c} : Finset (ValuationVertex X)) := by
    rw [hsets]
    simp
  have hmemB : b' ∈ ({a, b, c} : Finset (ValuationVertex X)) := by
    rw [hsets]
    simp
  have hmemC : c' ∈ ({a, b, c} : Finset (ValuationVertex X)) := by
    rw [hsets]
    simp
  have ha : a' = a ∨ a' = b ∨ a' = c := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmemA
  have hb : b' = a ∨ b' = b ∨ b' = c := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmemB
  have hc : c' = a ∨ c' = b ∨ c' = c := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmemC
  have h1 : vertexTripleParity a b c = vertexTripleParity b a c :=
    vertexTripleParity_swap_first_two a b c
  have h2 : vertexTripleParity a b c = vertexTripleParity a c b :=
    vertexTripleParity_swap_last_two a b c
  have h3 : vertexTripleParity a b c = vertexTripleParity b c a :=
    h1.trans (vertexTripleParity_swap_last_two b a c)
  have h4 : vertexTripleParity a b c = vertexTripleParity c a b :=
    h2.trans (vertexTripleParity_swap_first_two a c b)
  have h5 : vertexTripleParity a b c = vertexTripleParity c b a :=
    h3.trans (vertexTripleParity_swap_first_two b c a)
  rcases ha with ha | ha | ha <;>
    rcases hb with hb | hb | hb <;>
    rcases hc with hc | hc | hc <;>
    grind

end EPPAReducts.TwoGraphs
