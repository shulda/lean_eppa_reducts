import EPPAReducts.TwoGraphs.ValuationTwoGraph

/-!
# Evaluating the unordered triple relation on any three vertices

The existing bridge handled three pairwise distinct vertices.
This lemma removes that restriction by using the separately proved
fact that the ternary valuation parity vanishes on repeated vertices.
It is the final local bridge required to turn a parity-preserving
vertex permutation into an automorphism of the literal two-graph API.
-/

namespace EPPAReducts.TwoGraphs

variable {X : Type} [DecidableEq (ValuationVertex X)]

/-- The unordered valuation triple predicate agrees with its ternary
formula even on tuples with repeated vertices. -/
theorem unorderedTripleParity_on_any_three
    (a b c : ValuationVertex X) :
    unorderedTripleParity ({a, b, c} : Finset (ValuationVertex X)) =
      vertexTripleParity a b c := by
  classical
  by_cases hab : a = b
  · subst b
    have hle : ({a, a, c} : Finset (ValuationVertex X)).card ≤ 2 := by
      simpa using (Finset.card_le_two (a := a) (b := c))
    have hn : ({a, a, c} : Finset (ValuationVertex X)).card ≠ 3 := by
      exact Nat.ne_of_lt (lt_of_le_of_lt hle (by decide))
    have hleft :
        unorderedTripleParity ({a, a, c} : Finset (ValuationVertex X)) = false := by
      simp only [unorderedTripleParity, dif_neg hn]
    exact hleft.trans (vertexTripleParity_duplicate_first a c).symm
  by_cases hac : a = c
  · subst c
    have heq : ({a, b, a} : Finset (ValuationVertex X)) = {a, b} := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hle : ({a, b, a} : Finset (ValuationVertex X)).card ≤ 2 := by
      rw [heq]
      exact Finset.card_le_two
    have hn : ({a, b, a} : Finset (ValuationVertex X)).card ≠ 3 := by
      exact Nat.ne_of_lt (lt_of_le_of_lt hle (by decide))
    have hleft :
        unorderedTripleParity ({a, b, a} : Finset (ValuationVertex X)) = false := by
      simp only [unorderedTripleParity, dif_neg hn]
    calc
      unorderedTripleParity ({a, b, a} : Finset (ValuationVertex X)) = false := hleft
      _ = vertexTripleParity a a b := (vertexTripleParity_duplicate_first a b).symm
      _ = vertexTripleParity a b a :=
        (vertexTripleParity_swap_last_two a b a).symm
  by_cases hbc : b = c
  · subst c
    have hle : ({a, b, b} : Finset (ValuationVertex X)).card ≤ 2 := by
      simpa using (Finset.card_le_two (a := a) (b := b))
    have hn : ({a, b, b} : Finset (ValuationVertex X)).card ≠ 3 := by
      exact Nat.ne_of_lt (lt_of_le_of_lt hle (by decide))
    have hleft :
        unorderedTripleParity ({a, b, b} : Finset (ValuationVertex X)) = false := by
      simp only [unorderedTripleParity, dif_neg hn]
    exact hleft.trans (vertexTripleParity_duplicate_last a b).symm
  exact unorderedTripleParity_on_three a b c hab hac hbc

end EPPAReducts.TwoGraphs
