import EPPAReducts.TwoGraphs.FourSubsetEnumeration

/-!
# Distinctness of the four unordered triples of a four-element set

These six inequalities are the hypotheses for the already certified
Boolean four-element cardinality/XOR equivalence when it is applied
to the family of three-element subsets.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {V : Type u} [DecidableEq V]

private theorem finset_ne_of_mem_not_mem
    (s t : Finset V) (x : V) (hs : x ∈ s) (ht : x ∉ t) :
    s ≠ t := by
  intro heq
  exact ht (heq ▸ hs)

/-- The four three-element subsets of four pairwise distinct vertices
are themselves pairwise distinct elements of the Finset-of-Finsets type. -/
theorem four_triple_subsets_distinct
    (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (({a, b, c} : Finset V) ≠ {a, b, d}) ∧
    (({a, b, c} : Finset V) ≠ {a, c, d}) ∧
    (({a, b, c} : Finset V) ≠ {b, c, d}) ∧
    (({a, b, d} : Finset V) ≠ {a, c, d}) ∧
    (({a, b, d} : Finset V) ≠ {b, c, d}) ∧
    (({a, c, d} : Finset V) ≠ {b, c, d}) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply finset_ne_of_mem_not_mem _ _ c (by simp)
    simp [hac.symm, hbc.symm, hcd]
  · apply finset_ne_of_mem_not_mem _ _ b (by simp)
    simp [hab.symm, hbc, hbd]
  · apply finset_ne_of_mem_not_mem _ _ a (by simp)
    simp [hab, hac, had]
  · apply finset_ne_of_mem_not_mem _ _ b (by simp)
    simp [hab.symm, hbc, hbd]
  · apply finset_ne_of_mem_not_mem _ _ a (by simp)
    simp [hab, hac, had]
  · apply finset_ne_of_mem_not_mem _ _ a (by simp)
    simp [hab, hac, had]

end EPPAReducts.TwoGraphs
