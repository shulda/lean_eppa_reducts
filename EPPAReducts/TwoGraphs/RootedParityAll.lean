import EPPAReducts.TwoGraphs.RootedParityAway

/-!
# Rooted parity reconstruction for all genuine triples

The four-point XOR equation handles triples disjoint from the root.
If the root is one of the three vertices, the other two root triples
are degenerate and hence false by the exact onlyTriples axiom.

This module combines these cases, without assuming an arbitrary
graph representative or weakening the human-facing two-graph API.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- Cyclically permuting an unordered triple changes nothing. -/
theorem triple_cycle {V : Type} (a b c : V) :
    triple a b c = triple b c a := by
  classical
  apply Finset.ext
  intro v
  simp only [triple, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- A triple with any repeated vertex has false two-graph indicator. -/
theorem twoGraph_triple_false_of_repeat
    {V : Type} (A : TwoGraph V) (a b c : V)
    (h : a = b ∨ a = c ∨ b = c) :
    A.isTriple (triple a b c) = false := by
  classical
  have hcard : (triple a b c).card ≠ 3 := by
    rcases h with h | h | h
    · subst b
      by_cases hac : a = c <;> simp [triple, hac]
    · subst c
      by_cases hab : a = b <;> simp [triple, hab]
    · subst c
      by_cases hab : a = b <;> simp [triple, hab]
  cases hv : A.isTriple (triple a b c) with
  | false => rfl
  | true => exact False.elim (hcard (A.onlyTriples _ hv))

/-- On distinct triples, the original relation is exactly the
Boolean triangle boundary of its rooted edge indicators. This
includes triples containing the chosen root. -/
theorem twoGraph_rootedParity_distinct
    {V : Type} (A : TwoGraph V) (o x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    A.isTriple (triple x y z) =
      Bool.xor
        (Bool.xor (A.isTriple (triple o x y))
          (A.isTriple (triple o y z)))
        (A.isTriple (triple o z x)) := by
  classical
  by_cases hox : o = x
  · subst x
    have hfirst : A.isTriple (triple o o y) = false :=
      twoGraph_triple_false_of_repeat A o o y (Or.inl rfl)
    have hlast : A.isTriple (triple o z o) = false :=
      twoGraph_triple_false_of_repeat A o z o (Or.inr (Or.inl rfl))
    simp [hfirst, hlast]
  by_cases hoy : o = y
  · subst y
    have hfirst : A.isTriple (triple o x o) = false :=
      twoGraph_triple_false_of_repeat A o x o (Or.inr (Or.inl rfl))
    have hsecond : A.isTriple (triple o o z) = false :=
      twoGraph_triple_false_of_repeat A o o z (Or.inl rfl)
    rw [triple_cycle x o z]
    simp [hfirst, hsecond]
  by_cases hoz : o = z
  · subst z
    have hsecond : A.isTriple (triple o y o) = false :=
      twoGraph_triple_false_of_repeat A o y o (Or.inr (Or.inl rfl))
    have hlast : A.isTriple (triple o o x) = false :=
      twoGraph_triple_false_of_repeat A o o x (Or.inl rfl)
    rw [triple_cycle o x y]
    simp [hsecond, hlast]
  exact twoGraph_rootedParity_away A o x y z hox hoy hoz hxy hxz hyz

end EPPAReducts.TwoGraphs
