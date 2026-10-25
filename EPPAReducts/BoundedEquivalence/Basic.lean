import Mathlib.Data.Finset.Card

/-!
# Bounded equivalence relations on tuples and subsets

The eventual negative theorem concerns induced partial isomorphisms of these
structures. In particular, colours are *not* named in the language: an
automorphism may permute their equivalence classes.
-/

namespace EPPAReducts.BoundedEquivalence

/-- Unordered subsets having exactly `r` elements. -/
abbrev RSubsets (α : Type*) (r : ℕ) := { s : Finset α // s.card = r }

/-- Ordered, injective `r`-tuples. -/
abbrev InjectiveTuples (α : Type*) (r : ℕ) :=
  { t : Fin r → α // Function.Injective t }

/-- The quotient of `E` has at most `m` classes, presented by an unlabelled
partition that admits a colouring by `Fin m`. -/
def HasAtMostClasses {β : Type*} (E : Setoid β) (m : ℕ) : Prop :=
  ∃ colouring : β → Fin m,
    ∀ x y, E.r x y ↔ colouring x = colouring y

end EPPAReducts.BoundedEquivalence
