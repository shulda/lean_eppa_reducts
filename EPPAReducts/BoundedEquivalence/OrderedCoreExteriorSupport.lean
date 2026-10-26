import EPPAReducts.BoundedEquivalence.OrderedCoreExteriorColour
import EPPAReducts.BoundedEquivalence.Basic

/-!
# Exact support of ordered tuples in a core plus one external vertex

For an injective r-tuple supported on the cyclic core and one
specified external vertex (r >= 2), the first two positions cannot
both be external: they would contain the same external vertex,
violating injectivity.

This connects the certified raw shift formula to *every* tuple on
each of the induced domains used in the ordered non-EPPA obstruction.
-/

namespace EPPAReducts.BoundedEquivalence

/-- An injective tuple using only the core and at most one fixed
external vertex has a core entry in at least one of its first two
positions. -/
theorem orderedTuple_firstTwo_has_core_of_one_exterior
    {N r : ℕ} (hr : 1 < r)
    (t : InjectiveTuples (Sum (ZMod N) (Fin r)) r)
    (a : Fin r)
    (hsupp : ∀ j : Fin r, ∀ k : Fin r,
      t.val j = Sum.inr k → k = a) :
    (∃ x : ZMod N,
      t.val (⟨0, Nat.zero_lt_of_lt hr⟩ : Fin r) = Sum.inl x) ∨
    (∃ x : ZMod N,
      t.val (⟨1, hr⟩ : Fin r) = Sum.inl x) := by
  let z : Fin r := ⟨0, Nat.zero_lt_of_lt hr⟩
  let o : Fin r := ⟨1, hr⟩
  change (∃ x : ZMod N, t.val z = Sum.inl x) ∨
    (∃ x : ZMod N, t.val o = Sum.inl x)
  cases hz : t.val z with
  | inl x =>
      exact Or.inl ⟨x, hz⟩
  | inr k =>
      cases ho : t.val o with
      | inl y =>
          exact Or.inr ⟨y, ho⟩
      | inr l =>
          have hk : k = a := hsupp z k hz
          have hl : l = a := hsupp o l ho
          have hsame : t.val z = t.val o := by
            calc
              t.val z = Sum.inr k := hz
              _ = Sum.inr a := congrArg Sum.inr hk
              _ = Sum.inr l := congrArg Sum.inr hl.symm
              _ = t.val o := ho.symm
          have hzo : z = o := t.property hsame
          have hv : (0 : ℕ) = 1 := congrArg Fin.val hzo
          exact False.elim (Nat.zero_ne_one hv)

/-- Every injective r-tuple on the cyclic core plus a single fixed
external vertex has its colour increased by one under the core
translation, including the case in which that external vertex is
in the first or second position. -/
theorem orderedCoreExteriorColour_shift_of_one_external
    (m N r : ℕ) (hmN : m ∣ N) (hr : 1 < r)
    (t : InjectiveTuples (Sum (ZMod N) (Fin r)) r)
    (a : Fin r)
    (hsupp : ∀ j : Fin r, ∀ k : Fin r,
      t.val j = Sum.inr k → k = a) :
    orderedCoreExteriorColour m N r hmN hr
        (fun j => orderedCoreShift (t.val j)) =
      orderedCoreExteriorColour m N r hmN hr t.val + 1 := by
  exact orderedCoreExteriorColour_shift m N r hmN hr t.val
    (orderedTuple_firstTwo_has_core_of_one_exterior hr t a hsupp)

end EPPAReducts.BoundedEquivalence
