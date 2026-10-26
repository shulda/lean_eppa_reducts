import EPPAReducts.BoundedEquivalence.OrderedColourTranslationFixed
import EPPAReducts.BoundedEquivalence.OrderedCoreColourClasses

/-!
# The explicit cyclic core acts by a nonzero class translation

On every injective ordered r-tuple supported on the core, the
vertex translation x ↦ x+1 increases the total core/exterior
auxiliary colour by one. This is the concrete premise needed by
the abstract core-to-witness class-action theorem.
-/

namespace EPPAReducts.BoundedEquivalence

/-- The unit cyclic translation viewed as a genuine permutation. -/
def orderedUnitCorePerm (N : ℕ) : Equiv.Perm (ZMod N) :=
  orderedColourTranslationPerm (1 : ZMod N)

/-- Translation of core vertices agrees with tuplewise additive
translation; the chosen orientation of multiplication is explicit. -/
theorem orderedUnitCorePerm_on_tuple
    {N r : ℕ} (t : InjectiveTuples (ZMod N) r) :
    permuteOrderedTuple (orderedUnitCorePerm N) t =
      translateInjectiveTuple (1 : ZMod N) t := by
  apply Subtype.ext
  funext j
  change t.val j + (1 : ZMod N) = (1 : ZMod N) + t.val j
  exact add_comm _ _

/-- On ordered core tuples of positive length, applying the core
translation to each vertex adds one to the total auxiliary colour.
This is independent of all external vertices. -/
theorem orderedCoreExteriorColour_on_core_shift
    (m N r : ℕ) (hmN : m ∣ N) (hr : 1 < r)
    (t : InjectiveTuples (ZMod N) r) :
    orderedCoreExteriorColour m N r hmN hr
        (fun j => Sum.inl
          ((orderedUnitCorePerm N) (t.val j))) =
      orderedCoreExteriorColour m N r hmN hr
        (fun j => Sum.inl (t.val j)) + 1 := by
  let p := orderedUnitCorePerm N
  have hp : permuteOrderedTuple p t =
      translateInjectiveTuple (1 : ZMod N) t :=
    orderedUnitCorePerm_on_tuple t
  calc
    orderedCoreExteriorColour m N r hmN hr
        (fun j => Sum.inl (p (t.val j))) =
      orderedTupleFirstCoordinateColour hmN (Nat.zero_lt_of_lt hr)
        (permuteOrderedTuple p t) :=
      orderedCoreExteriorColour_on_core m N r hmN hr _
    _ = orderedTupleFirstCoordinateColour hmN (Nat.zero_lt_of_lt hr)
        (translateInjectiveTuple 1 t) := by rw [hp]
    _ = orderedTupleFirstCoordinateColour hmN (Nat.zero_lt_of_lt hr) t + 1 :=
      orderedTupleFirstCoordinateColour_shift hmN (Nat.zero_lt_of_lt hr) t
    _ = orderedCoreExteriorColour m N r hmN hr
        (fun j => Sum.inl (t.val j)) + 1 := by
      rw [orderedCoreExteriorColour_on_core m N r hmN hr t]

end EPPAReducts.BoundedEquivalence
