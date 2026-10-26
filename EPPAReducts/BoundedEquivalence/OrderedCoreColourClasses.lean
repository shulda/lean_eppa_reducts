import EPPAReducts.BoundedEquivalence.OrderedCoreExteriorColour
import EPPAReducts.BoundedEquivalence.OrderedTupleKernelPartial

/-!
# Unlabelled ordered obstruction: realisation of every class on its core

On a tuple of old/core vertices, the explicit total colouring agrees
exactly with the first-coordinate cyclic colouring. Its image is all
of ZMod m once the core contains an injective r-tuple and m|N.
Thus the induced equivalence relation has all m classes already
present on the core, and any extension with at most m classes has
no additional classes.

The numerical labels are auxiliary only; the structure is the kernel.
-/

namespace EPPAReducts.BoundedEquivalence

/-- On core tuples, the total core/exterior colouring reduces to the
first-coordinate colouring already proved surjective. -/
theorem orderedCoreExteriorColour_on_core
    (m N r : ℕ) (hmN : m ∣ N) (hr : 1 < r)
    (t : InjectiveTuples (ZMod N) r) :
    orderedCoreExteriorColour m N r hmN hr
      (fun i => Sum.inl (t.val i)) =
    orderedTupleFirstCoordinateColour hmN (Nat.zero_lt_of_lt hr) t := by
  classical
  simp [orderedCoreExteriorColour, orderedCoreBase,
    orderedExteriorCorrection, orderedTupleFirstCoordinateColour]

/-- The unlabelled kernel of the actual exterior colouring on ordered
injective r-tuples. -/
noncomputable def orderedCoreExteriorKernel
    (m N r : ℕ) (hmN : m ∣ N) (hr : 1 < r) :
    Setoid (InjectiveTuples (Sum (ZMod N) (Fin r)) r) :=
  orderedTupleKernelSetoid
    (fun t : InjectiveTuples (Sum (ZMod N) (Fin r)) r =>
      orderedCoreExteriorColour m N r hmN hr t.val)

/-- The total finite structure has at most m *unlabelled* classes,
without requiring the colouring to be part of its signature. -/
theorem orderedCoreExteriorKernel_hasAtMostClasses
    (m N r : ℕ) (hm : 0 < m)
    (hmN : m ∣ N) (hr : 1 < r) :
    HasAtMostClasses (orderedCoreExteriorKernel m N r hmN hr) m :=
  colourKernelSetoid_hasAtMostClasses m hm
    (fun t : InjectiveTuples (Sum (ZMod N) (Fin r)) r =>
      orderedCoreExteriorColour m N r hmN hr t.val)

/-- For S=ZMod(m*r), the full old-core restriction of the total
colouring is surjective onto ZMod m. This is the exact source of all
m inequivalent tuples which controls class actions in every extension. -/
theorem orderedCyclicCoreExteriorColour_surjective
    (m r : ℕ) (hm : 0 < m) (hr : 1 < r) :
    Function.Surjective
      (fun t : InjectiveTuples (ZMod (m * r)) r =>
        orderedCoreExteriorColour m (m * r) r
          (show m ∣ m * r from ⟨r, rfl⟩) hr
          (fun j => Sum.inl (t.val j))) := by
  have hs := orderedCyclicCoreColour_surjective
    m r hm (Nat.zero_lt_of_lt hr)
  intro c
  obtain ⟨t, ht⟩ := hs c
  refine ⟨t, ?_⟩
  rw [orderedCoreExteriorColour_on_core]
  exact ht

end EPPAReducts.BoundedEquivalence
