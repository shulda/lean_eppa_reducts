import EPPAReducts.BoundedEquivalence.OrderedCyclicCore
import Mathlib.Tactic.Abel

/-!
# Explicit colours on a core with external vertices

The intended finite obstruction has vertex set
  Sum (ZMod N) (Fin r).
All r-tuples supported on the core and at most one selected external
vertex must change colour by +1 when the core is translated by +1.

Instead of deleting the external coordinate and choosing an ordering
of the remaining tuple, we use the first available core entry among
the first two coordinates, plus a position-dependent correction.
For injective r-tuples supported on the core and one external vertex
(r >= 2), such an entry always exists.

The output colours are auxiliary; only equality of colours will enter
the unlabelled equivalence structure.
-/

namespace EPPAReducts.BoundedEquivalence

/-- Shift the cyclic core by one and leave every external vertex fixed. -/
def orderedCoreShift {N r : ℕ}
    (v : Sum (ZMod N) (Fin r)) : Sum (ZMod N) (Fin r) :=
  match v with
  | .inl x => .inl (x + 1)
  | .inr i => .inr i

@[simp] theorem orderedCoreShift_eq_inr_iff {N r : ℕ}
    (v : Sum (ZMod N) (Fin r)) (j : Fin r) :
    orderedCoreShift v = Sum.inr j ↔ v = Sum.inr j := by
  cases v <;> simp [orderedCoreShift]

/-- The base colour is the residue of the first core coordinate
among positions zero and one. When neither position belongs to the
core, the value is irrelevant for the intended induced substructures. -/
def orderedCoreBase (m N r : ℕ)
    (hmN : m ∣ N) (hr : 1 < r)
    (t : Fin r → Sum (ZMod N) (Fin r)) : ZMod m :=
  match t (⟨0, Nat.zero_lt_of_lt hr⟩ : Fin r) with
  | .inl x => (ZMod.castHom hmN (ZMod m)) x
  | .inr _ =>
      match t (⟨1, hr⟩ : Fin r) with
      | .inl x => (ZMod.castHom hmN (ZMod m)) x
      | .inr _ => 0

/-- A correction of one records the occurrence of an external
vertex in the position having the same label as that vertex. -/
noncomputable def orderedExteriorCorrection
    (m : ℕ) {N r : ℕ}
    (t : Fin r → Sum (ZMod N) (Fin r)) : ZMod m :=
  if ∃ j : Fin r, t j = Sum.inr j then 1 else 0

/-- The actual auxiliary colouring for all ordered tuples on
the core-plus-exterior carrier. No injectivity is needed merely to
define this function; it will be restricted to injective tuples. -/
noncomputable def orderedCoreExteriorColour
    (m N r : ℕ) (hmN : m ∣ N) (hr : 1 < r)
    (t : Fin r → Sum (ZMod N) (Fin r)) : ZMod m :=
  orderedCoreBase m N r hmN hr t +
    orderedExteriorCorrection m t

/-- The external-position correction is invariant under shifting
the entire core. -/
theorem orderedExteriorCorrection_shift
    (m : ℕ) {N r : ℕ}
    (t : Fin r → Sum (ZMod N) (Fin r)) :
    orderedExteriorCorrection m (fun j => orderedCoreShift (t j)) =
      orderedExteriorCorrection m t := by
  classical
  have hh :
      (∃ j : Fin r, orderedCoreShift (t j) = Sum.inr j) ↔
        (∃ j : Fin r, t j = Sum.inr j) := by
    simp only [orderedCoreShift_eq_inr_iff]
  change
    (if ∃ j : Fin r, orderedCoreShift (t j) = Sum.inr j then
      (1 : ZMod m) else 0) =
    (if ∃ j : Fin r, t j = Sum.inr j then
      (1 : ZMod m) else 0)
  by_cases h : ∃ j : Fin r, t j = Sum.inr j
  · have h' : ∃ j : Fin r, orderedCoreShift (t j) = Sum.inr j :=
      hh.mpr h
    simp only [if_pos h, if_pos h']
  · have h' : ¬ ∃ j : Fin r, orderedCoreShift (t j) = Sum.inr j :=
      fun hshift => h (hh.mp hshift)
    simp only [if_neg h, if_neg h']

/-- If one of the first two tuple positions belongs to the core,
shifting every core coordinate increases the base colour by one. -/
theorem orderedCoreBase_shift
    (m N r : ℕ) (hmN : m ∣ N) (hr : 1 < r)
    (t : Fin r → Sum (ZMod N) (Fin r))
    (hcore :
      (∃ x : ZMod N,
        t (⟨0, Nat.zero_lt_of_lt hr⟩ : Fin r) = Sum.inl x) ∨
      (∃ x : ZMod N,
        t (⟨1, hr⟩ : Fin r) = Sum.inl x)) :
    orderedCoreBase m N r hmN hr
        (fun j => orderedCoreShift (t j)) =
      orderedCoreBase m N r hmN hr t + 1 := by
  have hmap (x : ZMod N) :
      (ZMod.castHom hmN (ZMod m)) (x + 1) =
        (ZMod.castHom hmN (ZMod m)) x + 1 := by
    simp only [ZMod.castHom_apply, ZMod.cast_add hmN, ZMod.cast_one hmN]
  rcases hcore with ⟨x, hx⟩ | ⟨x, hx⟩
  · simpa [orderedCoreBase, orderedCoreShift, hx] using hmap x
  · cases hzero :
        t (⟨0, Nat.zero_lt_of_lt hr⟩ : Fin r) with
    | inl y =>
        simpa [orderedCoreBase, orderedCoreShift, hzero] using hmap y
    | inr i =>
        simpa [orderedCoreBase, orderedCoreShift, hzero, hx] using hmap x

/-- The complete auxiliary colour changes by +1 whenever at least
one of the first two positions is occupied by a core vertex. -/
theorem orderedCoreExteriorColour_shift
    (m N r : ℕ) (hmN : m ∣ N) (hr : 1 < r)
    (t : Fin r → Sum (ZMod N) (Fin r))
    (hcore :
      (∃ x : ZMod N,
        t (⟨0, Nat.zero_lt_of_lt hr⟩ : Fin r) = Sum.inl x) ∨
      (∃ x : ZMod N,
        t (⟨1, hr⟩ : Fin r) = Sum.inl x)) :
    orderedCoreExteriorColour m N r hmN hr
        (fun j => orderedCoreShift (t j)) =
      orderedCoreExteriorColour m N r hmN hr t + 1 := by
  change
    orderedCoreBase m N r hmN hr (fun j => orderedCoreShift (t j)) +
        orderedExteriorCorrection m (fun j => orderedCoreShift (t j)) =
      (orderedCoreBase m N r hmN hr t +
        orderedExteriorCorrection m t) + 1
  rw [orderedCoreBase_shift m N r hmN hr t hcore,
    orderedExteriorCorrection_shift m t]
  abel

end EPPAReducts.BoundedEquivalence
