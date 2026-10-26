import EPPAReducts.BoundedEquivalence.OrderedTupleTranslation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel

/-!
# Explicit shift-equivariant colourings of ordered injective tuples

For the ordered-tuple negative EPPA construction, a cyclic orbit
selector is unnecessary: the first coordinate itself provides an
equivariant colour after reducing modulo m. The statements below
are auxiliary numerical colourings; the actual structures only
remember equality of colours and do not name colour classes.
-/

namespace EPPAReducts.BoundedEquivalence

/-- An auxiliary colour for each positive-length ordered injective
tuple over a cyclic group. The reduction modulo m is canonical whenever
m divides N. -/
def orderedTupleFirstCoordinateColour
    {m N r : ℕ} (hmN : m ∣ N) (hr : 0 < r)
    (t : InjectiveTuples (ZMod N) r) : ZMod m :=
  (ZMod.castHom hmN (ZMod m)) (t.val ⟨0, hr⟩)

/-- Translation of every coordinate shifts the colour by the residue
of the translating element. No orbit choices are involved. -/
theorem orderedTupleFirstCoordinateColour_translate
    {m N r : ℕ} (hmN : m ∣ N) (hr : 0 < r)
    (a : ZMod N) (t : InjectiveTuples (ZMod N) r) :
    orderedTupleFirstCoordinateColour hmN hr
        (translateInjectiveTuple a t) =
      (ZMod.castHom hmN (ZMod m)) a +
        orderedTupleFirstCoordinateColour hmN hr t := by
  change (ZMod.castHom hmN (ZMod m)) (a + t.val ⟨0, hr⟩) =
    (ZMod.castHom hmN (ZMod m)) a +
      (ZMod.castHom hmN (ZMod m)) (t.val ⟨0, hr⟩)
  exact (ZMod.castHom hmN (ZMod m)).map_add a _

/-- In particular, the canonical cyclic translation increases the
auxiliary colour by exactly one. -/
theorem orderedTupleFirstCoordinateColour_shift
    {m N r : ℕ} (hmN : m ∣ N) (hr : 0 < r)
    (t : InjectiveTuples (ZMod N) r) :
    orderedTupleFirstCoordinateColour hmN hr
        (translateInjectiveTuple (1 : ZMod N) t) =
      orderedTupleFirstCoordinateColour hmN hr t + 1 := by
  calc
    orderedTupleFirstCoordinateColour hmN hr
        (translateInjectiveTuple (1 : ZMod N) t) =
        (ZMod.castHom hmN (ZMod m)) (1 : ZMod N) +
          orderedTupleFirstCoordinateColour hmN hr t :=
      orderedTupleFirstCoordinateColour_translate hmN hr 1 t
    _ = orderedTupleFirstCoordinateColour hmN hr t + 1 := by
      rw [map_one, add_comm]

/-- If there is at least one injective tuple, the explicit cyclic
colouring uses all m colours. In particular this will apply to
r-tuples and (r-1)-tuples on a core of m*r vertices, for r,m≥2. -/
theorem orderedTupleFirstCoordinateColour_surjective
    {m N r : ℕ} (hmN : m ∣ N) (hr : 0 < r)
    [Nonempty (InjectiveTuples (ZMod N) r)] :
    Function.Surjective (orderedTupleFirstCoordinateColour hmN hr) := by
  classical
  let t : InjectiveTuples (ZMod N) r := Classical.choice inferInstance
  intro c
  obtain ⟨a, ha⟩ :=
    (ZMod.castHom_surjective hmN)
      (c - orderedTupleFirstCoordinateColour hmN hr t)
  refine ⟨translateInjectiveTuple a t, ?_⟩
  calc
    orderedTupleFirstCoordinateColour hmN hr
        (translateInjectiveTuple a t) =
        (ZMod.castHom hmN (ZMod m)) a +
          orderedTupleFirstCoordinateColour hmN hr t :=
      orderedTupleFirstCoordinateColour_translate hmN hr a t
    _ = (c - orderedTupleFirstCoordinateColour hmN hr t) +
          orderedTupleFirstCoordinateColour hmN hr t := by rw [ha]
    _ = c := sub_add_cancel _ _

/-- On (r-1)-tuples, add a positional correction recording whether
the chosen external vertex label agrees with the insertion position.
This is again an *auxiliary* colour, not a named relation symbol. -/
def orderedExteriorPositionColour
    {m N r : ℕ} (hmN : m ∣ N) (hr : 1 < r)
    (label position : Fin r)
    (t : InjectiveTuples (ZMod N) (r - 1)) : ZMod m :=
  orderedTupleFirstCoordinateColour hmN (Nat.sub_pos_of_lt hr) t +
    if label = position then 1 else 0

/-- The positional correction survives translation unchanged, so
each exterior colour still increases by one. -/
theorem orderedExteriorPositionColour_shift
    {m N r : ℕ} (hmN : m ∣ N) (hr : 1 < r)
    (label position : Fin r)
    (t : InjectiveTuples (ZMod N) (r - 1)) :
    orderedExteriorPositionColour hmN hr label position
        (translateInjectiveTuple (1 : ZMod N) t) =
      orderedExteriorPositionColour hmN hr label position t + 1 := by
  unfold orderedExteriorPositionColour
  rw [orderedTupleFirstCoordinateColour_shift]
  abel

/-- Distinct external labels give distinct functions of the
remaining tuple and insertion position: test them at the first label's
own insertion position. This is valid even for r=2. -/
theorem orderedExteriorPositionColour_distinct
    {m N r : ℕ} (hmN : m ∣ N) (hr : 1 < r)
    (hm : 2 ≤ m)
    (i j : Fin r) (hij : i ≠ j)
    (t : InjectiveTuples (ZMod N) (r - 1)) :
    orderedExteriorPositionColour hmN hr i i t ≠
      orderedExteriorPositionColour hmN hr j i t := by
  have hone : (1 : ZMod m) ≠ 0 := by
    intro hzero
    have hm1 : m = 1 := ZMod.one_eq_zero_iff.mp hzero
    have hgt : 1 < m := lt_of_lt_of_le (by decide : 1 < 2) hm
    exact (Nat.ne_of_gt hgt) hm1
  intro heq
  simp only [orderedExteriorPositionColour, if_pos rfl,
    if_neg hij.symm, add_zero] at heq
  exact hone (add_left_cancel heq)

end EPPAReducts.BoundedEquivalence
