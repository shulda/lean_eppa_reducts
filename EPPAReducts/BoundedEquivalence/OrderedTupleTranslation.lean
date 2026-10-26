import EPPAReducts.BoundedEquivalence.Basic
import Mathlib.Algebra.Group.Defs

/-!
# Free translations of nonempty ordered injective tuples

The negative EPPA obstruction for ordered tuples uses cyclic
translations of a finite additive group. These lemmas isolate the
essential freeness, independently of the particular cyclic group,
the number of colours, or any named colouring.

Positive length is essential: the empty tuple is fixed by all shifts.
-/

namespace EPPAReducts.BoundedEquivalence

variable {G : Type} [AddGroup G] {r : ℕ}

/-- Translate every entry of an ordered injective tuple by the same
group element. Translation preserves injectivity. -/
def translateInjectiveTuple (a : G)
    (t : InjectiveTuples G r) : InjectiveTuples G r :=
  ⟨fun i => a + t.val i, by
    intro i j hij
    exact t.property (add_left_cancel hij)⟩

/-- Translation by zero acts trivially. -/
theorem translateInjectiveTuple_zero (t : InjectiveTuples G r) :
    translateInjectiveTuple (0 : G) t = t := by
  apply Subtype.ext
  funext i
  exact zero_add (t.val i)

/-- Sequential translation is translation by the sum, in the
corresponding (left-action) order. -/
theorem translateInjectiveTuple_add (a b : G)
    (t : InjectiveTuples G r) :
    translateInjectiveTuple (a + b) t =
      translateInjectiveTuple a (translateInjectiveTuple b t) := by
  apply Subtype.ext
  funext i
  exact add_assoc a b (t.val i)

/-- Opposite translations cancel, including for zero-length tuples. -/
theorem translateInjectiveTuple_neg_cancel (a : G)
    (t : InjectiveTuples G r) :
    translateInjectiveTuple (-a) (translateInjectiveTuple a t) = t := by
  rw [← translateInjectiveTuple_add, neg_add_cancel,
    translateInjectiveTuple_zero]

/-- A translation fixing one nonempty ordered tuple must be zero.
Only the first coordinate is used, so this also holds without
injectivity; the tuple API retains the actual intended language. -/
theorem translateInjectiveTuple_fixed_implies_zero
    (hr : 0 < r) (a : G) (t : InjectiveTuples G r)
    (h : translateInjectiveTuple a t = t) : a = 0 := by
  let i : Fin r := ⟨0, hr⟩
  have hi : a + t.val i = t.val i := by
    have hp := congrArg (fun u : InjectiveTuples G r => u.val i) h
    exact hp
  have hzero : a + t.val i = (0 : G) + t.val i := by
    simpa only [zero_add] using hi
  exact add_right_cancel hzero

/-- Exact free-action characterization for positive-length
ordered tuples. -/
theorem translateInjectiveTuple_fixed_iff
    (hr : 0 < r) (a : G) (t : InjectiveTuples G r) :
    translateInjectiveTuple a t = t ↔ a = 0 := by
  constructor
  · exact translateInjectiveTuple_fixed_implies_zero hr a t
  · intro ha
    subst a
    exact translateInjectiveTuple_zero t

/-- Translating a fixed nonempty tuple gives different tuples for
different group elements. -/
theorem translateInjectiveTuple_injective_of_pos
    (hr : 0 < r) (t : InjectiveTuples G r) :
    Function.Injective (fun a : G => translateInjectiveTuple a t) := by
  intro a b h
  let i : Fin r := ⟨0, hr⟩
  have hi := congrArg (fun u : InjectiveTuples G r => u.val i) h
  change a + t.val i = b + t.val i at hi
  exact add_right_cancel hi

/-- The orbit of an ordered injective tuple under all translations
of the finite group. -/
noncomputable def translatedTupleOrbit [Fintype G]
    (t : InjectiveTuples G r) : Finset (InjectiveTuples G r) := by
  classical
  exact (Finset.univ : Finset G).image
    (fun a => translateInjectiveTuple a t)

/-- Every positive-length ordered tuple has a translation orbit
with exactly as many elements as the ambient finite group. This is
the cardinality statement needed for cyclic-orbit colourings. -/
theorem translatedTupleOrbit_card [Fintype G]
    (hr : 0 < r) (t : InjectiveTuples G r) :
    (translatedTupleOrbit t).card = Fintype.card G := by
  classical
  change ((Finset.univ : Finset G).image
    (fun a => translateInjectiveTuple a t)).card = Fintype.card G
  simpa only [Finset.card_univ] using
    (Finset.card_image_of_injective (Finset.univ : Finset G)
      (translateInjectiveTuple_injective_of_pos hr t))

end EPPAReducts.BoundedEquivalence
