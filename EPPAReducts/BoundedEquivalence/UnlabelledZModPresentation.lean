import EPPAReducts.BoundedEquivalence.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card

/-!
# Auxiliary colours and genuinely unlabelled equivalence classes

The intended language only knows equality of equivalence classes.
Numerical labels (Fin m and ZMod m) are presentations, not relation
symbols. These lemmas certify the exact equivalence of the two
presentations for m>0 and show that adding a constant shift to every
auxiliary colour preserves the unlabelled equivalence.
-/

namespace EPPAReducts.BoundedEquivalence

universe u v

/-- The genuine unlabelled equivalence relation induced by an
auxiliary colouring. It remembers only equality of colour values. -/
def colourKernelSetoid {α : Type u} {κ : Type v} (f : α → κ) :
    Setoid α where
  r x y := f x = f y
  iseqv := ⟨fun _ => rfl,
    fun _ _ h => h.symm,
    fun _ _ _ hxy hyz => hxy.trans hyz⟩

@[simp] theorem colourKernelSetoid_rel
    {α : Type u} {κ : Type v} (f : α → κ) (x y : α) :
    (colourKernelSetoid f).r x y ↔ f x = f y := Iff.rfl

/-- The existing at-most-m-class API uses Fin m presentations.
For m>0, this is equivalent to admitting an auxiliary ZMod m
presentation, including the at-most rather than exactly m case. -/
theorem hasAtMostClasses_iff_zmod_presentation
    {α : Type u} (m : ℕ) (hm : 0 < m) (E : Setoid α) :
    HasAtMostClasses E m ↔
      ∃ f : α → ZMod m, ∀ x y, E.r x y ↔ f x = f y := by
  classical
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let e : Fin m ≃ ZMod m :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_fin, ZMod.card])
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun x => e (f x), ?_⟩
    intro x y
    constructor
    · intro h
      exact congrArg e ((hf x y).mp h)
    · intro h
      exact (hf x y).mpr (e.injective h)
  · rintro ⟨f, hf⟩
    refine ⟨fun x => e.symm (f x), ?_⟩
    intro x y
    constructor
    · intro h
      exact congrArg e.symm ((hf x y).mp h)
    · intro h
      exact (hf x y).mpr (e.symm.injective h)

/-- In particular, any ZMod m colouring, even a nonsurjective one,
gives an equivalence relation with at most m unlabelled classes. -/
theorem colourKernelSetoid_hasAtMostClasses
    {α : Type u} (m : ℕ) (hm : 0 < m)
    (f : α → ZMod m) :
    HasAtMostClasses (colourKernelSetoid f) m := by
  apply (hasAtMostClasses_iff_zmod_presentation m hm
    (colourKernelSetoid f)).mpr
  exact ⟨f, fun _ _ => Iff.rfl⟩

/-- A permutation shifting ALL auxiliary colours by one fixed
constant preserves equality of the colours and therefore is an
automorphism of the actual unlabelled equivalence relation.
Surjectivity is not needed for this direction. -/
theorem colourKernelSetoid_preserved_of_constant_shift
    {α : Type u} {m : ℕ}
    (f : α → ZMod m) (p : Equiv.Perm α) (δ : ZMod m)
    (hshift : ∀ x, f (p x) = f x + δ) :
    ∀ x y, (colourKernelSetoid f).r x y ↔
      (colourKernelSetoid f).r (p x) (p y) := by
  intro x y
  change f x = f y ↔ f (p x) = f (p y)
  rw [hshift x, hshift y]
  constructor
  · intro h
    exact congrArg (fun c => c + δ) h
  · intro h
    exact add_right_cancel h

end EPPAReducts.BoundedEquivalence
