import EPPAReducts.BoundedEquivalence.ExtendLabels
import Mathlib.Data.Fintype.EquivFin

/-!
# Extension of all realized auxiliary labels over finite colour sets

A presentation of a finite unlabelled equivalence by a finite set
of numerical class names is uniquely determined by the names on an
induced old core realizing *every* class. No names occur in the
language, and this module does not assume that automorphisms fix the
chosen names.

The original helper specialized to Fin m. This version applies
equally to ZMod m and avoids repeatedly converting between them.
-/

namespace EPPAReducts.BoundedEquivalence

universe u v w

/-- If both auxiliary colourings use the same finite set of colours,
the old colouring realizes all colours, and equality of old colours
is precisely equality of restricted new colours, then every new
colour class already meets the old carrier. -/
theorem every_finite_class_meets_realized_core
    {α : Type u} {β : Type v} {κ : Type w} [Finite κ]
    (ι : α → β) (fA : α → κ) (fB₀ : β → κ)
    (hA : Function.Surjective fA)
    (hKernel : ∀ a a' : α,
      fA a = fA a' ↔ fB₀ (ι a) = fB₀ (ι a')) :
    ∀ b : β, ∃ a : α, fB₀ (ι a) = fB₀ b := by
  classical
  let s : κ → α := fun c => Classical.choose (hA c)
  have hs (c : κ) : fA (s c) = c :=
    Classical.choose_spec (hA c)
  let u : κ → κ := fun c => fB₀ (ι (s c))
  have hu : Function.Injective u := by
    intro c d hcd
    have hEq : fA (s c) = fA (s d) :=
      (hKernel (s c) (s d)).mpr hcd
    calc
      c = fA (s c) := (hs c).symm
      _ = fA (s d) := hEq
      _ = d := hs d
  have hSurj : Function.Surjective u :=
    Finite.surjective_of_injective hu
  intro b
  obtain ⟨c, hc⟩ := hSurj (fB₀ b)
  exact ⟨s c, hc⟩

/-- The unique colouring of a finite-class extension that induces
the same unlabelled equivalence and agrees exactly with the
auxiliary names on the old fully realised core. -/
theorem unique_extension_colours_of_finite_realized_core
    {α : Type u} {β : Type v} {κ : Type w} [Finite κ]
    (ι : α → β) (fA : α → κ) (fB₀ : β → κ)
    (hA : Function.Surjective fA)
    (hKernel : ∀ a a' : α,
      fA a = fA a' ↔ fB₀ (ι a) = fB₀ (ι a')) :
    ∃! fB : β → κ,
      (∀ a, fB (ι a) = fA a) ∧
      (∀ b c, fB b = fB c ↔ fB₀ b = fB₀ c) :=
  unique_extend_labels_from_core ι fA fB₀
    (every_finite_class_meets_realized_core ι fA fB₀ hA hKernel)
    hKernel

end EPPAReducts.BoundedEquivalence
