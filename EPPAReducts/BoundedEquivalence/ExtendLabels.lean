import Mathlib.Data.Fintype.Card

/-!
# Canonical extension of unlabelled equivalence-class names

If every class of an extension B meets the old core A, names for the
classes on A extend in a unique way to B. No relation symbol naming a
class is introduced: these functions are auxiliary presentations.
-/

namespace EPPAReducts.BoundedEquivalence

universe u v w
variable {α : Type u} {β : Type v} {κ : Type w}

/-- If every class of B meets A and the two auxiliary presentations agree
on equality of old classes, the old class names extend uniquely to B.
This lemma does not need finiteness after the class-representative
hypothesis has been established. -/
theorem unique_extend_labels_from_core
    (ι : α → β) (fA : α → κ) (fB₀ : β → κ)
    (hCore : ∀ b : β, ∃ a : α, fB₀ (ι a) = fB₀ b)
    (hKernel : ∀ a a' : α,
      fA a = fA a' ↔ fB₀ (ι a) = fB₀ (ι a')) :
    ∃! fB : β → κ,
      (∀ a, fB (ι a) = fA a) ∧
      (∀ b c, fB b = fB c ↔ fB₀ b = fB₀ c) := by
  classical
  let rep : β → α := fun b => Classical.choose (hCore b)
  have hrep (b : β) : fB₀ (ι (rep b)) = fB₀ b :=
    Classical.choose_spec (hCore b)
  let fB : β → κ := fun b => fA (rep b)
  have hExt (a : α) : fB (ι a) = fA a := by
    change fA (rep (ι a)) = fA a
    exact (hKernel (rep (ι a)) a).mpr (hrep (ι a))
  have hEq (b c : β) : fB b = fB c ↔ fB₀ b = fB₀ c := by
    change fA (rep b) = fA (rep c) ↔ fB₀ b = fB₀ c
    rw [hKernel (rep b) (rep c), hrep b, hrep c]
  refine ⟨fB, ⟨hExt, hEq⟩, ?_⟩
  intro g hg
  funext b
  obtain ⟨a, ha⟩ := hCore b
  calc
    g b = g (ι a) := (hg.2 b (ι a)).mpr ha.symm
    _ = fA a := hg.1 a
    _ = fB (ι a) := (hExt a).symm
    _ = fB b := ((hEq b (ι a)).mpr ha.symm).symm


/-- Suppose the old carrier realizes all m classes, and an auxiliary
Fin m-presentation of the extension induces exactly the same equivalence
on old points. Then every class of the extension meets the old carrier.
The key finite step is that an injective self-map of Fin m is surjective. -/
theorem all_extension_classes_meet_core
    (m : ℕ) (ι : α → β)
    (fA : α → Fin m) (fB₀ : β → Fin m)
    (hA : Function.Surjective fA)
    (hKernel : ∀ a a' : α,
      fA a = fA a' ↔ fB₀ (ι a) = fB₀ (ι a')) :
    ∀ b : β, ∃ a : α, fB₀ (ι a) = fB₀ b := by
  classical
  let s : Fin m → α := fun c => Classical.choose (hA c)
  have hs (c : Fin m) : fA (s c) = c :=
    Classical.choose_spec (hA c)
  let u : Fin m → Fin m := fun c => fB₀ (ι (s c))
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

/-- Canonical and unique recovery of the auxiliary labels on the whole
finite-class extension from a fully realized old core. This is the
class-naming interface used by the negative EPPA obstruction. -/
theorem unique_extend_labels_of_bounded_classes
    (m : ℕ) (ι : α → β)
    (fA : α → Fin m) (fB₀ : β → Fin m)
    (hA : Function.Surjective fA)
    (hKernel : ∀ a a' : α,
      fA a = fA a' ↔ fB₀ (ι a) = fB₀ (ι a')) :
    ∃! fB : β → Fin m,
      (∀ a, fB (ι a) = fA a) ∧
      (∀ b c, fB b = fB c ↔ fB₀ b = fB₀ c) :=
  unique_extend_labels_from_core ι fA fB₀
    (all_extension_classes_meet_core m ι fA fB₀ hA hKernel)
    hKernel

end EPPAReducts.BoundedEquivalence
