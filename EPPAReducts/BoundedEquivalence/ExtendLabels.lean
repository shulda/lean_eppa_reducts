import Mathlib.Logic.Equiv.Defs

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

end EPPAReducts.BoundedEquivalence
