import Mathlib.Logic.Equiv.Defs

/-!
# Auxiliary class names are unique up to permutation

These lemmas support the negative EPPA argument for **unlabelled**
equivalence classes. Auxiliary numerical names are not relation
symbols: any isomorphism preserving the equality of class names may
permute all names.

The proof uses only surjectivity and equality of the two kernels; it
does not assume that an automorphism preserves the numerical names.
-/

namespace EPPAReducts.BoundedEquivalence

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- Two surjective presentations of the same equivalence relation
are related by exactly one bijection of their sets of class names. -/
theorem unique_label_equiv
    (f : α → β) (g : α → γ)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hkernel : ∀ x y, f x = f y ↔ g x = g y) :
    ∃! e : β ≃ γ, ∀ x, e (f x) = g x := by
  classical
  let s : β → α := fun b => Classical.choose (hf b)
  have hs (b : β) : f (s b) = b := Classical.choose_spec (hf b)
  let h : β → γ := fun b => g (s b)
  have hh (x : α) : h (f x) = g x := by
    change g (s (f x)) = g x
    exact (hkernel (s (f x)) x).mp (hs (f x))
  have hinj : Function.Injective h := by
    intro b c hbc
    have h' : f (s b) = f (s c) :=
      (hkernel (s b) (s c)).mpr hbc
    calc
      b = f (s b) := (hs b).symm
      _ = f (s c) := h'
      _ = c := hs c
  have hsurj : Function.Surjective h := by
    intro y
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨f x, hh x⟩
  let e : β ≃ γ := Equiv.ofBijective h ⟨hinj, hsurj⟩
  refine ⟨e, ?_, ?_⟩
  · intro x
    exact hh x
  · intro e' he'
    apply Equiv.ext
    intro b
    obtain ⟨x, rfl⟩ := hf b
    exact (he' x).trans (hh x).symm

/-- A permutation preserving *equality* of auxiliary class names
induces a unique permutation of the class names themselves. -/
theorem unique_label_action
    (f : α → β) (hf : Function.Surjective f)
    (p : α ≃ α)
    (hkernel : ∀ x y, f x = f y ↔ f (p x) = f (p y)) :
    ∃! σ : Equiv.Perm β, ∀ x, σ (f x) = f (p x) := by
  let g : α → β := fun x => f (p x)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    refine ⟨p.symm x, ?_⟩
    simp only [g, p.apply_symm_apply]
  exact unique_label_equiv f g hf hg hkernel

end EPPAReducts.BoundedEquivalence
