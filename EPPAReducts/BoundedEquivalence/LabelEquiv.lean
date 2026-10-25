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

/-- Once every class name is realized, any permutation fixing the label
of every vertex must fix every class name. -/
theorem label_action_id
    (f : α → β) (hf : Function.Surjective f)
    (σ : Equiv.Perm β)
    (hσ : ∀ x, σ (f x) = f x) :
    σ = Equiv.refl β := by
  apply Equiv.ext
  intro b
  obtain ⟨x, rfl⟩ := hf b
  exact hσ x

/-- Uniquely induced permutations of class names respect composition.
Here `p.trans q` means apply p first, then q; in particular this
statement applies to the induced action of the automorphism group. -/
theorem label_action_comp
    (f : α → β) (hf : Function.Surjective f)
    (p q : α ≃ α)
    (σp σq σpq : Equiv.Perm β)
    (hp : ∀ x, σp (f x) = f (p x))
    (hq : ∀ x, σq (f x) = f (q x))
    (hpq : ∀ x, σpq (f x) = f (q (p x))) :
    σpq = σp.trans σq := by
  apply Equiv.ext
  intro b
  obtain ⟨x, rfl⟩ := hf b
  calc
    σpq (f x) = f (q (p x)) := hpq x
    _ = σq (f (p x)) := (hq (p x)).symm
    _ = σq (σp (f x)) := congrArg σq (hp x).symm
    _ = (σp.trans σq) (f x) := rfl

end EPPAReducts.BoundedEquivalence
