import EPPAReducts.BoundedEquivalence.ExtendLabels
import EPPAReducts.BoundedEquivalence.LabelEquiv

/-!
# The class action is determined by its realized core

A finite old core realizes every auxiliary class. Consequently, to
determine how a kernel-preserving map acts on class names throughout
a candidate EPPA witness, it is enough to know its action on the core.
This avoids any accidental assumption that numerical names belong to
the relational language.

The proof is valid for arbitrary label sets and does not require
a permutation of labels to be chosen in advance.
-/

namespace EPPAReducts.BoundedEquivalence

universe u v w

/-- If every auxiliary class is represented on the embedded core and
p preserves equality of class labels, its action on *all* labels is
uniquely determined by its action on representatives in that core.

The label map tau need not be bijective for this implication. -/
theorem core_determines_label_action
    {A : Type u} {B : Type v} {κ : Type w}
    (ι : A → B) (f : B → κ)
    (hcore : Function.Surjective (fun a : A => f (ι a)))
    (p : B → B)
    (hkernel : ∀ x y : B, f x = f y → f (p x) = f (p y))
    (τ : κ → κ)
    (hcoreAction : ∀ a : A, f (p (ι a)) = τ (f (ι a))) :
    ∀ x : B, f (p x) = τ (f x) := by
  intro x
  obtain ⟨a, ha⟩ := hcore (f x)
  calc
    f (p x) = f (p (ι a)) := hkernel x (ι a) ha.symm
    _ = τ (f (ι a)) := hcoreAction a
    _ = τ (f x) := congrArg τ ha

/-- In particular, any kernel-preserving map fixing the entire core
pointwise fixes every unlabelled equivalence class, not just the
classes of tuples supported on the old core. -/
theorem core_pointwise_fixed_preserves_labels
    {A : Type u} {B : Type v} {κ : Type w}
    (ι : A → B) (f : B → κ)
    (hcore : Function.Surjective (fun a : A => f (ι a)))
    (p : B → B)
    (hkernel : ∀ x y : B, f x = f y → f (p x) = f (p y))
    (hfix : ∀ a : A, p (ι a) = ι a) :
    ∀ x : B, f (p x) = f x := by
  exact core_determines_label_action ι f hcore p hkernel id
    (by intro a; simp only [hfix, id_eq])

/-- If p shifts all auxiliary colours on the realized core by
delta, its action on every class in the full extension is the
same translation. This will be instantiated with delta=1 in ZMod m.
No class-name preservation is assumed of p. -/
theorem core_constant_shift_determines_all_labels
    {A : Type u} {B : Type v} {κ : Type w} [Add κ]
    (ι : A → B) (f : B → κ)
    (hcore : Function.Surjective (fun a : A => f (ι a)))
    (p : B → B)
    (hkernel : ∀ x y : B, f x = f y → f (p x) = f (p y))
    (δ : κ)
    (hshiftCore : ∀ a : A, f (p (ι a)) = f (ι a) + δ) :
    ∀ x : B, f (p x) = f x + δ :=
  core_determines_label_action ι f hcore p hkernel
    (fun c => c + δ) hshiftCore

end EPPAReducts.BoundedEquivalence
