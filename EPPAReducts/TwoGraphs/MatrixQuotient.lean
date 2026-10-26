import EPPAReducts.TwoGraphs.MatrixKernelConverse

/-!
# Faithful quotient of symmetric Boolean matrices

The kernel of the action on the valuation witness is the globally
constant matrix (zero or one). This module constructs an actual
quotient of symmetric matrices and injects it into permutations of
the valuation vertices. The relation is presented by equality of
induced actions; the preceding kernel theorem establishes that this
is **exactly** the global-constant-matrix equivalence when X is
nonempty, not a quotient by arbitrary individual row complements.

No complete EPPA witness has yet been proved.
-/

namespace EPPAReducts.TwoGraphs

universe u

/-- A symmetric Boolean matrix with its symmetry proof. -/
structure SymmetricBoolMatrix (X : Type u) where
  entries : X → X → Bool
  symmetric : IsSymmetricBoolMatrix entries

/-- Two symmetric matrices are equivalent when they induce the same
row-shift permutation of the valuation-vertex carrier. -/
def symmetricMatrixActionSetoid (X : Type u) :
    Setoid (SymmetricBoolMatrix X) where
  r F G := rowShiftPerm F.entries = rowShiftPerm G.entries
  iseqv := {
    refl := by
      intro F
      rfl
    symm := by
      intro F G h
      exact h.symm
    trans := by
      intro F G H h₁ h₂
      exact h₁.trans h₂
  }

/-- The quotient of symmetric matrices by the action kernel. -/
abbrev SymmetricMatrixClass (X : Type u) :=
  Quotient (symmetricMatrixActionSetoid X)

/-- Quotient map from symmetric matrices to action classes. -/
def symmetricMatrixClass {X : Type u}
    (F : SymmetricBoolMatrix X) : SymmetricMatrixClass X :=
  Quotient.mk (symmetricMatrixActionSetoid X) F

/-- The action of an equivalence class on the valuation witness. -/
def symmetricMatrixClassPerm {X : Type u}
    (q : SymmetricMatrixClass X) : Equiv.Perm (ValuationVertex X) :=
  Quotient.liftOn q (fun F => rowShiftPerm F.entries)
    (by intro F G h; exact h)

@[simp] theorem symmetricMatrixClassPerm_mk {X : Type u}
    (F : SymmetricBoolMatrix X) :
    symmetricMatrixClassPerm (symmetricMatrixClass F) =
      rowShiftPerm F.entries := by
  rfl

/-- The quotient action is faithful: different quotient classes
really yield different permutations of the valuation witness. -/
theorem symmetricMatrixClassPerm_injective {X : Type u} :
    Function.Injective (symmetricMatrixClassPerm (X := X)) := by
  intro p q h
  induction p using Quotient.inductionOn with
  | _ F =>
    induction q using Quotient.inductionOn with
    | _ G =>
      apply Quotient.sound
      exact h

/-- On a nonempty index set, two symmetric matrix classes coincide
if and only if the XOR of their matrices is **globally** constant. -/
theorem symmetricMatrixClass_eq_iff_globalConstant
    {X : Type u} [Nonempty X]
    (F G : SymmetricBoolMatrix X) :
    symmetricMatrixClass F = symmetricMatrixClass G ↔
      ∃ bit : Bool, ∀ x y, xorMatrix F.entries G.entries x y = bit := by
  constructor
  · intro h
    have ha : rowShiftPerm F.entries = rowShiftPerm G.entries :=
      Quotient.exact h
    exact (symmetric_rowShiftPerm_eq_iff_global_constant
      F.entries G.entries F.symmetric G.symmetric).mp ha
  · intro h
    apply Quotient.sound
    exact (symmetric_rowShiftPerm_eq_iff_global_constant
      F.entries G.entries F.symmetric G.symmetric).mpr h

end EPPAReducts.TwoGraphs
