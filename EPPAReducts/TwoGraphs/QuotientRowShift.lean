import EPPAReducts.TwoGraphs.SymmetricRowShift
import EPPAReducts.TwoGraphs.ValuationVertex

/-!
# Descending Boolean row translations to quotient valuation classes

A row translation by a Boolean matrix commutes with complementing the
input valuation, hence induces a self-inverse permutation of Q_X.
We then obtain an actual permutation of the valuation-vertex carrier.

This is only the identity-fibre-permutation part of the matrix group.
The general action will allow also permuting the first coordinates.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u}

/-- Translating a valuation by a matrix row commutes with complementing it. -/
theorem shiftValuationByRow_flip
    (F : X → X → Bool) (x : X) (a : Valuation X) :
    shiftValuationByRow F x (flipValuation a) =
      flipValuation (shiftValuationByRow F x a) := by
  funext y
  cases ha : a y <;> cases hF : F x y <;>
    simp [shiftValuationByRow, flipValuation, ha, hF]

/-- Applying the same row translation twice is the identity. -/
theorem shiftValuationByRow_twice
    (F : X → X → Bool) (x : X) (a : Valuation X) :
    shiftValuationByRow F x (shiftValuationByRow F x a) = a := by
  funext y
  cases ha : a y <;> cases hF : F x y <;>
    simp [shiftValuationByRow, ha, hF]

/-- A row translation is well-defined on valuation complement classes. -/
def shiftValuationClassByRow
    (F : X → X → Bool) (x : X) (q : ValuationClass X) : ValuationClass X :=
  Quotient.liftOn q
    (fun a => valuationClass (shiftValuationByRow F x a))
    (by
      intro a b h
      rcases h with hab | hab
      · rw [hab]
      · rw [hab, shiftValuationByRow_flip, valuationClass_flip])

@[simp] theorem shiftValuationClassByRow_mk
    (F : X → X → Bool) (x : X) (a : Valuation X) :
    shiftValuationClassByRow F x (valuationClass a) =
      valuationClass (shiftValuationByRow F x a) := by
  rfl

/-- On the quotient, every row translation is an involution. -/
theorem shiftValuationClassByRow_twice
    (F : X → X → Bool) (x : X) (q : ValuationClass X) :
    shiftValuationClassByRow F x
      (shiftValuationClassByRow F x q) = q := by
  induction q using Quotient.inductionOn with
  | _ a =>
    change valuationClass
      (shiftValuationByRow F x (shiftValuationByRow F x a)) =
      valuationClass a
    rw [shiftValuationByRow_twice]

/-- The actual valuation-vertex map induced by a Boolean matrix. -/
def rowShiftVertex
    (F : X → X → Bool) (v : ValuationVertex X) : ValuationVertex X :=
  (v.1, shiftValuationClassByRow F v.1 v.2)

/-- A matrix row shift is self-inverse on the whole witness carrier. -/
theorem rowShiftVertex_twice
    (F : X → X → Bool) (v : ValuationVertex X) :
    rowShiftVertex F (rowShiftVertex F v) = v := by
  rcases v with ⟨x, q⟩
  change
    (x, shiftValuationClassByRow F x
       (shiftValuationClassByRow F x q)) = (x, q)
  rw [shiftValuationClassByRow_twice]

/-- A Boolean matrix induces a bona fide permutation of the witness
carrier, regardless of symmetry. Symmetry will be used for relation
preservation, not for bijectivity. -/
def rowShiftPerm (F : X → X → Bool) : Equiv.Perm (ValuationVertex X) where
  toFun := rowShiftVertex F
  invFun := rowShiftVertex F
  left_inv := rowShiftVertex_twice F
  right_inv := rowShiftVertex_twice F

/-- Symmetric matrix row shifts preserve the ternary parity on all
valuation vertices, including non-transversal triples. -/
theorem vertexTripleParity_rowShift
    (F : X → X → Bool) (hF : IsSymmetricBoolMatrix F)
    (u v w : ValuationVertex X) :
    vertexTripleParity (rowShiftVertex F u)
      (rowShiftVertex F v) (rowShiftVertex F w) =
      vertexTripleParity u v w := by
  rcases u with ⟨x, a⟩
  rcases v with ⟨y, b⟩
  rcases w with ⟨z, c⟩
  induction a using Quotient.inductionOn with
  | _ va =>
    induction b using Quotient.inductionOn with
    | _ vb =>
      induction c using Quotient.inductionOn with
      | _ vc =>
        change rawTripleParity x y z
            (shiftValuationByRow F x va)
            (shiftValuationByRow F y vb)
            (shiftValuationByRow F z vc) =
          rawTripleParity x y z va vb vc
        exact rawTripleParity_symmetricRowShift F hF x y z va vb vc

end EPPAReducts.TwoGraphs
