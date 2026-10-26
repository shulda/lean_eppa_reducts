import EPPAReducts.TwoGraphs.QuotientRowShift

/-!
# Composition of Boolean matrix translations

These identities are the group-law backbone for coherent extensions.
An arbitrary matrix row translation acts on the quotient-valuation
carrier; symmetric matrices are closed under entrywise XOR and
preserve the ternary two-graph relation.

No assertion of EPPA or a matrix-action section is made here.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u}

/-- Add matrices entrywise over the two-element field. -/
def xorMatrix (F G : X → X → Bool) : X → X → Bool :=
  fun x y => Bool.xor (F x y) (G x y)

/-- The XOR of symmetric matrices is again symmetric. -/
theorem xorMatrix_symmetric
    (F G : X → X → Bool)
    (hF : IsSymmetricBoolMatrix F) (hG : IsSymmetricBoolMatrix G) :
    IsSymmetricBoolMatrix (xorMatrix F G) := by
  intro x y
  simp only [xorMatrix, hF x y, hG x y]

/-- Composition of two row translations is an entrywise XOR row translation. -/
theorem shiftValuationByRow_xor
    (F G : X → X → Bool) (x : X) (a : Valuation X) :
    shiftValuationByRow F x (shiftValuationByRow G x a) =
      shiftValuationByRow (xorMatrix F G) x a := by
  funext y
  cases ha : a y <;> cases hF : F x y <;> cases hG : G x y <;>
    simp [shiftValuationByRow, xorMatrix, ha, hF, hG]

/-- Composition law descended to quotient valuation classes. -/
theorem shiftValuationClassByRow_xor
    (F G : X → X → Bool) (x : X) (q : ValuationClass X) :
    shiftValuationClassByRow F x (shiftValuationClassByRow G x q) =
      shiftValuationClassByRow (xorMatrix F G) x q := by
  induction q using Quotient.inductionOn with
  | _ a =>
    change
      valuationClass (shiftValuationByRow F x (shiftValuationByRow G x a)) =
        valuationClass (shiftValuationByRow (xorMatrix F G) x a)
    rw [shiftValuationByRow_xor]

/-- The same composition formula on the whole valuation-vertex carrier. -/
theorem rowShiftVertex_xor
    (F G : X → X → Bool) (v : ValuationVertex X) :
    rowShiftVertex F (rowShiftVertex G v) =
      rowShiftVertex (xorMatrix F G) v := by
  rcases v with ⟨x, q⟩
  change (x, shiftValuationClassByRow F x (shiftValuationClassByRow G x q)) =
    (x, shiftValuationClassByRow (xorMatrix F G) x q)
  rw [shiftValuationClassByRow_xor]

/-- The map from matrices into witness permutations respects composition. -/
theorem rowShiftPerm_xor
    (F G : X → X → Bool) :
    (rowShiftPerm G).trans (rowShiftPerm F) =
      rowShiftPerm (xorMatrix F G) := by
  apply Equiv.ext
  intro v
  exact rowShiftVertex_xor F G v

/-- Identity matrix for the XOR law. -/
def zeroMatrix (X : Type u) : X → X → Bool := fun _ _ => false

theorem zeroMatrix_symmetric :
    IsSymmetricBoolMatrix (zeroMatrix X) := by
  intro x y
  rfl

/-- Translating by the zero matrix is the identity permutation. -/
theorem rowShiftPerm_zero :
    rowShiftPerm (zeroMatrix X) = Equiv.refl (ValuationVertex X) := by
  apply Equiv.ext
  intro v
  rcases v with ⟨x, q⟩
  induction q using Quotient.inductionOn with
  | _ a =>
    change (x, valuationClass (shiftValuationByRow (zeroMatrix X) x a)) =
      (x, valuationClass a)
    congr 1
    funext y
    simp [shiftValuationByRow, zeroMatrix]

end EPPAReducts.TwoGraphs
