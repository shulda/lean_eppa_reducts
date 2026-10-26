import EPPAReducts.TwoGraphs.CombinedGroupLaw

/-!
# Kernel of the matrix action: the constant-matrix necessity

If two symmetric Boolean matrices give the same permutation of all
valuation vertices, then their XOR is a **single globally constant
matrix**. This is not rowwise complementation: symmetry forces all
row-constants to agree.

The converse and the global-matrix quotient are separate lemmas.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u}

/-- Equality of valuation classes is exactly equality or full
complementation of the two representatives. -/
theorem valuationClass_eq_iff
    (a b : Valuation X) :
    valuationClass a = valuationClass b ↔
      a = b ∨ a = flipValuation b := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- Equality of two row-shift permutations forces equality or
complementation of each individual matrix row. -/
theorem rowShiftPerm_eq_implies_row_equiv
    (F G : X → X → Bool)
    (h : rowShiftPerm F = rowShiftPerm G)
    (x : X) :
    (fun y => F x y) = (fun y => G x y) ∨
      (fun y => F x y) = flipValuation (fun y => G x y) := by
  let z : Valuation X := fun _ => false
  have hpoint :
      (rowShiftPerm F) (x, valuationClass z) =
        (rowShiftPerm G) (x, valuationClass z) := by rw [h]
  have hq := congrArg Prod.snd hpoint
  change valuationClass (shiftValuationByRow F x z) =
    valuationClass (shiftValuationByRow G x z) at hq
  rcases (valuationClass_eq_iff _ _).mp hq with hr | hr
  · left
    funext y
    have hy := congrFun hr y
    simpa [shiftValuationByRow, z] using hy
  · right
    funext y
    have hy := congrFun hr y
    simpa [shiftValuationByRow, flipValuation, z] using hy

/-- The XOR of the two matrices is constant along every row
whenever their actions agree. -/
theorem rowShiftPerm_eq_implies_row_constant
    (F G : X → X → Bool)
    (h : rowShiftPerm F = rowShiftPerm G)
    (x : X) :
    ∃ b : Bool, ∀ y, xorMatrix F G x y = b := by
  rcases rowShiftPerm_eq_implies_row_equiv F G h x with hr | hr
  · refine ⟨false, ?_⟩
    intro y
    have heq := congrFun hr y
    change Bool.xor (F x y) (G x y) = false
    rw [heq]
    cases G x y <;> decide
  · refine ⟨true, ?_⟩
    intro y
    have heq := congrFun hr y
    change Bool.xor (F x y) (G x y) = true
    rw [heq]
    cases G x y <;> decide

/-- Symmetry upgrades rowwise constant XOR to *one global bit*,
provided the index set is nonempty. -/
theorem symmetric_rowShiftPerm_eq_implies_global_constant
    [Nonempty X]
    (F G : X → X → Bool)
    (hF : IsSymmetricBoolMatrix F)
    (hG : IsSymmetricBoolMatrix G)
    (h : rowShiftPerm F = rowShiftPerm G) :
    ∃ b : Bool, ∀ x y, xorMatrix F G x y = b := by
  obtain ⟨r⟩ := ‹Nonempty X›
  obtain ⟨b, hb⟩ := rowShiftPerm_eq_implies_row_constant F G h r
  have hsym : IsSymmetricBoolMatrix (xorMatrix F G) :=
    xorMatrix_symmetric F G hF hG
  refine ⟨b, ?_⟩
  intro x y
  obtain ⟨bx, hbx⟩ := rowShiftPerm_eq_implies_row_constant F G h x
  calc
    xorMatrix F G x y = bx := hbx y
    _ = xorMatrix F G x r := (hbx r).symm
    _ = xorMatrix F G r x := hsym x r
    _ = b := hb x

end EPPAReducts.TwoGraphs
