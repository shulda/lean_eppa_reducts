import EPPAReducts.TwoGraphs.MatrixKernel

/-!
# Exact kernel of the symmetric-matrix action

Two symmetric matrices induce the same permutation of all valuation
vertices if and only if their entrywise XOR is globally constant
(false everywhere or true everywhere). We prove both directions without
identifying independent row complements with independent matrix quotients.

Nonemptiness of X is needed only for the "only if" direction.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u}

/-- Two Boolean bits have XOR false exactly when they are equal. -/
private theorem xor_eq_false_implies_eq
    (p q : Bool) (h : Bool.xor p q = false) : p = q := by
  cases p <;> cases q <;> simp_all

/-- Two Boolean bits have XOR true exactly when they are complements. -/
private theorem xor_eq_true_implies_not
    (p q : Bool) (h : Bool.xor p q = true) : p = !q := by
  cases p <;> cases q <;> simp_all

/-- A globally constant XOR between two matrices guarantees that
their row-shift permutations on quotient valuations are identical. -/
theorem rowShiftPerm_eq_of_global_constant
    (F G : X → X → Bool) (bit : Bool)
    (h : ∀ x y, xorMatrix F G x y = bit) :
    rowShiftPerm F = rowShiftPerm G := by
  apply Equiv.ext
  intro v
  rcases v with ⟨x, q⟩
  induction q using Quotient.inductionOn with
  | _ a =>
    have hq :
        valuationClass (shiftValuationByRow F x a) =
          valuationClass (shiftValuationByRow G x a) := by
      cases bit with
      | false =>
          have hrow (y : X) : F x y = G x y := by
            exact xor_eq_false_implies_eq _ _ (h x y)
          have heq : shiftValuationByRow F x a =
              shiftValuationByRow G x a := by
            funext y
            simp only [shiftValuationByRow, hrow y]
          exact congrArg valuationClass heq
      | true =>
          have hrow (y : X) : F x y = !(G x y) := by
            exact xor_eq_true_implies_not _ _ (h x y)
          have heq : shiftValuationByRow F x a =
              flipValuation (shiftValuationByRow G x a) := by
            funext y
            rw [show F x y = !(G x y) from hrow y]
            cases ha : a y <;> cases hg : G x y <;>
              simp [shiftValuationByRow, flipValuation, ha, hg]
          calc
            valuationClass (shiftValuationByRow F x a) =
                valuationClass (flipValuation (shiftValuationByRow G x a)) :=
                  congrArg valuationClass heq
            _ = valuationClass (shiftValuationByRow G x a) :=
                  valuationClass_flip _
    change
      (x, valuationClass (shiftValuationByRow F x a)) =
        (x, valuationClass (shiftValuationByRow G x a))
    exact congrArg (fun z : ValuationClass X => (x, z)) hq

/-- Exact faithful-action kernel for **symmetric** matrices. Only the
single globally constant Boolean matrix is invisible on the witness. -/
theorem symmetric_rowShiftPerm_eq_iff_global_constant
    [Nonempty X]
    (F G : X → X → Bool)
    (hF : IsSymmetricBoolMatrix F)
    (hG : IsSymmetricBoolMatrix G) :
    rowShiftPerm F = rowShiftPerm G ↔
      ∃ bit : Bool, ∀ x y, xorMatrix F G x y = bit := by
  constructor
  · intro h
    exact symmetric_rowShiftPerm_eq_implies_global_constant F G hF hG h
  · rintro ⟨bit, h⟩
    exact rowShiftPerm_eq_of_global_constant F G bit h

end EPPAReducts.TwoGraphs
