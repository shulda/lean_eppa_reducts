import EPPAReducts.TwoGraphs.IndexPermutation
import EPPAReducts.TwoGraphs.MatrixXor

/-!
# Semidirect-product compatibility of matrix shifts and index permutations

The matrix action is NOT an ordinary direct product. Reindexing a
matrix by σ sends F(x,y) to F(σ⁻¹x, σ⁻¹y), and conjugates its
row-shift permutation accordingly.

The identities below are necessary for the true action group and
for the later homomorphic extension/partial-automorphism sections.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u}

/-- Transport a Boolean matrix through an index permutation. -/
def reindexMatrix (σ : Equiv.Perm X)
    (F : X → X → Bool) : X → X → Bool :=
  fun x y => F (σ.symm x) (σ.symm y)

/-- Matrix reindexing preserves symmetry. -/
theorem reindexMatrix_symmetric
    (σ : Equiv.Perm X) (F : X → X → Bool)
    (hF : IsSymmetricBoolMatrix F) :
    IsSymmetricBoolMatrix (reindexMatrix σ F) := by
  intro x y
  exact hF (σ.symm x) (σ.symm y)

/-- Reindexing a row-shifted raw valuation is equivalent to
shifting the reindexed valuation by the transported matrix row. -/
theorem reindexValuation_shiftValuationByRow
    (σ : Equiv.Perm X) (F : X → X → Bool)
    (x : X) (a : Valuation X) :
    reindexValuation σ (shiftValuationByRow F x a) =
      shiftValuationByRow (reindexMatrix σ F) (σ x)
        (reindexValuation σ a) := by
  funext y
  simp [reindexValuation, shiftValuationByRow, reindexMatrix]

/-- Compatibility of matrix shifts with reindexing on the quotient Q_X. -/
theorem reindexValuationClass_shiftValuationClassByRow
    (σ : Equiv.Perm X) (F : X → X → Bool)
    (x : X) (q : ValuationClass X) :
    reindexValuationClass σ (shiftValuationClassByRow F x q) =
      shiftValuationClassByRow (reindexMatrix σ F) (σ x)
        (reindexValuationClass σ q) := by
  induction q using Quotient.inductionOn with
  | _ a =>
    change
      valuationClass (reindexValuation σ (shiftValuationByRow F x a)) =
        valuationClass
          (shiftValuationByRow (reindexMatrix σ F) (σ x)
            (reindexValuation σ a))
    rw [reindexValuation_shiftValuationByRow]

/-- Row shifts and index permutations obey the semidirect conjugation law
pointwise on the whole valuation witness. -/
theorem indexPermVertex_rowShiftVertex
    (σ : Equiv.Perm X) (F : X → X → Bool)
    (v : ValuationVertex X) :
    indexPermVertex σ (rowShiftVertex F v) =
      rowShiftVertex (reindexMatrix σ F) (indexPermVertex σ v) := by
  rcases v with ⟨x, q⟩
  change
    (σ x, reindexValuationClass σ (shiftValuationClassByRow F x q)) =
      (σ x, shiftValuationClassByRow (reindexMatrix σ F) (σ x)
        (reindexValuationClass σ q))
  rw [reindexValuationClass_shiftValuationClassByRow]

/-- The same conjugation law for actual permutations. -/
theorem indexPerm_rowShift_conjugation
    (σ : Equiv.Perm X) (F : X → X → Bool) :
    (rowShiftPerm F).trans (indexPermVertex σ) =
      (indexPermVertex σ).trans
        (rowShiftPerm (reindexMatrix σ F)) := by
  apply Equiv.ext
  intro v
  exact indexPermVertex_rowShiftVertex σ F v

/-- Reindexing permutations compose in the expected order on raw valuations. -/
theorem reindexValuation_trans
    (σ τ : Equiv.Perm X) (a : Valuation X) :
    reindexValuation τ (reindexValuation σ a) =
      reindexValuation (σ.trans τ) a := by
  funext x
  rfl

/-- Reindexing permutations compose on quotient classes. -/
theorem reindexValuationClass_trans
    (σ τ : Equiv.Perm X) (q : ValuationClass X) :
    reindexValuationClass τ (reindexValuationClass σ q) =
      reindexValuationClass (σ.trans τ) q := by
  induction q using Quotient.inductionOn with
  | _ a =>
    change valuationClass
      (reindexValuation τ (reindexValuation σ a)) =
        valuationClass (reindexValuation (σ.trans τ) a)
    rw [reindexValuation_trans]

/-- Actual index permutations form a homomorphic action on the carrier. -/
theorem indexPermVertex_trans (σ τ : Equiv.Perm X) :
    (indexPermVertex σ).trans (indexPermVertex τ) =
      indexPermVertex (σ.trans τ) := by
  apply Equiv.ext
  intro v
  rcases v with ⟨x, q⟩
  change
    (τ (σ x), reindexValuationClass τ (reindexValuationClass σ q)) =
      ((σ.trans τ) x, reindexValuationClass (σ.trans τ) q)
  rw [reindexValuationClass_trans]
  rfl

end EPPAReducts.TwoGraphs
