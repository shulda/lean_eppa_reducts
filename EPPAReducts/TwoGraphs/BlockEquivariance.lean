import EPPAReducts.TwoGraphs.ValuationBlockInflation

/-!
# Equivariance of the marked block inflation

Inflating quotient valuations along an equivariant block retraction commutes
with reindexing and with symmetric-matrix row shifts.  Consequently the
induced embedding C_D ↪ C_X intertwines the actual combined permutation/
matrix actions, with no choice of valuation representatives.

This proves the action-level equality needed for blockwise homomorphic
lifts.  The full subgroup section and coherent EPPA are separate tasks.
-/

namespace EPPAReducts.TwoGraphs

universe u v
variable {D : Type u} {X : Type v}

/-- Valuation inflation intertwines reindexing whenever the retraction
is equivariant for the two index permutations. -/
theorem inflateValuation_reindex
    (r : X → D) (p : Equiv.Perm D) (pX : Equiv.Perm X)
    (hp : ∀ x, r (pX x) = p (r x))
    (a : Valuation D) :
    inflateValuation r (reindexValuation p a) =
      reindexValuation pX (inflateValuation r a) := by
  funext x
  change a (p.symm (r x)) = a (r (pX.symm x))
  have h := hp (pX.symm x)
  simpa using congrArg (fun d => a (p.symm d)) h

/-- Reindexing/inflation compatibility descends to complement classes. -/
theorem inflateValuationClass_reindex
    (r : X → D) (p : Equiv.Perm D) (pX : Equiv.Perm X)
    (hp : ∀ x, r (pX x) = p (r x))
    (q : ValuationClass D) :
    inflateValuationClass r (reindexValuationClass p q) =
      reindexValuationClass pX (inflateValuationClass r q) := by
  induction q using Quotient.inductionOn with
  | _ a =>
    change valuationClass (inflateValuation r (reindexValuation p a)) =
      valuationClass (reindexValuation pX (inflateValuation r a))
    rw [inflateValuation_reindex r p pX hp a]

/-- Translating a valuation by a matrix row and then inflating agrees
with translating the inflated valuation at a marked block point. -/
theorem inflateValuation_shiftValuationByRow
    (r : X → D) (ι : D → X) (hsection : ∀ d, r (ι d) = d)
    (F : D → D → Bool) (d : D) (a : Valuation D) :
    inflateValuation r (shiftValuationByRow F d a) =
      shiftValuationByRow (inflateMatrix r F) (ι d)
        (inflateValuation r a) := by
  funext x
  simp [inflateValuation, shiftValuationByRow, inflateMatrix, hsection]

/-- The row-shift compatibility is independent of representatives. -/
theorem inflateValuationClass_shiftValuationByRow
    (r : X → D) (ι : D → X) (hsection : ∀ d, r (ι d) = d)
    (F : D → D → Bool) (d : D) (q : ValuationClass D) :
    inflateValuationClass r (shiftValuationClassByRow F d q) =
      shiftValuationClassByRow (inflateMatrix r F) (ι d)
        (inflateValuationClass r q) := by
  induction q using Quotient.inductionOn with
  | _ a =>
    change valuationClass
        (inflateValuation r (shiftValuationByRow F d a)) =
      valuationClass
        (shiftValuationByRow (inflateMatrix r F) (ι d)
          (inflateValuation r a))
    rw [inflateValuation_shiftValuationByRow r ι hsection F d a]

/-- An inflated vertex commutes with blockwise reindexing. -/
theorem BlockCoordinates.inflateValuationVertex_indexPerm
    (B : BlockCoordinates D X) (p : Equiv.Perm D)
    (w : ValuationVertex D) :
    B.inflateValuationVertex (indexPermVertex p w) =
      indexPermVertex (B.liftPerm p) (B.inflateValuationVertex w) := by
  rcases w with ⟨d, q⟩
  apply Prod.ext
  · exact (B.liftPerm_marked p d).symm
  · exact inflateValuationClass_reindex B.projection p (B.liftPerm p)
      (B.projection_liftPerm p) q

/-- An inflated vertex commutes with any matrix row shift. -/
theorem BlockCoordinates.inflateValuationVertex_rowShift
    (B : BlockCoordinates D X) (F : D → D → Bool)
    (w : ValuationVertex D) :
    B.inflateValuationVertex (rowShiftPerm F w) =
      rowShiftPerm (inflateMatrix B.projection F)
        (B.inflateValuationVertex w) := by
  rcases w with ⟨d, q⟩
  apply Prod.ext
  · rfl
  · exact inflateValuationClass_shiftValuationByRow
      B.projection B.markedEmbedding B.projection_marked F d q

/-- **Equivariant induced embedding:** block inflation intertwines
the complete matrix/index permutation action, not just its factors.
This is the exact action identity used by the eventual group lift. -/
theorem BlockCoordinates.inflateValuationVertex_matrixIndexPerm
    (B : BlockCoordinates D X) (p : Equiv.Perm D)
    (F : D → D → Bool) (w : ValuationVertex D) :
    B.inflateValuationVertex (matrixIndexPerm p F w) =
      matrixIndexPerm (B.liftPerm p) (inflateMatrix B.projection F)
        (B.inflateValuationVertex w) := by
  change B.inflateValuationVertex
      (indexPermVertex p (rowShiftPerm F w)) =
    indexPermVertex (B.liftPerm p)
      (rowShiftPerm (inflateMatrix B.projection F)
        (B.inflateValuationVertex w))
  rw [B.inflateValuationVertex_indexPerm p (rowShiftPerm F w),
    B.inflateValuationVertex_rowShift F w]

end EPPAReducts.TwoGraphs
