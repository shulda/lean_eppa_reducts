import EPPAReducts.TwoGraphs.CombinedAutomorphism

/-!
# Full composition law for permutation-and-matrix actions

Recall that \`matrixIndexPerm σ F\` adds the row of F first and then
reindexes by σ. With \`trans\` meaning "first, then", composition is

(σ,F) ; (τ,G) = (σ.trans τ, (σ⁻¹)_*G + F).

In particular this is *not* componentwise multiplication of the two
factors. No global-matrix faithfulness statement is assumed here.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u}

/-- Pulling back a matrix first through σ⁻¹ and then through σ
returns the original matrix. -/
theorem reindexMatrix_symm_cancel
    (σ : Equiv.Perm X) (G : X → X → Bool) :
    reindexMatrix σ (reindexMatrix σ.symm G) = G := by
  funext x y
  simp [reindexMatrix]

/-- Move a row translation past an index permutation, in the
direction required by composing the two combined actions. -/
theorem indexPerm_rowShift_reverse
    (σ : Equiv.Perm X) (G : X → X → Bool) :
    (indexPermVertex σ).trans (rowShiftPerm G) =
      (rowShiftPerm (reindexMatrix σ.symm G)).trans
        (indexPermVertex σ) := by
  have h := indexPerm_rowShift_conjugation σ (reindexMatrix σ.symm G)
  rw [reindexMatrix_symm_cancel] at h
  exact h.symm

/-- The full semidirect composition law, proved for actual permutations
of the valuation-vertex carrier (without assuming matrix symmetry). -/
theorem matrixIndexPerm_trans
    (σ τ : Equiv.Perm X) (F G : X → X → Bool) :
    (matrixIndexPerm σ F).trans (matrixIndexPerm τ G) =
      matrixIndexPerm (σ.trans τ)
        (xorMatrix (reindexMatrix σ.symm G) F) := by
  apply Equiv.ext
  intro v
  let H := reindexMatrix σ.symm G
  have hswap :
      (rowShiftPerm G) ((indexPermVertex σ) ((rowShiftPerm F) v)) =
      (indexPermVertex σ) ((rowShiftPerm H) ((rowShiftPerm F) v)) := by
    have h := indexPerm_rowShift_reverse σ G
    exact congrArg (fun e : Equiv.Perm (ValuationVertex X) =>
      e ((rowShiftPerm F) v)) h
  have hrow :
      (rowShiftPerm H) ((rowShiftPerm F) v) =
      (rowShiftPerm (xorMatrix H F)) v :=
    rowShiftVertex_xor H F v
  have hindices :
      (indexPermVertex τ) ((indexPermVertex σ) ((rowShiftPerm (xorMatrix H F)) v)) =
      (indexPermVertex (σ.trans τ)) ((rowShiftPerm (xorMatrix H F)) v) := by
    have h := indexPermVertex_trans σ τ
    exact congrArg (fun e : Equiv.Perm (ValuationVertex X) =>
      e ((rowShiftPerm (xorMatrix H F)) v)) h
  change
    (indexPermVertex τ) ((rowShiftPerm G) ((indexPermVertex σ) ((rowShiftPerm F) v))) =
    (indexPermVertex (σ.trans τ)) ((rowShiftPerm (xorMatrix H F)) v)
  calc
    (indexPermVertex τ) ((rowShiftPerm G) ((indexPermVertex σ) ((rowShiftPerm F) v))) =
        (indexPermVertex τ) ((indexPermVertex σ) ((rowShiftPerm H) ((rowShiftPerm F) v))) :=
          congrArg (indexPermVertex τ) hswap
    _ = (indexPermVertex τ) ((indexPermVertex σ) ((rowShiftPerm (xorMatrix H F)) v)) := by
          rw [hrow]
    _ = (indexPermVertex (σ.trans τ)) ((rowShiftPerm (xorMatrix H F)) v) :=
          hindices

end EPPAReducts.TwoGraphs
