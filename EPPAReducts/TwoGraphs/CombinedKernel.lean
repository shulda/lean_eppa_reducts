import EPPAReducts.TwoGraphs.MatrixQuotient

/-!
# Faithfulness of the complete permutation-and-matrix action

Equality of two combined actions first identifies their index
permutations (every fibre contains at least one valuation class).
Cancelling that common permutation leaves equality of row shifts,
which was already proved equivalent to a globally constant
difference of symmetric matrices.

Thus the kernel of the full action is exactly the global matrix
of all zeroes or all ones, not any independent rowwise quotient.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u}

/-- The first-coordinate permutation is uniquely determined by the
combined action on all valuation vertices. -/
theorem matrixIndexPerm_eq_implies_index_eq
    (σ τ : Equiv.Perm X) (F G : X → X → Bool)
    (h : matrixIndexPerm σ F = matrixIndexPerm τ G) :
    σ = τ := by
  apply Equiv.ext
  intro x
  let z : Valuation X := fun _ => false
  have hx := congrArg (fun p : Equiv.Perm (ValuationVertex X) =>
    (p (x, valuationClass z)).1) h
  exact hx

/-- After identifying their first-coordinate permutations,
equal combined actions have identical row-shift permutations. -/
theorem matrixIndexPerm_eq_implies_rowShift_eq
    (σ : Equiv.Perm X) (F G : X → X → Bool)
    (h : matrixIndexPerm σ F = matrixIndexPerm σ G) :
    rowShiftPerm F = rowShiftPerm G := by
  apply Equiv.ext
  intro v
  have hv := congrArg (fun p : Equiv.Perm (ValuationVertex X) => p v) h
  change
    (indexPermVertex σ) ((rowShiftPerm F) v) =
      (indexPermVertex σ) ((rowShiftPerm G) v) at hv
  exact (indexPermVertex σ).injective hv

/-- Complete kernel characterization of the full action. If the
indices agree, the matrices need only agree modulo the single
globally constant matrix. -/
theorem matrixIndexPerm_eq_iff
    [Nonempty X]
    (σ τ : Equiv.Perm X) (F G : X → X → Bool)
    (hF : IsSymmetricBoolMatrix F)
    (hG : IsSymmetricBoolMatrix G) :
    matrixIndexPerm σ F = matrixIndexPerm τ G ↔
      σ = τ ∧ ∃ bit : Bool, ∀ x y, xorMatrix F G x y = bit := by
  constructor
  · intro h
    have hσ : σ = τ := matrixIndexPerm_eq_implies_index_eq σ τ F G h
    refine ⟨hσ, ?_⟩
    subst τ
    have hrow := matrixIndexPerm_eq_implies_rowShift_eq σ F G h
    exact (symmetric_rowShiftPerm_eq_iff_global_constant F G hF hG).mp hrow
  · rintro ⟨rfl, ⟨bit, h⟩⟩
    have hrow := rowShiftPerm_eq_of_global_constant F G bit h
    unfold matrixIndexPerm
    rw [hrow]

end EPPAReducts.TwoGraphs
