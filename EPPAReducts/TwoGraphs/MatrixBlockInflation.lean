import EPPAReducts.TwoGraphs.FullTransversalCoherentLift

/-!
# Pulling symmetric matrices back along a block retraction

Given a projection r : X → D, we can inflate every Boolean matrix F
on D to F(r(x),r(y)) on X. Symmetry, XOR composition and the
global-constant-matrix kernel are preserved.

If a permutation σX of X covers a permutation σ of D under r,
the matrix pullback commutes with the *contravariant* index action.
This is precisely the conditional group-law algebra needed for block
inflation in the coherent EPPA proof.

The hard combinatorial construction of an equivariant block
projection from a divisibility hypothesis is not claimed here.
-/

namespace EPPAReducts.TwoGraphs

universe u v
variable {D : Type u} {X : Type v}

/-- Inflate a Boolean matrix on D along any block projection r : X → D. -/
def inflateMatrix (r : X → D) (F : D → D → Bool) :
    X → X → Bool :=
  fun x y => F (r x) (r y)

/-- Matrix inflation preserves symmetry, without requiring
r to be injective or surjective. -/
theorem inflateMatrix_symmetric
    (r : X → D) (F : D → D → Bool)
    (hF : IsSymmetricBoolMatrix F) :
    IsSymmetricBoolMatrix (inflateMatrix r F) := by
  intro x y
  exact hF (r x) (r y)

/-- Matrix inflation commutes with entrywise Boolean XOR. -/
theorem inflateMatrix_xor
    (r : X → D) (F G : D → D → Bool) :
    xorMatrix (inflateMatrix r F) (inflateMatrix r G) =
      inflateMatrix r (xorMatrix F G) := by
  rfl

/-- A global-constant-matrix difference remains globally
constant after block inflation. This is the key well-definedness
obligation for the matrix action quotient. -/
theorem inflateMatrix_preserves_global_constant
    (r : X → D) (F G : D → D → Bool)
    (h : ∃ bit : Bool, ∀ d e, xorMatrix F G d e = bit) :
    ∃ bit : Bool, ∀ x y,
      xorMatrix (inflateMatrix r F) (inflateMatrix r G) x y = bit := by
  obtain ⟨bit, hb⟩ := h
  exact ⟨bit, fun x y => hb (r x) (r y)⟩

/-- If σX covers σ under the block projection r, the
inverse-reindexed matrix pullback commutes with inflation.
The inverse indices are essential for the actual composition
law of combined matrix/index automorphisms. -/
theorem inflateMatrix_reindex_symm
    (r : X → D)
    (σ : Equiv.Perm D) (σX : Equiv.Perm X)
    (hσ : ∀ x, r (σX x) = σ (r x))
    (F : D → D → Bool) :
    reindexMatrix σX.symm (inflateMatrix r F) =
      inflateMatrix r (reindexMatrix σ.symm F) := by
  funext x y
  change F (r (σX x)) (r (σX y)) =
    F (σ (r x)) (σ (r y))
  rw [hσ x, hσ y]

/-- Block inflation of matrix/index automorphisms respects the
full semidirect composition formula when the index permutation
on X covers the corresponding permutation on D. -/
theorem inflateMatrix_combined_comp
    (r : X → D)
    (σ τ : Equiv.Perm D)
    (σX τX : Equiv.Perm X)
    (hσ : ∀ x, r (σX x) = σ (r x))
    (F G : D → D → Bool) :
    (matrixIndexPerm σX (inflateMatrix r F)).trans
        (matrixIndexPerm τX (inflateMatrix r G)) =
      matrixIndexPerm (σX.trans τX)
        (inflateMatrix r (xorMatrix (reindexMatrix σ.symm G) F)) := by
  calc
    (matrixIndexPerm σX (inflateMatrix r F)).trans
        (matrixIndexPerm τX (inflateMatrix r G)) =
      matrixIndexPerm (σX.trans τX)
        (xorMatrix (reindexMatrix σX.symm (inflateMatrix r G))
          (inflateMatrix r F)) :=
            matrixIndexPerm_trans σX τX _ _
    _ = matrixIndexPerm (σX.trans τX)
          (inflateMatrix r (xorMatrix (reindexMatrix σ.symm G) F)) := by
        rw [inflateMatrix_reindex_symm r σ σX hσ G,
          inflateMatrix_xor]

end EPPAReducts.TwoGraphs
