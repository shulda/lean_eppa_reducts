import EPPAReducts.TwoGraphs.MatrixBlockInflation

/-!
# Explicit marked block coordinates and their permutation actions

A marked block-coordinate system is a bijection
    D × I ≃ X
together with one distinguished block index i₀ ∈ I.

The resulting block projection, marked embedded copy of D, and
blockwise action of Perm D are all canonical. The action is
homomorphic and equivariant for the projection, enabling the
matrix inflation lemmas from the previous module.

Constructing these coordinates from |D| ∣ |X| and a specific
marked subset D ⊆ X remains a separate finite combinatorial lemma.
-/

namespace EPPAReducts.TwoGraphs

/-- A product decomposition of X into equally sized D-indexed blocks,
with one selected copy of D. -/
structure BlockCoordinates (D X : Type) where
  Index : Type
  distinguished : Index
  equiv : D × Index ≃ X

variable {D X : Type}

/-- Forget the block index to project X back to D. -/
def BlockCoordinates.projection (B : BlockCoordinates D X) : X → D :=
  fun x => (B.equiv.symm x).1

/-- The distinguished embedded copy of D in X. -/
def BlockCoordinates.markedEmbedding
    (B : BlockCoordinates D X) : D ↪ X where
  toFun := fun d => B.equiv (d, B.distinguished)
  inj' := by
    intro d e h
    exact congrArg Prod.fst (B.equiv.injective h)

/-- The blockwise extension of a permutation of D to all of X. -/
def BlockCoordinates.liftPerm
    (B : BlockCoordinates D X) (p : Equiv.Perm D) : Equiv.Perm X :=
  B.equiv.symm.trans
    (Equiv.prodCongr p (Equiv.refl B.Index)) |>.trans B.equiv

/-- The block projection restricts to the identity on the
distinguished embedded D. -/
theorem BlockCoordinates.projection_marked
    (B : BlockCoordinates D X) (d : D) :
    B.projection (B.markedEmbedding d) = d := by
  simp [BlockCoordinates.projection, BlockCoordinates.markedEmbedding]

/-- Blockwise permutations act on the marked copy as prescribed. -/
theorem BlockCoordinates.liftPerm_marked
    (B : BlockCoordinates D X) (p : Equiv.Perm D) (d : D) :
    B.liftPerm p (B.markedEmbedding d) =
      B.markedEmbedding (p d) := by
  simp [BlockCoordinates.liftPerm, BlockCoordinates.markedEmbedding]

/-- Every blockwise permutation covers p under the projection. -/
theorem BlockCoordinates.projection_liftPerm
    (B : BlockCoordinates D X) (p : Equiv.Perm D) (x : X) :
    B.projection (B.liftPerm p x) = p (B.projection x) := by
  simp [BlockCoordinates.projection, BlockCoordinates.liftPerm]

/-- The blockwise lift of the identity is the identity. -/
theorem BlockCoordinates.liftPerm_refl
    (B : BlockCoordinates D X) :
    B.liftPerm (Equiv.refl D) = Equiv.refl X := by
  apply Equiv.ext
  intro x
  simp [BlockCoordinates.liftPerm]

/-- Blockwise lifts respect composition, giving a homomorphic
permutation action of Perm D on X. -/
theorem BlockCoordinates.liftPerm_trans
    (B : BlockCoordinates D X) (p q : Equiv.Perm D) :
    (B.liftPerm p).trans (B.liftPerm q) =
      B.liftPerm (p.trans q) := by
  apply Equiv.ext
  intro x
  simp [BlockCoordinates.liftPerm, Equiv.prodCongr,
    Equiv.trans_apply]

/-- The matrix/index action inflated through this block system
respects the *full semidirect* composition law. -/
theorem BlockCoordinates.combinedAction_trans
    (B : BlockCoordinates D X) (p q : Equiv.Perm D)
    (F G : D → D → Bool) :
    (matrixIndexPerm (B.liftPerm p)
      (inflateMatrix B.projection F)).trans
      (matrixIndexPerm (B.liftPerm q)
        (inflateMatrix B.projection G)) =
      matrixIndexPerm (B.liftPerm (p.trans q))
        (inflateMatrix B.projection
          (xorMatrix (reindexMatrix p.symm G) F)) := by
  calc
    (matrixIndexPerm (B.liftPerm p)
      (inflateMatrix B.projection F)).trans
      (matrixIndexPerm (B.liftPerm q)
        (inflateMatrix B.projection G)) =
      matrixIndexPerm ((B.liftPerm p).trans (B.liftPerm q))
        (inflateMatrix B.projection
          (xorMatrix (reindexMatrix p.symm G) F)) :=
        inflateMatrix_combined_comp B.projection p q
          (B.liftPerm p) (B.liftPerm q)
          (B.projection_liftPerm p) F G
    _ = _ := by rw [B.liftPerm_trans]

end EPPAReducts.TwoGraphs
