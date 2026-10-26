import EPPAReducts.TwoGraphs.BlockEquivariance

/-!
# Block inflation on faithful combined-action classes

A combined action is represented by an index permutation and a symmetric
Boolean matrix.  Two data records represent the same action precisely when
their actual permutations of valuation vertices agree.

The block construction respects this action kernel, so inflation descends
to the quotient of combined actions.  At this stage the quotient is a
faithful action *set*, not yet equipped with its group operations.
-/

namespace EPPAReducts.TwoGraphs

/-- Data for a genuine combined matrix/index action. -/
structure CombinedActionData (X : Type) where
  indexPerm : Equiv.Perm X
  matrix : X → X → Bool
  symmetric : IsSymmetricBoolMatrix matrix

/-- The actual permutation of valuation vertices represented by the data. -/
def CombinedActionData.action {X : Type} (g : CombinedActionData X) :
    Equiv.Perm (ValuationVertex X) :=
  matrixIndexPerm g.indexPerm g.matrix

/-- Identify exactly those presentations inducing the same permutation. -/
def combinedActionSetoid (X : Type) : Setoid (CombinedActionData X) where
  r g h := g.action = h.action
  iseqv := {
    refl := by intro g; rfl
    symm := by intro g h hgh; exact hgh.symm
    trans := by intro g h k hgh hhk; exact hgh.trans hhk
  }

/-- The faithful quotient of the combined-action data. -/
abbrev CombinedActionClass (X : Type) :=
  Quotient (combinedActionSetoid X)

/-- The actual action of a quotient class. -/
def combinedActionClassPerm {X : Type}
    (g : CombinedActionClass X) :
    Equiv.Perm (ValuationVertex X) :=
  Quotient.liftOn g (fun a => a.action)
    (by intro a b h; exact h)

/-- The action representation is faithful by construction. -/
theorem combinedActionClassPerm_injective {X : Type} :
    Function.Injective (combinedActionClassPerm (X := X)) := by
  intro p q h
  induction p using Quotient.inductionOn with
  | _ a =>
    induction q using Quotient.inductionOn with
    | _ b =>
      apply Quotient.sound
      exact h

/-- Raw block inflation on a combined-action presentation. -/
def BlockCoordinates.inflateActionData {D X : Type}
    (B : BlockCoordinates D X) (g : CombinedActionData D) :
    CombinedActionData X where
  indexPerm := B.liftPerm g.indexPerm
  matrix := inflateMatrix B.projection g.matrix
  symmetric := inflateMatrix_symmetric B.projection g.matrix g.symmetric

/-- Inflation is independent of symmetric matrix representatives and
of the presentation of the combined permutation/index action. -/
theorem BlockCoordinates.inflateActionData_wellDefined
    {D X : Type} [Nonempty D] (B : BlockCoordinates D X)
    (a b : CombinedActionData D) (hab : a.action = b.action) :
    (B.inflateActionData a).action = (B.inflateActionData b).action := by
  letI : Nonempty X :=
    ⟨B.markedEmbedding (Classical.choice ‹Nonempty D›)⟩
  have hab' : matrixIndexPerm a.indexPerm a.matrix =
      matrixIndexPerm b.indexPerm b.matrix := hab
  obtain ⟨hperm, hbit⟩ :=
    (matrixIndexPerm_eq_iff a.indexPerm b.indexPerm
      a.matrix b.matrix a.symmetric b.symmetric).mp hab'
  apply (matrixIndexPerm_eq_iff
    (B.liftPerm a.indexPerm) (B.liftPerm b.indexPerm)
    (inflateMatrix B.projection a.matrix)
    (inflateMatrix B.projection b.matrix)
    (inflateMatrix_symmetric B.projection a.matrix a.symmetric)
    (inflateMatrix_symmetric B.projection b.matrix b.symmetric)).mpr
  exact ⟨congrArg B.liftPerm hperm,
    inflateMatrix_preserves_global_constant
      B.projection a.matrix b.matrix hbit⟩

/-- The block inflation descends to the faithful quotient action. -/
def BlockCoordinates.inflateCombinedActionClass
    {D X : Type} [Nonempty D] (B : BlockCoordinates D X)
    (g : CombinedActionClass D) : CombinedActionClass X :=
  Quotient.liftOn g
    (fun a => Quotient.mk (combinedActionSetoid X) (B.inflateActionData a))
    (by
      intro a b hab
      apply Quotient.sound
      exact B.inflateActionData_wellDefined a b hab)

/-- Equivariance holds on the quotient action without representatives. -/
theorem BlockCoordinates.inflateValuationVertex_combinedActionClass
    {D X : Type} [Nonempty D] (B : BlockCoordinates D X)
    (g : CombinedActionClass D) (w : ValuationVertex D) :
    B.inflateValuationVertex (combinedActionClassPerm g w) =
      combinedActionClassPerm (B.inflateCombinedActionClass g)
        (B.inflateValuationVertex w) := by
  induction g using Quotient.inductionOn with
  | _ a =>
    change B.inflateValuationVertex
        (matrixIndexPerm a.indexPerm a.matrix w) =
      matrixIndexPerm (B.liftPerm a.indexPerm)
        (inflateMatrix B.projection a.matrix)
        (B.inflateValuationVertex w)
    exact B.inflateValuationVertex_matrixIndexPerm a.indexPerm a.matrix w

end EPPAReducts.TwoGraphs
