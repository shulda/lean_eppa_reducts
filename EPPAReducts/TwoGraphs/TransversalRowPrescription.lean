import EPPAReducts.TwoGraphs.TransversalDiscrepancy
import EPPAReducts.TwoGraphs.CombinedAutomorphism

/-!
# Consistent symmetric matrix prescriptions from a cut potential

For a prescribed index permutation σ and source and target valuation
representatives χ,η, a cut potential c determines the row value

  F(s(x),y) = χ(x)(y) + η(x)(σ(y)) + c(x).

The cut equation is *exactly* the consistency condition requiring
F(s(x),s(y)) = F(s(y),s(x)). This lemma proves that consistency,
including the diagonal case; actual matrix assembly follows.
-/

namespace EPPAReducts.TwoGraphs

universe u v
variable {D : Type u} {X : Type v}

/-- The six-bit form of the elementary cut consistency equation. -/
private theorem xor_row_consistency
    (a b c d e f : Bool)
    (h : Bool.xor (Bool.xor a c) (Bool.xor b d) =
      Bool.xor e f) :
    Bool.xor (Bool.xor a b) e =
      Bool.xor (Bool.xor c d) f := by
  revert h
  cases a <;> cases b <;> cases c <;>
    cases d <;> cases e <;> cases f <;> decide

/-- The row entry prescribed by one vertex of the source transversal. -/
def prescribedTransversalRow
    (σ : Equiv.Perm X)
    (χ η : D → Valuation X) (c : D → Bool)
    (x : D) (y : X) : Bool :=
  Bool.xor
    (Bool.xor (χ x y) (η x (σ y)))
    (c x)

/-- Pair discrepancy in the form used for a transversal whose source
coordinate is src(x) and target coordinate is σ(src(x)). -/
theorem transversalPairDiscrepancy_as_rows
    (src : D → X) (σ : Equiv.Perm X)
    (χ η : D → Valuation X) (x y : D) :
    transversalPairDiscrepancy src (fun d => σ (src d)) χ η x y =
      Bool.xor
        (Bool.xor (χ x (src y)) (χ y (src x)))
        (Bool.xor (η x (σ (src y))) (η y (σ (src x)))) := by
  rfl

/-- Pairwise cut compatibility implies the two symmetric matrix
prescriptions coincide at every pair of source vertices. -/
theorem prescribedTransversalRow_symmetric
    (src : D → X) (σ : Equiv.Perm X)
    (χ η : D → Valuation X) (c : D → Bool)
    (hcut : ∀ x y,
      transversalPairDiscrepancy src (fun d => σ (src d))
        χ η x y = Bool.xor (c x) (c y))
    (x y : D) :
    prescribedTransversalRow σ χ η c x (src y) =
      prescribedTransversalRow σ χ η c y (src x) := by
  have hp := hcut x y
  rw [transversalPairDiscrepancy_as_rows] at hp
  exact xor_row_consistency
    (χ x (src y)) (η x (σ (src y)))
    (χ y (src x)) (η y (σ (src x)))
    (c x) (c y) hp

end EPPAReducts.TwoGraphs
