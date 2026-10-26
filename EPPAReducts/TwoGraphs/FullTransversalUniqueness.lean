import EPPAReducts.TwoGraphs.TransversalCoordinateExtension
import EPPAReducts.TwoGraphs.MatrixKernel

/-!
# Uniqueness of the combined action on a full transversal

Fix one valuation class above every index x in X. The action of
a combined index permutation and Boolean matrix is completely
determined by the images of those chosen valuation vertices.

The key point is that row translations of Q_X are free modulo one
constant complement: two translations agreeing on a *single*
valuation class agree on all valuation classes in the fibre.
This lemma does not require finiteness or matrix symmetry.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u}

/-- Cancel a common Boolean bit in an XOR equation. -/
private theorem xor_left_cancel (u v w : Bool)
    (h : Bool.xor u v = Bool.xor u w) : v = w := by
  cases u <;> cases v <;> cases w <;> simp_all

/-- A Boolean XOR equation with complemented output identifies
complemented second entries. -/
private theorem xor_left_complement (u v w : Bool)
    (h : Bool.xor u v = !(Bool.xor u w)) : v = !w := by
  cases u <;> cases v <;> cases w <;> simp_all

/-- Two row translations of the quotient agreeing on one valuation
class in the same fibre agree on **every** class in that fibre. -/
theorem shiftValuationClassByRow_eq_of_eq_at_one
    (F G : X → X → Bool) (x : X) (q : ValuationClass X)
    (hq : shiftValuationClassByRow F x q =
      shiftValuationClassByRow G x q)
    (p : ValuationClass X) :
    shiftValuationClassByRow F x p =
      shiftValuationClassByRow G x p := by
  induction q using Quotient.inductionOn with
  | _ a =>
    change valuationClass (shiftValuationByRow F x a) =
      valuationClass (shiftValuationByRow G x a) at hq
    rcases (valuationClass_eq_iff _ _).mp hq with heq | heq
    · have hrow (y : X) : F x y = G x y := by
        have hy : Bool.xor (a y) (F x y) =
            Bool.xor (a y) (G x y) := by
          simpa only [shiftValuationByRow] using congrFun heq y
        exact xor_left_cancel _ _ _ hy
      induction p using Quotient.inductionOn with
      | _ b =>
        change valuationClass (shiftValuationByRow F x b) =
          valuationClass (shiftValuationByRow G x b)
        have heqRow : shiftValuationByRow F x b =
            shiftValuationByRow G x b := by
          funext y
          simp only [shiftValuationByRow, hrow y]
        rw [heqRow]
    · have hrow (y : X) : F x y = !(G x y) := by
        have hy : Bool.xor (a y) (F x y) =
            !(Bool.xor (a y) (G x y)) := by
          simpa only [shiftValuationByRow, flipValuation] using congrFun heq y
        exact xor_left_complement _ _ _ hy
      induction p using Quotient.inductionOn with
      | _ b =>
        change valuationClass (shiftValuationByRow F x b) =
          valuationClass (shiftValuationByRow G x b)
        have heqRow : shiftValuationByRow F x b =
            flipValuation (shiftValuationByRow G x b) := by
          funext y
          change Bool.xor (b y) (F x y) = !(Bool.xor (b y) (G x y))
          rw [hrow y]
          cases hb : b y <;> cases hg : G x y <;>
            simp [hb, hg]
        rw [heqRow, valuationClass_flip]

/-- If matrix row shifts agree on one chosen valuation class
over each x, then they agree as permutations of *all* vertices. -/
theorem rowShiftPerm_eq_of_full_transversal
    (F G : X → X → Bool) (q : X → ValuationClass X)
    (h : ∀ x, shiftValuationClassByRow F x (q x) =
      shiftValuationClassByRow G x (q x)) :
    rowShiftPerm F = rowShiftPerm G := by
  apply Equiv.ext
  rintro ⟨x, p⟩
  change (x, shiftValuationClassByRow F x p) =
    (x, shiftValuationClassByRow G x p)
  exact congrArg (fun z : ValuationClass X => (x, z))
    (shiftValuationClassByRow_eq_of_eq_at_one F G x (q x) (h x) p)

/-- A full transversal determines any combined index/matrix action:
equality of images of one vertex above each index implies equality
of the permutations on the **entire** valuation witness.
This is stronger than uniqueness only modulo global matrix constants
and does not assume symmetry of F,G. -/
theorem matrixIndexPerm_eq_of_full_transversal
    (σ τ : Equiv.Perm X) (F G : X → X → Bool)
    (q : X → ValuationClass X)
    (h : ∀ x,
      matrixIndexPerm σ F (x, q x) =
        matrixIndexPerm τ G (x, q x)) :
    matrixIndexPerm σ F = matrixIndexPerm τ G := by
  have hσ : σ = τ := by
    apply Equiv.ext
    intro x
    have hx := congrArg Prod.fst (h x)
    exact hx
  subst τ
  have hrows : ∀ x,
      shiftValuationClassByRow F x (q x) =
        shiftValuationClassByRow G x (q x) := by
    intro x
    have hx := h x
    change (indexPermVertex σ)
        (x, shiftValuationClassByRow F x (q x)) =
      (indexPermVertex σ)
        (x, shiftValuationClassByRow G x (q x)) at hx
    have hy := (indexPermVertex σ).injective hx
    exact congrArg Prod.snd hy
  have hFG : rowShiftPerm F = rowShiftPerm G :=
    rowShiftPerm_eq_of_full_transversal F G q hrows
  unfold matrixIndexPerm
  rw [hFG]

end EPPAReducts.TwoGraphs
