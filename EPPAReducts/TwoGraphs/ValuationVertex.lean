import EPPAReducts.TwoGraphs.QuotientFourPointParity
import Mathlib.Data.Fintype.Pi

/-!
# Concrete finite valuation vertices and their symmetric ternary parity

The carrier of the proposed two-graph witness is the genuine product
X × Q_X. These lemmas retain the precise four-point equation on
arbitrary four vertices, including repeated first coordinates.
The final induced relation on unordered triples is a separate
proof obligation; the statements here alone are not coherent EPPA.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u}

/-- A vertex consists of one fibre coordinate and one quotient valuation. -/
abbrev ValuationVertex (X : Type u) := X × ValuationClass X

/-- The candidate three-vertex relation on ordered vertices. -/
def vertexTripleParity (u v w : ValuationVertex X) : Bool :=
  quotientTripleParity u.1 v.1 w.1 u.2 v.2 w.2

/-- Swapping the first two vertices leaves the ternary relation unchanged. -/
theorem vertexTripleParity_swap_first_two
    (u v w : ValuationVertex X) :
    vertexTripleParity u v w = vertexTripleParity v u w := by
  exact quotientTripleParity_swap_first_two u.1 v.1 w.1 u.2 v.2 w.2

/-- Swapping the last two vertices leaves the ternary relation unchanged. -/
theorem vertexTripleParity_swap_last_two
    (u v w : ValuationVertex X) :
    vertexTripleParity u v w = vertexTripleParity u w v := by
  exact quotientTripleParity_swap_last_two u.1 v.1 w.1 u.2 v.2 w.2

/-- Four-point cancellation holds on all ordered quadruples of
valuation vertices, regardless of repeated fibre coordinates. -/
theorem vertexFourPointParityModTwo
    (u v w t : ValuationVertex X) :
    boolBit (vertexTripleParity u v w) +
      boolBit (vertexTripleParity u v t) +
      boolBit (vertexTripleParity u w t) +
      boolBit (vertexTripleParity v w t) = 0 := by
  exact quotientFourPointParityModTwo
    u.1 v.1 w.1 t.1 u.2 v.2 w.2 t.2

/-- Quotient valuations on a finite index type form a finite type. -/
instance valuationClass_finite [Finite X] : Finite (ValuationClass X) := by
  classical
  haveI : Finite (Valuation X) := inferInstance
  exact Quotient.finite (valuationSetoid X)

/-- Consequently the whole valuation witness carrier is finite. -/
instance valuationVertex_finite [Finite X] : Finite (ValuationVertex X) := by
  infer_instance

end EPPAReducts.TwoGraphs
