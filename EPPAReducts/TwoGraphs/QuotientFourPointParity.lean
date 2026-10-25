import EPPAReducts.TwoGraphs.QuotientTripleParity
import EPPAReducts.TwoGraphs.RawFourPointParity

/-!
# Four-point parity on the valuation quotient

This lifts the raw characteristic-two identity to four *actual* vertices
whose valuation components are quotient classes. No choice of
representatives survives into the theorem.

It is the algebraic form of the eventual two-graph four-point axiom;
encoding unordered triples as Finsets and comparing with the human-facing
TwoGraph.fourPointEven predicate are separate downstream tasks.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u}

/-- On any four valuation quotient vertices, the four triple parity bits
sum to zero in F₂, even with repeated first coordinates. -/
theorem quotientFourPointParityModTwo
    (x y z w : X)
    (a b c d : ValuationClass X) :
    boolBit (quotientTripleParity x y z a b c) +
      boolBit (quotientTripleParity x y w a b d) +
      boolBit (quotientTripleParity x z w a c d) +
      boolBit (quotientTripleParity y z w b c d) = 0 := by
  induction a using Quotient.inductionOn with
  | _ va =>
    induction b using Quotient.inductionOn with
    | _ vb =>
      induction c using Quotient.inductionOn with
      | _ vc =>
        induction d using Quotient.inductionOn with
        | _ vd =>
          change
            boolBit (rawTripleParity x y z va vb vc) +
              boolBit (rawTripleParity x y w va vb vd) +
              boolBit (rawTripleParity x z w va vc vd) +
              boolBit (rawTripleParity y z w vb vc vd) = 0
          exact rawFourPointParityModTwo x y z w va vb vc vd

end EPPAReducts.TwoGraphs
