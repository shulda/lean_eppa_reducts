import EPPAReducts.TwoGraphs.RawTripleParity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Four-point parity of the raw valuation construction

Every unordered pair contribution occurs in exactly two of the four
triples. Encoding Boolean XOR in ZMod 2 makes the cancellation an
abelian-ring identity. No distinctness of the first coordinates is
assumed, as required by the valuation witness.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u}

/-- Convert a Boolean bit to the field with two elements. -/
def boolBit (b : Bool) : ZMod 2 :=
  if b then 1 else 0

/-- XOR of Boolean bits becomes addition in the two-element field. -/
theorem boolBit_xor (p q : Bool) :
    boolBit (Bool.xor p q) = boolBit p + boolBit q := by
  cases p <;> cases q <;> decide

/-- The six-entry formula is the sum of the contributions of the
three unordered pairs, in the additive field F₂. -/
theorem boolBit_rawTripleParity
    (x y z : X) (a b c : Valuation X) :
    boolBit (rawTripleParity x y z a b c) =
      (boolBit (a y) + boolBit (b x)) +
      (boolBit (a z) + boolBit (c x)) +
      (boolBit (b z) + boolBit (c y)) := by
  simp only [rawTripleParity, boolBit_xor]

/-- The parity of the four triples on four labelled valuation vertices
is even; the formula is valid also if first coordinates coincide. -/
theorem rawFourPointParityModTwo
    (x y z w : X) (a b c d : Valuation X) :
    boolBit (rawTripleParity x y z a b c) +
      boolBit (rawTripleParity x y w a b d) +
      boolBit (rawTripleParity x z w a c d) +
      boolBit (rawTripleParity y z w b c d) = 0 := by
  simp only [boolBit_rawTripleParity]
  ring

end EPPAReducts.TwoGraphs
