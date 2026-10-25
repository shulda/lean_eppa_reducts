import EPPAReducts.TwoGraphs.ValuationQuotient

/-!
# The raw parity formula on three valuation vertices

Before descending to the valuation quotient, we verify that the
six-term Boolean XOR expression is unchanged if any one of the three
valuation representatives is complemented. This is the essential
well-definedness obligation even when first coordinates coincide.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u}

/-- Parity of the six valuation entries at the other vertices'
first coordinates (the sum of three unordered-pair contributions). -/
def rawTripleParity (x y z : X)
    (a b c : Valuation X) : Bool :=
  Bool.xor
    (Bool.xor
      (Bool.xor (a y) (b x))
      (Bool.xor (a z) (c x)))
    (Bool.xor (b z) (c y))

/-- Complementing the first valuation changes exactly two summands. -/
theorem rawTripleParity_flip_first
    (x y z : X) (a b c : Valuation X) :
    rawTripleParity x y z (flipValuation a) b c =
      rawTripleParity x y z a b c := by
  cases h₁ : a y <;> cases h₂ : b x <;>
    cases h₃ : a z <;> cases h₄ : c x <;>
    cases h₅ : b z <;> cases h₆ : c y <;>
    simp [rawTripleParity, flipValuation, h₁, h₂, h₃, h₄, h₅, h₆]

/-- Complementing the second valuation changes exactly two summands. -/
theorem rawTripleParity_flip_second
    (x y z : X) (a b c : Valuation X) :
    rawTripleParity x y z a (flipValuation b) c =
      rawTripleParity x y z a b c := by
  cases h₁ : a y <;> cases h₂ : b x <;>
    cases h₃ : a z <;> cases h₄ : c x <;>
    cases h₅ : b z <;> cases h₆ : c y <;>
    simp [rawTripleParity, flipValuation, h₁, h₂, h₃, h₄, h₅, h₆]

/-- Complementing the third valuation changes exactly two summands. -/
theorem rawTripleParity_flip_third
    (x y z : X) (a b c : Valuation X) :
    rawTripleParity x y z a b (flipValuation c) =
      rawTripleParity x y z a b c := by
  cases h₁ : a y <;> cases h₂ : b x <;>
    cases h₃ : a z <;> cases h₄ : c x <;>
    cases h₅ : b z <;> cases h₆ : c y <;>
    simp [rawTripleParity, flipValuation, h₁, h₂, h₃, h₄, h₅, h₆]

end EPPAReducts.TwoGraphs
