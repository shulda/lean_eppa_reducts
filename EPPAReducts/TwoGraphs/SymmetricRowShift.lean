import EPPAReducts.TwoGraphs.RawFourPointParity

/-!
# Symmetric matrix row translations preserve raw triple parity

The key local algebra for the finite automorphism group.
For a symmetric Boolean matrix F, shift each vertex valuation
χ_x at coordinate y by F(x,y). Every unordered-pair contribution
receives two equal F-terms and the sum vanishes in characteristic two.

This file establishes the raw formula identity for all vertex triples,
including those with repeated first coordinates. A full quotient action,
permutation pullback, and the coherent EPPA section are not yet proved.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u}

/-- A symmetric Boolean matrix indexed by the prospective fibres. -/
def IsSymmetricBoolMatrix (F : X → X → Bool) : Prop :=
  ∀ x y, F x y = F y x

/-- Translation of one valuation by a row of a Boolean matrix. -/
def shiftValuationByRow (F : X → X → Bool)
    (x : X) (a : Valuation X) : Valuation X :=
  fun y => Bool.xor (a y) (F x y)

/-- Converting a bit to ZMod 2 is an injective operation. -/
theorem boolBit_injective : Function.Injective boolBit := by
  intro b c h
  cases b <;> cases c <;> simp [boolBit] at h ⊢

/-- Simultaneous symmetric row translations preserve the six-bit parity,
even when some of x,y,z coincide. -/
theorem rawTripleParity_symmetricRowShift
    (F : X → X → Bool) (hF : IsSymmetricBoolMatrix F)
    (x y z : X) (a b c : Valuation X) :
    rawTripleParity x y z
        (shiftValuationByRow F x a)
        (shiftValuationByRow F y b)
        (shiftValuationByRow F z c) =
      rawTripleParity x y z a b c := by
  apply boolBit_injective
  simp only [boolBit_rawTripleParity, shiftValuationByRow, boolBit_xor]
  rw [hF y x, hF z x, hF z y]
  ring_nf
  have h₂ : (2 : ZMod 2) = 0 := by decide
  simp [h₂]

end EPPAReducts.TwoGraphs
