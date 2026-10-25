import EPPAReducts.TwoGraphs.ValuationVertex

/-!
# Degenerate triples and Boolean four-point parity

Before transporting the construction to *unordered* three-element sets,
we must show that the ternary parity is false when vertices repeat.
The characteristic-two four-point identity is also restated as an
actual XOR equation on four Boolean triple indicators.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u}

/-- The raw formula vanishes when the first two vertices coincide. -/
theorem rawTripleParity_duplicate_first
    (x y : X) (a b : Valuation X) :
    rawTripleParity x x y a a b = false := by
  cases hx : a x <;> cases hy : a y <;>
    cases hbx : b x <;>
    simp [rawTripleParity, hx, hy, hbx]

/-- The actual valuation-vertex relation has no repeated vertices. -/
theorem vertexTripleParity_duplicate_first
    (u v : ValuationVertex X) :
    vertexTripleParity u u v = false := by
  rcases u with ⟨x, a⟩
  rcases v with ⟨y, b⟩
  induction a using Quotient.inductionOn with
  | _ va =>
    induction b using Quotient.inductionOn with
    | _ vb =>
      change rawTripleParity x x y va va vb = false
      exact rawTripleParity_duplicate_first x y va vb

/-- The same statement if the final two vertices coincide. -/
theorem vertexTripleParity_duplicate_last
    (u v : ValuationVertex X) :
    vertexTripleParity u v v = false := by
  calc
    vertexTripleParity u v v = vertexTripleParity v u v :=
      vertexTripleParity_swap_first_two u v v
    _ = vertexTripleParity v v u :=
      vertexTripleParity_swap_last_two v u v
    _ = false := vertexTripleParity_duplicate_first v u

/-- A Boolean bit is zero in the field F₂ exactly when it is false. -/
theorem boolBit_eq_zero_iff (b : Bool) :
    boolBit b = 0 ↔ b = false := by
  cases b <;> decide

/-- The four-point identity, now stated entirely with Boolean XOR. -/
theorem vertexFourPointParityXor
    (u v w t : ValuationVertex X) :
    Bool.xor
      (Bool.xor
        (Bool.xor (vertexTripleParity u v w)
          (vertexTripleParity u v t))
        (vertexTripleParity u w t))
      (vertexTripleParity v w t) = false := by
  apply (boolBit_eq_zero_iff _).mp
  simp only [boolBit_xor]
  exact vertexFourPointParityModTwo u v w t

end EPPAReducts.TwoGraphs
