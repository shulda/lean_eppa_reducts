import EPPAReducts.TwoGraphs.RawTripleParity

/-!
# Descent of the triple parity formula to quotient valuations

This file constructs the actual Boolean triple-parity function on three
valuation classes. It is not yet the complete finite two-graph: we must
still prove permutation symmetry and four-point even parity.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u}

/-- Equal representatives up to independent pointwise complements yield
equal values of the raw six-entry parity expression. -/
theorem rawTripleParity_congr
    (x y z : X)
    (a a' b b' c c' : Valuation X)
    (ha : a = a' ∨ a = flipValuation a')
    (hb : b = b' ∨ b = flipValuation b')
    (hc : c = c' ∨ c = flipValuation c') :
    rawTripleParity x y z a b c =
      rawTripleParity x y z a' b' c' := by
  have h₁ : rawTripleParity x y z a b c =
      rawTripleParity x y z a' b c := by
    rcases ha with ha | ha
    · rw [ha]
    · rw [ha, rawTripleParity_flip_first]
  have h₂ : rawTripleParity x y z a' b c =
      rawTripleParity x y z a' b' c := by
    rcases hb with hb | hb
    · rw [hb]
    · rw [hb, rawTripleParity_flip_second]
  have h₃ : rawTripleParity x y z a' b' c =
      rawTripleParity x y z a' b' c' := by
    rcases hc with hc | hc
    · rw [hc]
    · rw [hc, rawTripleParity_flip_third]
  exact h₁.trans (h₂.trans h₃)

/-- Well-defined parity on quotient valuation classes, for arbitrary first
coordinates x,y,z (including repeated first coordinates). -/
def quotientTripleParity
    (x y z : X) (a b c : ValuationClass X) : Bool :=
  Quotient.liftOn a
    (fun va =>
      Quotient.liftOn b
        (fun vb =>
          Quotient.liftOn c
            (fun vc => rawTripleParity x y z va vb vc)
            (by
              intro vc vc' hc
              exact rawTripleParity_congr x y z va va vb vb vc vc'
                (Or.inl rfl) (Or.inl rfl) hc))
        (by
          intro vb vb' hb
          induction c using Quotient.inductionOn with
          | _ vc =>
            exact rawTripleParity_congr x y z va va vb vb' vc vc
              (Or.inl rfl) hb (Or.inl rfl)))
    (by
      intro va va' ha
      induction b using Quotient.inductionOn with
      | _ vb =>
        induction c using Quotient.inductionOn with
        | _ vc =>
          exact rawTripleParity_congr x y z va va' vb vb vc vc
            ha (Or.inl rfl) (Or.inl rfl))

end EPPAReducts.TwoGraphs
