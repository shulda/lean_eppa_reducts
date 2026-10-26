import EPPAReducts.TwoGraphs.FullTransversalBlockLift

/-!
# Restricting valuation transversals to an embedded index set

A transversal of C_X indexed by an injection ι : D ↪ X determines
a full transversal of C_D by restricting every valuation to ι(D).
The two induced two-graph structures agree exactly.  In particular,
the block-inflated restricted full transversal and the original
transversal of C_X are induced-isomorphic by the map preserving first
coordinates.

This is the comparison needed for the conjugation step of coherent EPPA.
-/

namespace EPPAReducts.TwoGraphs

variable {D X : Type}

/-- Precompose a valuation of X with an arbitrary map from D. -/
def restrictValuation (ι : D → X) (a : Valuation X) : Valuation D :=
  fun d => a (ι d)

/-- Restriction commutes with pointwise complementation. -/
theorem restrictValuation_flip (ι : D → X) (a : Valuation X) :
    restrictValuation ι (flipValuation a) =
      flipValuation (restrictValuation ι a) := by
  rfl

/-- Restriction descends to complement classes. -/
def restrictValuationClass (ι : D → X)
    (q : ValuationClass X) : ValuationClass D :=
  Quotient.liftOn q
    (fun a => valuationClass (restrictValuation ι a))
    (by
      intro a b h
      rcases h with hab | hab
      · rw [hab]
      · rw [hab, restrictValuation_flip, valuationClass_flip])

@[simp] theorem restrictValuationClass_mk
    (ι : D → X) (a : Valuation X) :
    restrictValuationClass ι (valuationClass a) =
      valuationClass (restrictValuation ι a) := by
  rfl

/-- All six pair evaluations commute with valuation restriction. -/
theorem rawTripleParity_restrict
    (ι : D → X) (d e f : D)
    (a b c : Valuation X) :
    rawTripleParity d e f
        (restrictValuation ι a)
        (restrictValuation ι b)
        (restrictValuation ι c) =
      rawTripleParity (ι d) (ι e) (ι f) a b c := by
  rfl

/-- Restriction preserves triple parity on the complement quotients. -/
theorem quotientTripleParity_restrict
    (ι : D → X) (d e f : D)
    (a b c : ValuationClass X) :
    quotientTripleParity d e f
        (restrictValuationClass ι a)
        (restrictValuationClass ι b)
        (restrictValuationClass ι c) =
      quotientTripleParity (ι d) (ι e) (ι f) a b c := by
  induction a using Quotient.inductionOn with
  | _ va =>
    induction b using Quotient.inductionOn with
    | _ vb =>
      induction c using Quotient.inductionOn with
      | _ vc =>
        change rawTripleParity d e f
            (restrictValuation ι va)
            (restrictValuation ι vb)
            (restrictValuation ι vc) =
          rawTripleParity (ι d) (ι e) (ι f) va vb vc
        exact rawTripleParity_restrict ι d e f va vb vc

/-- The full D-transversal obtained by restricting the original
chosen X-valuations to the embedded subset ι(D). -/
def restrictedTransversalValuations
    (ι : D → X) (χ : D → Valuation X) : D → Valuation D :=
  fun d => restrictValuation ι (χ d)

/-- The full restricted D-transversal and the original X-transversal
have precisely the same triple parity, including degenerate triples. -/
theorem restrictedTransversal_parity
    (ι : D → X) (χ : D → Valuation X) (d e f : D) :
    rawTripleParity d e f
      (restrictedTransversalValuations ι χ d)
      (restrictedTransversalValuations ι χ e)
      (restrictedTransversalValuations ι χ f) =
    rawTripleParity (ι d) (ι e) (ι f)
      (χ d) (χ e) (χ f) := by
  exact rawTripleParity_restrict ι d e f (χ d) (χ e) (χ f)

/-- The block-inflated restricted transversal is induced-isomorphic
to the original transversal inside C_X via the shared index d ∈ D.
Only the values on the marked subset, not on the rest of X, matter. -/
theorem BlockCoordinates.restrictedTransversal_induced_iso
    (B : BlockCoordinates D X)
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (χ : D → Valuation X) (d e f : D) :
    (valuationTwoGraph X).isTriple
      (HumanTargets.triple
        (B.inflateValuationVertex
          (d, valuationClass (restrictedTransversalValuations
            B.markedEmbedding χ d)))
        (B.inflateValuationVertex
          (e, valuationClass (restrictedTransversalValuations
            B.markedEmbedding χ e)))
        (B.inflateValuationVertex
          (f, valuationClass (restrictedTransversalValuations
            B.markedEmbedding χ f)))) =
    (valuationTwoGraph X).isTriple
      (HumanTargets.triple
        (B.markedEmbedding d, valuationClass (χ d))
        (B.markedEmbedding e, valuationClass (χ e))
        (B.markedEmbedding f, valuationClass (χ f))) := by
  rw [valuationTwoGraph_triple_eq_vertexParity,
      valuationTwoGraph_triple_eq_vertexParity]
  calc
    vertexTripleParity
      (B.inflateValuationVertex
        (d, valuationClass (restrictedTransversalValuations
          B.markedEmbedding χ d)))
      (B.inflateValuationVertex
        (e, valuationClass (restrictedTransversalValuations
          B.markedEmbedding χ e)))
      (B.inflateValuationVertex
        (f, valuationClass (restrictedTransversalValuations
          B.markedEmbedding χ f))) =
      vertexTripleParity
        (d, valuationClass (restrictedTransversalValuations
          B.markedEmbedding χ d))
        (e, valuationClass (restrictedTransversalValuations
          B.markedEmbedding χ e))
        (f, valuationClass (restrictedTransversalValuations
          B.markedEmbedding χ f)) :=
          B.inflateValuationVertex_tripleParity _ _ _
    _ = vertexTripleParity
        (B.markedEmbedding d, valuationClass (χ d))
        (B.markedEmbedding e, valuationClass (χ e))
        (B.markedEmbedding f, valuationClass (χ f)) := by
      change rawTripleParity d e f
          (restrictValuation B.markedEmbedding (χ d))
          (restrictValuation B.markedEmbedding (χ e))
          (restrictValuation B.markedEmbedding (χ f)) =
        rawTripleParity (B.markedEmbedding d)
          (B.markedEmbedding e) (B.markedEmbedding f)
          (χ d) (χ e) (χ f)
      rfl

end EPPAReducts.TwoGraphs
