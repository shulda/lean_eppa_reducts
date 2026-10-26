import EPPAReducts.TwoGraphs.BlockDivisibility
import EPPAReducts.TwoGraphs.TransversalLiteralExtension

/-!
# Induced embedding of valuation two-graphs by block inflation

Given marked block coordinates B : D × I ≃ X with projection r,
precomposing every D-valuation with r embeds its complement class in
the valuation quotient on X. Together with the marked vertex
embedding, this gives an *induced embedding* C_D ↪ C_X in the exact
author-approved TwoGraph API.

Faithful quotient-valuations are proved by restricting inflated
valuations back along the marked copy of D.
Equivariance with the matrix/index action is the next obligation.
-/

namespace EPPAReducts.TwoGraphs

variable {D X : Type}

/-- Extend a valuation from D to X by making it constant
within the fibres of the block retraction r : X → D. -/
def inflateValuation (r : X → D) (a : Valuation D) : Valuation X :=
  fun x => a (r x)

/-- Inflating a valuation commutes with its full complement. -/
theorem inflateValuation_flip
    (r : X → D) (a : Valuation D) :
    inflateValuation r (flipValuation a) =
      flipValuation (inflateValuation r a) := by
  rfl

/-- A well-defined map between complement quotient spaces. -/
def inflateValuationClass
    (r : X → D) (q : ValuationClass D) : ValuationClass X :=
  Quotient.liftOn q
    (fun a => valuationClass (inflateValuation r a))
    (by
      intro a b h
      rcases h with heq | heq
      · rw [heq]
      · rw [heq, inflateValuation_flip, valuationClass_flip])

@[simp] theorem inflateValuationClass_mk
    (r : X → D) (a : Valuation D) :
    inflateValuationClass r (valuationClass a) =
      valuationClass (inflateValuation r a) := by
  rfl

/-- If r has a section, inflation is injective on quotient
valuation classes, not just on chosen raw representatives. -/
theorem inflateValuationClass_injective
    (r : X → D) (ι : D → X)
    (hsection : ∀ d, r (ι d) = d) :
    Function.Injective (inflateValuationClass r) := by
  intro a b h
  induction a using Quotient.inductionOn with
  | _ va =>
    induction b using Quotient.inductionOn with
    | _ vb =>
      change valuationClass (inflateValuation r va) =
        valuationClass (inflateValuation r vb) at h
      apply Quotient.sound
      rcases (valuationClass_eq_iff _ _).mp h with heq | heq
      · left
        funext d
        have hd := congrFun heq (ι d)
        simpa [inflateValuation, hsection] using hd
      · right
        funext d
        have hd := congrFun heq (ι d)
        simpa [inflateValuation, flipValuation, hsection] using hd

/-- The induced injection C_D ↪ C_X using the marked copy of D
and inflation of quotient valuations. -/
def BlockCoordinates.inflateValuationVertex
    (B : BlockCoordinates D X) : ValuationVertex D ↪ ValuationVertex X where
  toFun := fun v =>
    (B.markedEmbedding v.1, inflateValuationClass B.projection v.2)
  inj' := by
    intro v w h
    apply Prod.ext
    · exact B.markedEmbedding.injective (congrArg Prod.fst h)
    · exact inflateValuationClass_injective
        B.projection B.markedEmbedding B.projection_marked
        (congrArg Prod.snd h)

/-- Triple parity of quotient valuations is unchanged by inflation.
The marked block is a genuine section of the retraction. -/
theorem BlockCoordinates.inflateValuationVertex_tripleParity
    (B : BlockCoordinates D X)
    (u v w : ValuationVertex D) :
    vertexTripleParity (B.inflateValuationVertex u)
      (B.inflateValuationVertex v) (B.inflateValuationVertex w) =
      vertexTripleParity u v w := by
  rcases u with ⟨d, a⟩
  rcases v with ⟨e, b⟩
  rcases w with ⟨f, c⟩
  induction a using Quotient.inductionOn with
  | _ va =>
    induction b using Quotient.inductionOn with
    | _ vb =>
      induction c using Quotient.inductionOn with
      | _ vc =>
        change
          rawTripleParity (B.markedEmbedding d)
            (B.markedEmbedding e) (B.markedEmbedding f)
            (inflateValuation B.projection va)
            (inflateValuation B.projection vb)
            (inflateValuation B.projection vc) =
          rawTripleParity d e f va vb vc
        simp [rawTripleParity, inflateValuation, B.projection_marked]

/-- The block inflation is an **induced embedding** of actual
two-graphs in the exact approved HumanTargets API. -/
theorem BlockCoordinates.inflateValuationVertex_induced
    (B : BlockCoordinates D X)
    [DecidableEq D] [DecidableEq X]
    [DecidableEq (ValuationVertex D)]
    [DecidableEq (ValuationVertex X)] :
    HumanTargets.IsInducedTwoGraphEmbedding
      (valuationTwoGraph D) (valuationTwoGraph X)
      B.inflateValuationVertex := by
  intro u v w
  rw [valuationTwoGraph_triple_eq_vertexParity,
    valuationTwoGraph_triple_eq_vertexParity]
  exact (B.inflateValuationVertex_tripleParity u v w).symm

end EPPAReducts.TwoGraphs
