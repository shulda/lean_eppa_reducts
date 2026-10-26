import EPPAReducts.TwoGraphs.ConjugatedTransversalLift

/-!
# Simultaneous lifts under the exact finite divisibility hypothesis

For any finite nonempty index set D injected into a finite X with
|D| dividing |X|, and any chosen D-indexed transversal in C_X,
there is a simultaneous composition-preserving choice of extensions
of all induced automorphisms of that transversal.

The statement quantifies over the original prescribed embedding ι;
the block coordinates and conjugating automorphism are chosen once,
independently of individual group elements.

This is a subgroup section for transversals, not the final
coherent EPPA witness for arbitrary two-graphs.
-/

namespace EPPAReducts.TwoGraphs

variable {D X : Type}

/-- An automorphism of the chosen D-indexed induced transversal of
C_X, expressed on its first-coordinate permutation. -/
def PreservesEmbeddedTransversal
    (ι : D ↪ X) (χ : D → Valuation X) (p : Equiv.Perm D) : Prop :=
  ∀ d e f : D,
    rawTripleParity (ι d) (ι e) (ι f)
      (χ d) (χ e) (χ f) =
    rawTripleParity (ι (p d)) (ι (p e)) (ι (p f))
      (χ (p d)) (χ (p e)) (χ (p f))

theorem preservesEmbeddedTransversal_refl
    (ι : D ↪ X) (χ : D → Valuation X) :
    PreservesEmbeddedTransversal ι χ (Equiv.refl D) := by
  intro d e f
  rfl

theorem preservesEmbeddedTransversal_trans
    (ι : D ↪ X) (χ : D → Valuation X)
    (p q : Equiv.Perm D)
    (hp : PreservesEmbeddedTransversal ι χ p)
    (hq : PreservesEmbeddedTransversal ι χ q) :
    PreservesEmbeddedTransversal ι χ (p.trans q) := by
  intro d e f
  exact (hp d e f).trans (hq (p d) (p e) (p f))

/-- **Simultaneous subgroup lift for every divisible transversal.**
The same choice of extensions preserves the identity and every
composition.  This is the paper's subgroup-section lemma in the
internal valuation-transversal formulation. -/
theorem exists_divisibleTransversal_coherentLift
    [Fintype D] [Fintype X] [Nonempty D]
    (ι : D ↪ X)
    (hdiv : Fintype.card D ∣ Fintype.card X)
    (χ : D → Valuation X) :
    ∃ lift :
        (p : Equiv.Perm D) →
        PreservesEmbeddedTransversal ι χ p →
        Equiv.Perm (ValuationVertex X),
      (∀ p hp,
        HumanTargets.IsTwoGraphAutomorphism (valuationTwoGraph X)
          (lift p hp)) ∧
      (∀ p hp d,
        lift p hp (ι d, valuationClass (χ d)) =
          (ι (p d), valuationClass (χ (p d)))) ∧
      (lift (Equiv.refl D) (preservesEmbeddedTransversal_refl ι χ) =
        Equiv.refl (ValuationVertex X)) ∧
      (∀ p q
        (hp : PreservesEmbeddedTransversal ι χ p)
        (hq : PreservesEmbeddedTransversal ι χ q),
        (lift p hp).trans (lift q hq) =
        lift (p.trans q)
          (preservesEmbeddedTransversal_trans ι χ p q hp hq)) := by
  classical
  obtain ⟨B, hB⟩ := exists_markedBlockCoordinates_of_dvd ι hdiv
  have convert (p : Equiv.Perm D)
      (hp : PreservesEmbeddedTransversal ι χ p) :
      B.PreservesMarkedTransversal χ p := by
    intro d e f
    simpa only [hB] using hp d e f
  let lift : (p : Equiv.Perm D) →
      PreservesEmbeddedTransversal ι χ p →
      Equiv.Perm (ValuationVertex X) :=
    fun p hp => B.conjugatedMarkedLift χ p (convert p hp)
  refine ⟨lift, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact B.conjugatedMarkedLift_isAutomorphism
      χ p (convert p hp)
  · intro p hp d
    have h := B.conjugatedMarkedLift_marked
      χ p (convert p hp) d
    simpa only [hB] using h
  · change B.conjugatedMarkedLift χ (Equiv.refl D)
        (convert _ (preservesEmbeddedTransversal_refl ι χ)) =
        Equiv.refl (ValuationVertex X)
    exact B.conjugatedMarkedLift_refl χ
  · intro p q hp hq
    change (B.conjugatedMarkedLift χ p (convert p hp)).trans
      (B.conjugatedMarkedLift χ q (convert q hq)) =
      B.conjugatedMarkedLift χ (p.trans q)
        (convert (p.trans q)
          (preservesEmbeddedTransversal_trans ι χ p q hp hq))
    exact B.conjugatedMarkedLift_trans χ p q
      (convert p hp) (convert q hq)

end EPPAReducts.TwoGraphs
