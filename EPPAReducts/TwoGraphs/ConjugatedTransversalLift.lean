import EPPAReducts.TwoGraphs.TransversalConjugator

/-!
# Coherent subgroup lifts for a chosen marked transversal

The same ambient automorphism γ carries the block-inflated restriction
of a chosen transversal to the chosen transversal itself.  Conjugating
the already proved homomorphic block lift by γ therefore yields genuine
automorphisms extending all induced automorphisms of the original
transversal, while strictly preserving identity and composition.

The parameter B is still a marked block decomposition; choosing B
from cardinal divisibility and using abstract coherentisation follow.
-/

namespace EPPAReducts.TwoGraphs

variable {D X : Type}

/-- A permutation of D preserves the induced two-graph relation on the
chosen D-indexed transversal of C_X. -/
def BlockCoordinates.PreservesMarkedTransversal
    (B : BlockCoordinates D X)
    (χ : D → Valuation X) (p : Equiv.Perm D) : Prop :=
  ∀ d e f : D,
    rawTripleParity (B.markedEmbedding d) (B.markedEmbedding e)
      (B.markedEmbedding f) (χ d) (χ e) (χ f) =
    rawTripleParity (B.markedEmbedding (p d))
      (B.markedEmbedding (p e)) (B.markedEmbedding (p f))
      (χ (p d)) (χ (p e)) (χ (p f))

theorem BlockCoordinates.preservesMarkedTransversal_refl
    (B : BlockCoordinates D X) (χ : D → Valuation X) :
    B.PreservesMarkedTransversal χ (Equiv.refl D) := by
  intro d e f
  rfl

theorem BlockCoordinates.preservesMarkedTransversal_trans
    (B : BlockCoordinates D X) (χ : D → Valuation X)
    (p q : Equiv.Perm D)
    (hp : B.PreservesMarkedTransversal χ p)
    (hq : B.PreservesMarkedTransversal χ q) :
    B.PreservesMarkedTransversal χ (p.trans q) := by
  intro d e f
  exact (hp d e f).trans (hq (p d) (p e) (p f))

/-- Preserving the original embedded transversal is equivalent to
preserving the corresponding full restricted D-transversal. -/
theorem BlockCoordinates.preservesRestrictedTransversal
    (B : BlockCoordinates D X) (χ : D → Valuation X)
    (p : Equiv.Perm D)
    (hp : B.PreservesMarkedTransversal χ p) :
    PreservesFullTransversal
      (restrictedTransversalValuations B.markedEmbedding χ) p := by
  intro d e f
  calc
    rawTripleParity d e f
      (restrictedTransversalValuations B.markedEmbedding χ d)
      (restrictedTransversalValuations B.markedEmbedding χ e)
      (restrictedTransversalValuations B.markedEmbedding χ f) =
      rawTripleParity (B.markedEmbedding d) (B.markedEmbedding e)
        (B.markedEmbedding f) (χ d) (χ e) (χ f) :=
          restrictedTransversal_parity B.markedEmbedding χ d e f
    _ = rawTripleParity (B.markedEmbedding (p d))
          (B.markedEmbedding (p e)) (B.markedEmbedding (p f))
          (χ (p d)) (χ (p e)) (χ (p f)) := hp d e f
    _ = rawTripleParity (p d) (p e) (p f)
          (restrictedTransversalValuations B.markedEmbedding χ (p d))
          (restrictedTransversalValuations B.markedEmbedding χ (p e))
          (restrictedTransversalValuations B.markedEmbedding χ (p f)) :=
            (restrictedTransversal_parity B.markedEmbedding χ
              (p d) (p e) (p f)).symm

/-- Choose the *same* conjugator for every automorphism of the given
marked transversal. -/
noncomputable def BlockCoordinates.canonicalTransversalConjugator
    (B : BlockCoordinates D X)
    [Fintype D] [DecidableEq X]
    [DecidableEq (ValuationVertex X)]
    (χ : D → Valuation X) :
    Equiv.Perm (ValuationVertex X) :=
  Classical.choose (B.exists_conjugatingAutomorphism χ)

theorem BlockCoordinates.canonicalTransversalConjugator_isAutomorphism
    (B : BlockCoordinates D X)
    [Fintype D] [DecidableEq X]
    [DecidableEq (ValuationVertex X)]
    (χ : D → Valuation X) :
    HumanTargets.IsTwoGraphAutomorphism (valuationTwoGraph X)
      (B.canonicalTransversalConjugator χ) :=
  (Classical.choose_spec (B.exists_conjugatingAutomorphism χ)).1

theorem BlockCoordinates.canonicalTransversalConjugator_marked
    (B : BlockCoordinates D X)
    [Fintype D] [DecidableEq X]
    [DecidableEq (ValuationVertex X)]
    (χ : D → Valuation X) (d : D) :
    B.canonicalTransversalConjugator χ
      (B.inflateValuationVertex
        (d, valuationClass (restrictedTransversalValuations
          B.markedEmbedding χ d))) =
      (B.markedEmbedding d, valuationClass (χ d)) :=
  (Classical.choose_spec (B.exists_conjugatingAutomorphism χ)).2 d

/-- An inverse of a two-graph automorphism is again an automorphism. -/
theorem twoGraphAutomorphism_symm
    {V : Type} (A : HumanTargets.TwoGraph V)
    (g : Equiv.Perm V)
    (hg : HumanTargets.IsTwoGraphAutomorphism A g) :
    HumanTargets.IsTwoGraphAutomorphism A g.symm := by
  intro x y z
  have h := hg (g.symm x) (g.symm y) (g.symm z)
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- Conjugate the canonical block lift by the fixed transversal
conjugator.  It acts directly on the *original* D-transversal. -/
noncomputable def BlockCoordinates.conjugatedMarkedLift
    (B : BlockCoordinates D X)
    [Fintype D] [DecidableEq D] [Nonempty D]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (χ : D → Valuation X) (p : Equiv.Perm D)
    (hp : B.PreservesMarkedTransversal χ p) :
    Equiv.Perm (ValuationVertex X) :=
  (B.canonicalTransversalConjugator χ).symm.trans
    (B.inflatedCanonicalFullTransversalLift
      (restrictedTransversalValuations B.markedEmbedding χ) p
      (B.preservesRestrictedTransversal χ p hp)) |>.trans
      (B.canonicalTransversalConjugator χ)

/-- The conjugated full-transversal lift is an actual automorphism
of the entire literal valuation two-graph. -/
theorem BlockCoordinates.conjugatedMarkedLift_isAutomorphism
    (B : BlockCoordinates D X)
    [Fintype D] [DecidableEq D] [Nonempty D]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (χ : D → Valuation X) (p : Equiv.Perm D)
    (hp : B.PreservesMarkedTransversal χ p) :
    HumanTargets.IsTwoGraphAutomorphism (valuationTwoGraph X)
      (B.conjugatedMarkedLift χ p hp) := by
  let γ := B.canonicalTransversalConjugator χ
  let χD := restrictedTransversalValuations B.markedEmbedding χ
  let hpD := B.preservesRestrictedTransversal χ p hp
  have hγ := B.canonicalTransversalConjugator_isAutomorphism χ
  have hγinv := twoGraphAutomorphism_symm (valuationTwoGraph X) γ hγ
  have hL := B.inflatedCanonicalFullTransversalLift_isAutomorphism χD p hpD
  exact twoGraphAutomorphism_trans (valuationTwoGraph X)
    (γ.symm.trans (B.inflatedCanonicalFullTransversalLift χD p hpD)) γ
    (twoGraphAutomorphism_trans (valuationTwoGraph X)
      γ.symm (B.inflatedCanonicalFullTransversalLift χD p hpD)
      hγinv hL) hγ

/-- Conjugated lifts extend their prescribed permutation of every
vertex of the original marked transversal. -/
theorem BlockCoordinates.conjugatedMarkedLift_marked
    (B : BlockCoordinates D X)
    [Fintype D] [DecidableEq D] [Nonempty D]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (χ : D → Valuation X) (p : Equiv.Perm D)
    (hp : B.PreservesMarkedTransversal χ p) (d : D) :
    B.conjugatedMarkedLift χ p hp
        (B.markedEmbedding d, valuationClass (χ d)) =
      (B.markedEmbedding (p d), valuationClass (χ (p d))) := by
  let γ := B.canonicalTransversalConjugator χ
  let χD := restrictedTransversalValuations B.markedEmbedding χ
  let hpD := B.preservesRestrictedTransversal χ p hp
  have hd := B.canonicalTransversalConjugator_marked χ d
  have hpd := B.canonicalTransversalConjugator_marked χ (p d)
  have hL := B.inflatedCanonicalFullTransversalLift_marked χD p hpD d
  calc
    B.conjugatedMarkedLift χ p hp
        (B.markedEmbedding d, valuationClass (χ d)) =
      γ ((B.inflatedCanonicalFullTransversalLift χD p hpD)
        (γ.symm (B.markedEmbedding d, valuationClass (χ d)))) := by
          rfl
    _ = γ ((B.inflatedCanonicalFullTransversalLift χD p hpD)
        (B.inflateValuationVertex (d, valuationClass (χD d)))) := by
          rw [← hd, Equiv.symm_apply_apply]
    _ = γ (B.inflateValuationVertex
        (p d, valuationClass (χD (p d)))) := congrArg γ hL
    _ = (B.markedEmbedding (p d), valuationClass (χ (p d))) := hpd

/-- Conjugated lifts preserve the identity. -/
theorem BlockCoordinates.conjugatedMarkedLift_refl
    (B : BlockCoordinates D X)
    [Fintype D] [DecidableEq D] [Nonempty D]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (χ : D → Valuation X) :
    B.conjugatedMarkedLift χ (Equiv.refl D)
      (B.preservesMarkedTransversal_refl χ) =
        Equiv.refl (ValuationVertex X) := by
  let γ := B.canonicalTransversalConjugator χ
  let χD := restrictedTransversalValuations B.markedEmbedding χ
  apply Equiv.ext
  intro v
  change γ ((B.inflatedCanonicalFullTransversalLift χD (Equiv.refl D) _)
    (γ.symm v)) = v
  rw [B.inflatedCanonicalFullTransversalLift_identity χD]
  simp

/-- **Simultaneous subgroup section:** conjugated lifts of every two
original transversal automorphisms respect composition exactly. -/
theorem BlockCoordinates.conjugatedMarkedLift_trans
    (B : BlockCoordinates D X)
    [Fintype D] [DecidableEq D] [Nonempty D]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (χ : D → Valuation X)
    (p q : Equiv.Perm D)
    (hp : B.PreservesMarkedTransversal χ p)
    (hq : B.PreservesMarkedTransversal χ q) :
    (B.conjugatedMarkedLift χ p hp).trans
      (B.conjugatedMarkedLift χ q hq) =
    B.conjugatedMarkedLift χ (p.trans q)
      (B.preservesMarkedTransversal_trans χ p q hp hq) := by
  let γ := B.canonicalTransversalConjugator χ
  let χD := restrictedTransversalValuations B.markedEmbedding χ
  let hpD := B.preservesRestrictedTransversal χ p hp
  let hqD := B.preservesRestrictedTransversal χ q hq
  have hcomp := B.inflatedCanonicalFullTransversalLift_trans
    χD p q hpD hqD
  apply Equiv.ext
  intro v
  change γ ((B.inflatedCanonicalFullTransversalLift χD q hqD)
      (γ.symm (γ ((B.inflatedCanonicalFullTransversalLift χD p hpD)
        (γ.symm v))))) =
    γ ((B.inflatedCanonicalFullTransversalLift χD (p.trans q) _)
      (γ.symm v))
  rw [Equiv.symm_apply_apply]
  exact congrArg γ (congrArg
    (fun f : Equiv.Perm (ValuationVertex X) => f (γ.symm v)) hcomp)

end EPPAReducts.TwoGraphs
