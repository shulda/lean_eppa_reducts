import EPPAReducts.TwoGraphs.BlockCoordinates
import Mathlib.Logic.Equiv.Fintype

/-!
# Producing marked block coordinates from finite cardinal divisibility

For a finite marked injection ι : D ↪ X with D nonempty, the
divisibility |D| ∣ |X| yields a partition of X into equally sized
copies of D, including a distinguished copy whose embedding is
**exactly** ι. The associated blockwise permutation action is
therefore homomorphic and fixes the marked copy as required.

The construction first chooses an arbitrary product bijection,
then adjusts it by a permutation of X extending the prescribed
bijection of the distinguished block. This avoids a noncanonical
choice of blocks depending on the permutation of D.
-/

namespace EPPAReducts.TwoGraphs

/-- Equal cardinality |X|=|D|*k and k>0 provide a marked product
decomposition whose distinguished block is any prescribed injection
ι : D ↪ X. -/
theorem exists_markedBlockCoordinates_of_card_eq
    {D X : Type} [Fintype D] [Fintype X]
    (ι : D ↪ X) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card X = Fintype.card D * k) :
    ∃ B : BlockCoordinates D X, ∀ d, B.markedEmbedding d = ι d := by
  classical
  have hc : Fintype.card (D × Fin k) = Fintype.card X := by
    simpa [Fintype.card_prod] using hcard.symm
  let e : D × Fin k ≃ X := Fintype.equivOfCardEq hc
  let i₀ : Fin k := ⟨0, hk⟩
  have hinj : Function.Injective (fun d : D => e (d, i₀)) := by
    intro d d' h
    exact congrArg Prod.fst (e.injective h)
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair
    (fun d : D => e (d, i₀)) (fun d : D => ι d) hinj ι.injective
  let B : BlockCoordinates D X :=
    { Index := Fin k
      distinguished := i₀
      equiv := e.trans π }
  refine ⟨B, ?_⟩
  intro d
  change π (e (d, i₀)) = ι d
  exact hπ d

/-- The exact finite combinatorial block-inflation hypothesis:
a nonempty marked subset D of X whose size divides |X| can be made
the distinguished block of an equivariant product decomposition. -/
theorem exists_markedBlockCoordinates_of_dvd
    {D X : Type} [Fintype D] [Fintype X] [Nonempty D]
    (ι : D ↪ X)
    (hdiv : Fintype.card D ∣ Fintype.card X) :
    ∃ B : BlockCoordinates D X, ∀ d, B.markedEmbedding d = ι d := by
  classical
  obtain ⟨k, hk⟩ := hdiv
  haveI : Nonempty X := ⟨ι (Classical.choice ‹Nonempty D›)⟩
  have hkpos : 0 < k := by
    have hne : k ≠ 0 := by
      intro hkzero
      have hzero : Fintype.card X = 0 := by
        simpa [hkzero] using hk
      exact Fintype.card_ne_zero hzero
    exact Nat.pos_of_ne_zero hne
  exact exists_markedBlockCoordinates_of_card_eq ι k hkpos hk

/-- Concrete output of the divisibility lemma: an equivariant
retraction from X onto D and a composition-preserving permutation
lift, extending the marked inclusion. These are the exact hypotheses
needed by the subsequent valuation and matrix inflation proofs. -/
theorem exists_blockwise_permutation_lift
    {D X : Type} [Fintype D] [Fintype X] [Nonempty D]
    (ι : D ↪ X) (hdiv : Fintype.card D ∣ Fintype.card X) :
    ∃ (r : X → D) (lift : Equiv.Perm D → Equiv.Perm X),
      (∀ d, r (ι d) = d) ∧
      (∀ (p : Equiv.Perm D) (d : D), lift p (ι d) = ι (p d)) ∧
      (∀ (p : Equiv.Perm D) (x : X), r (lift p x) = p (r x)) ∧
      (∀ p q, (lift p).trans (lift q) = lift (p.trans q)) ∧
      lift (Equiv.refl D) = Equiv.refl X := by
  obtain ⟨B, hB⟩ := exists_markedBlockCoordinates_of_dvd ι hdiv
  refine ⟨B.projection, B.liftPerm, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    rw [← hB d]
    exact B.projection_marked d
  · intro p d
    rw [← hB d, ← hB (p d)]
    exact B.liftPerm_marked p d
  · intro p x
    exact B.projection_liftPerm p x
  · intro p q
    exact B.liftPerm_trans p q
  · exact B.liftPerm_refl

end EPPAReducts.TwoGraphs
