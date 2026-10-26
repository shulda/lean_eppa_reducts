import EPPAReducts.TwoGraphs.FullTransversalUniqueness

/-!
# A unique combined-action extension of a full transversal automorphism

Take one (raw) valuation χ(x) above each x. Every index permutation
preserving the induced triple parity on this full transversal has a
unique extension **within the combined index/matrix action group**.

Existence follows from the now-proved technical EPPA lifting theorem.
Uniqueness follows from the full-transversal action-determination
theorem, not from arbitrary automorphisms of the ambient two-graph.

A homomorphic choice of these unique lifts is the next milestone.
-/

namespace EPPAReducts.TwoGraphs

variable {X : Type}

/-- A permutation of the indices is an automorphism of the full
transversal with the chosen valuations. -/
def PreservesFullTransversal
    (χ : X → Valuation X) (p : Equiv.Perm X) : Prop :=
  ∀ x y z,
    rawTripleParity x y z (χ x) (χ y) (χ z) =
      rawTripleParity (p x) (p y) (p z)
        (χ (p x)) (χ (p y)) (χ (p z))

/-- The identity index permutation preserves any full transversal. -/
theorem preservesFullTransversal_refl (χ : X → Valuation X) :
    PreservesFullTransversal χ (Equiv.refl X) := by
  intro x y z
  rfl

/-- The full-transversal preservation property is closed under
composition of index permutations. -/
theorem preservesFullTransversal_trans
    (χ : X → Valuation X)
    (p q : Equiv.Perm X)
    (hp : PreservesFullTransversal χ p)
    (hq : PreservesFullTransversal χ q) :
    PreservesFullTransversal χ (p.trans q) := by
  intro x y z
  exact (hp x y z).trans (hq (p x) (p y) (p z))

/-- Any full-transversal automorphism has a combined matrix/index
extension. Only finiteness of X and nonemptiness of its transversal
are needed; the matrix entries are genuinely symmetric. -/
theorem exists_fullTransversal_matrixLift
    [Fintype X] [DecidableEq X] [Nonempty X]
    (χ : X → Valuation X)
    (p : Equiv.Perm X)
    (hp : PreservesFullTransversal χ p) :
    ∃ F : X → X → Bool,
      IsSymmetricBoolMatrix F ∧
      ∀ x,
        matrixIndexPerm p F (x, valuationClass (χ x)) =
          (p x, valuationClass (χ (p x))) := by
  classical
  let s : Finset X := Finset.univ
  have hs : s.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨x, Finset.mem_univ x⟩
  let χs : {x : X // x ∈ s} → Valuation X := fun x => χ x.val
  let ηs : {x : X // x ∈ s} → Valuation X :=
    fun x => χ (p x.val)
  have hpres : ∀ a b c : {x : X // x ∈ s},
      rawTripleParity a.val b.val c.val (χs a) (χs b) (χs c) =
        rawTripleParity (p a.val) (p b.val) (p c.val)
          (ηs a) (ηs b) (ηs c) := by
    intro a b c
    exact hp a.val b.val c.val
  obtain ⟨F, hF, hmaps⟩ :=
    exists_matrixIndexPerm_extending_raw_transversal
      s hs p χs ηs hpres
  refine ⟨F, hF, ?_⟩
  intro x
  have hx := hmaps ⟨x, Finset.mem_univ x⟩
  change matrixIndexPerm p F (x, valuationClass (χ x)) =
    (p x, valuationClass (χ (p x))) at hx
  exact hx

/-- Each full-transversal automorphism has exactly one combined
index/matrix **permutation** extending it, among those obtained
from symmetric Boolean matrices. The matrix representative need
not be unique; only its global-constant quotient is. -/
theorem existsUnique_fullTransversal_combinedLift
    [Fintype X] [DecidableEq X] [Nonempty X]
    (χ : X → Valuation X)
    (p : Equiv.Perm X)
    (hp : PreservesFullTransversal χ p) :
    ∃! g : Equiv.Perm (ValuationVertex X),
      (∃ F : X → X → Bool,
        IsSymmetricBoolMatrix F ∧ g = matrixIndexPerm p F) ∧
      ∀ x, g (x, valuationClass (χ x)) =
        (p x, valuationClass (χ (p x))) := by
  obtain ⟨F, hF, hmap⟩ := exists_fullTransversal_matrixLift χ p hp
  refine ⟨matrixIndexPerm p F, ⟨⟨F, hF, rfl⟩, hmap⟩, ?_⟩
  intro g hg
  obtain ⟨⟨G, hG, rfl⟩, hmapG⟩ := hg
  have heq : matrixIndexPerm p F = matrixIndexPerm p G :=
    matrixIndexPerm_eq_of_full_transversal p p F G
      (fun x => valuationClass (χ x))
      (fun x => (hmap x).trans (hmapG x).symm)
  exact heq.symm

end EPPAReducts.TwoGraphs
