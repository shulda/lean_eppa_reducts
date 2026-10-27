import EPPAReducts.BoundedEquivalence.UnorderedKernelAutGroup
import Mathlib.Tactic.Group

/-!
# The core pointwise fixer and its normalizer

For an unlabelled equivalence on injective unordered tuples, restrict
the vertex automorphism group to those automorphisms which fix an
embedded core pointwise. This forms a subgroup L. Every kernel
automorphism mapping the core bijectively to itself normalizes L.

This is the abstract group-theoretic structural step which the
negative EPPA argument uses before applying the certified
normalizer-coset fixed-orbit inequality.
-/

namespace EPPAReducts.BoundedEquivalence

/-- Full unlabelled kernel automorphisms fixing an embedded old core
pointwise, rather than merely fixing its numerical class labels. -/
def unorderedKernelCorePointwiseFixer
    {V S κ : Type} {r : ℕ}
    (f : RSubsets V r → κ) (ι : S ↪ V) :
    Subgroup (Equiv.Perm V) where
  carrier := {g |
    PreservesUnorderedSubsetKernel f g ∧
      ∀ s : S, g (ι s) = ι s}
  one_mem' := by
    constructor
    · exact (unorderedSubsetKernelAutSubgroup f).one_mem
    · intro s
      rfl
  mul_mem' := by
    rintro g h ⟨hg, hgfix⟩ ⟨hh, hhfix⟩
    constructor
    · exact (unorderedSubsetKernelAutSubgroup f).mul_mem hg hh
    · intro s
      simp only [Equiv.Perm.mul_apply, hhfix s, hgfix s]
  inv_mem' := by
    rintro g ⟨hg, hgfix⟩
    constructor
    · exact (unorderedSubsetKernelAutSubgroup f).inv_mem hg
    · intro s
      have h := congrArg g.symm (hgfix s)
      simpa using h.symm

/-- Membership is exactly both full relation preservation and
pointwise fixation of the embedded core. -/
theorem mem_unorderedKernelCorePointwiseFixer_iff
    {V S κ : Type} {r : ℕ}
    (f : RSubsets V r → κ) (ι : S ↪ V)
    (g : Equiv.Perm V) :
    g ∈ unorderedKernelCorePointwiseFixer f ι ↔
      PreservesUnorderedSubsetKernel f g ∧
        ∀ s : S, g (ι s) = ι s := Iff.rfl

/-- Conjugating a core-pointwise automorphism by a kernel
automorphism whose inverse preserves the core setwise produces
another core-pointwise automorphism. -/
theorem unorderedKernelCorePointwiseFixer_conjugate_mem
    {V S κ : Type} {r : ℕ}
    (f : RSubsets V r → κ) (ι : S ↪ V)
    (g : Equiv.Perm V)
    (hg : g ∈ unorderedSubsetKernelAutSubgroup f)
    (hcoreInv : ∀ s : S, ∃ t : S, g⁻¹ (ι s) = ι t)
    (l : Equiv.Perm V)
    (hl : l ∈ unorderedKernelCorePointwiseFixer f ι) :
    g * l * g⁻¹ ∈ unorderedKernelCorePointwiseFixer f ι := by
  constructor
  · exact (unorderedSubsetKernelAutSubgroup f).mul_mem
      ((unorderedSubsetKernelAutSubgroup f).mul_mem hg hl.1)
      ((unorderedSubsetKernelAutSubgroup f).inv_mem hg)
  · intro s
    obtain ⟨t, ht⟩ := hcoreInv s
    change (g * l * g⁻¹) (ι s) = ι s
    simp only [Equiv.Perm.mul_apply]
    rw [ht, hl.2 t]
    have h := congrArg g ht
    simpa using h.symm

/-- An automorphism of the unlabelled kernel which permutes the
embedded core in both directions belongs to the normalizer of its
pointwise fixer. The two setwise hypotheses are automatic when the
core is finite and g restricts to a permutation of it. -/
theorem unorderedKernelCorePointwiseFixer_normalizer
    {V S κ : Type} {r : ℕ}
    (f : RSubsets V r → κ) (ι : S ↪ V)
    (g : Equiv.Perm V)
    (hg : g ∈ unorderedSubsetKernelAutSubgroup f)
    (hcore : ∀ s : S, ∃ t : S, g (ι s) = ι t)
    (hcoreInv : ∀ s : S, ∃ t : S, g⁻¹ (ι s) = ι t) :
    g ∈ Subgroup.normalizer (unorderedKernelCorePointwiseFixer f ι) := by
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · intro hl
    exact unorderedKernelCorePointwiseFixer_conjugate_mem
      f ι g hg hcoreInv l hl
  · intro hconj
    have hback := unorderedKernelCorePointwiseFixer_conjugate_mem
      f ι g⁻¹ ((unorderedSubsetKernelAutSubgroup f).inv_mem hg)
      (by simpa only [inv_inv] using hcore)
      (g * l * g⁻¹) hconj
    have hsimp : g⁻¹ * (g * l * g⁻¹) * (g⁻¹)⁻¹ = l := by
      group
    simpa only [hsimp] using hback

end EPPAReducts.BoundedEquivalence
