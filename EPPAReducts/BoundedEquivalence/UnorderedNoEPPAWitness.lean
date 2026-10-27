import EPPAReducts.BoundedEquivalence.UnorderedCyclicPartials
import EPPAReducts.BoundedEquivalence.UnorderedNoSimultaneousExtensions
import EPPAReducts.BoundedEquivalence.UnorderedGraphTargetBridge
import EPPAReducts.BoundedEquivalence.UnorderedColourNormalization

/-!
# Ordinary EPPA fails for bounded-class equivalences on unordered r-subsets

This file combines the explicit finite cyclic obstruction and genuine
literal partial automorphisms with the finite normalizer-coset
contradiction. No auxiliary colour is named in the structure. The
final theorem, if certified by a full Lean build and axiom audit,
proves the exact frozen HumanTargets graph-modulo-complementation
failure statement as the r=m=2 specialization.
-/

namespace EPPAReducts.BoundedEquivalence

open EPPAReducts.HumanTargets

/-- The explicit finite unlabelled cyclic (b+1)-subset equivalence
has no finite ordinary EPPA witness, for all m≥2 and b≥1. -/
theorem unorderedCyclicObstruction_noEPPAWitness_succ
    (m b : ℕ) (hm : 2 ≤ m) (hb : 1 ≤ b)
    (W : Type) [Fintype W] [DecidableEq W]
    (B : UnorderedBoundedEquivalence W (b + 1) m)
    (ι : Sum (ZMod (unorderedCommonCoreSize m (b + 1)))
      (Fin (b + 1)) ↪ W) :
    ¬ IsUnorderedBoundedEPPAWitness
      (unorderedCyclicObstruction m b hm hb) B ι := by
  classical
  have hmpos : 0 < m := by omega
  have hN : 0 < unorderedCommonCoreSize m (b + 1) :=
    unorderedCommonCoreSize_pos m (b + 1) hm (by omega)
  letI : NeZero (unorderedCommonCoreSize m (b + 1)) :=
    ⟨Nat.ne_of_gt hN⟩
  let fA : RSubsets
      (Sum (ZMod (unorderedCommonCoreSize m (b + 1))) (Fin (b + 1)))
      (b + 1) → ZMod m :=
    unorderedCyclicObstructionColour m b
  have hkernel : ∀ q s : RSubsets
        (Sum (ZMod (unorderedCommonCoreSize m (b + 1))) (Fin (b + 1)))
        (b + 1),
      (unorderedCyclicObstruction m b hm hb).sameClass.r q s ↔
        fA q = fA s := by
    intro q s
    change fA q = fA s ↔ fA q = fA s
    exact Iff.rfl
  have hsurjA : Function.Surjective fA := by
    intro c
    obtain ⟨q, hq⟩ :=
      unorderedCyclicObstruction_core_surjective m b hm hb c
    exact ⟨mapRSubset
      (unorderedCoreInclusion (E := Fin (b + 1))) q, hq⟩
  intro hWitness
  obtain ⟨fB, hB⟩ :=
    exists_unordered_extension_colours hmpos
      (unorderedCyclicObstruction m b hm hb)
      B ι fA hkernel hsurjA hWitness.1
  let hp (i : Fin (b + 1)) :=
    unorderedCyclicObstruction_partialAut m b hm hb i
  let existence (i : Fin (b + 1)) :=
    hWitness.2 (orderedCoreOnePartialShift i) (hp i)
  let g (i : Fin (b + 1)) : Equiv.Perm W :=
    Classical.choose (existence i)
  have hgAut (i : Fin (b + 1)) :
      IsUnorderedBoundedAutomorphism B (g i) :=
    (Classical.choose_spec (existence i)).1
  have hgExt (i : Fin (b + 1)) :
      Extends ι (orderedCoreOnePartialShift i) (g i) :=
    (Classical.choose_spec (existence i)).2
  have hg (i : Fin (b + 1)) :
      g i ∈ unorderedSubsetKernelAutSubgroup fB :=
    (unorderedBoundedAutomorphism_iff_kernelAut
      B fB hB.2 (g i)).mp (hgAut i)
  have hgcore (i : Fin (b + 1))
      (s : ZMod (unorderedCommonCoreSize m (b + 1))) :
      g i (ι (Sum.inl s)) = ι (Sum.inl (s + 1)) := by
    let v : {v : Sum (ZMod (unorderedCommonCoreSize m (b + 1)))
        (Fin (b + 1)) // v ∈ orderedCoreOne i} :=
      ⟨Sum.inl s, mem_orderedCoreOne_inl i s⟩
    calc
      g i (ι (Sum.inl s)) =
          ι (((orderedCoreOnePartialShift i).bijection v).val) :=
        hgExt i (Sum.inl s) (mem_orderedCoreOne_inl i s)
      _ = ι (orderedCoreShift (Sum.inl s)) :=
        congrArg ι (orderedCoreOnePartialShift_apply i v)
      _ = ι (Sum.inl (s + 1)) := rfl
  have hfix (i : Fin (b + 1)) :
      g i (ι (Sum.inr i)) = ι (Sum.inr i) := by
    have hmem :
        (Sum.inr i : Sum
          (ZMod (unorderedCommonCoreSize m (b + 1))) (Fin (b + 1))) ∈
            (orderedCoreOnePartialShift i).source :=
      (mem_orderedCoreOne_inr i i).mpr rfl
    let v : {v : Sum (ZMod (unorderedCommonCoreSize m (b + 1)))
        (Fin (b + 1)) // v ∈ orderedCoreOne i} :=
      ⟨Sum.inr i, hmem⟩
    calc
      g i (ι (Sum.inr i)) =
          ι (((orderedCoreOnePartialShift i).bijection v).val) :=
        hgExt i (Sum.inr i) hmem
      _ = ι (orderedCoreShift (Sum.inr i)) :=
        congrArg ι (orderedCoreOnePartialShift_apply i v)
      _ = ι (Sum.inr i) := rfl
  have hOld (q : RSubsets
        (Sum (ZMod (unorderedCommonCoreSize m (b + 1))) (Fin (b + 1)))
        (b + 1)) :
      fB (mapRSubset ι q) =
        unorderedCyclicObstructionColour m b q :=
    hB.1 q
  exact unorderedCyclicCore_exterior_extensions_impossible
    m b hm hb ι fB hOld g hg hgcore hfix

/-- For EVERY r,m≥2, the finite class of unlabelled equivalence
relations on unordered r-subsets with at most m classes fails
ordinary EPPA. This matches the fixed global proposition exactly. -/
theorem allUnorderedBoundedEquivalencesFailEPPA :
    unorderedBoundedEquivalencesFailEPPA := by
  intro r m hr hm
  cases r with
  | zero => omega
  | succ b =>
      have hb : 1 ≤ b := by omega
      refine ⟨Sum
        (ZMod (unorderedCommonCoreSize m (b + 1))) (Fin (b + 1)),
        unorderedCyclicObstruction_carrierFinite m b hm hb,
        unorderedCyclicObstruction m b hm hb, ?_⟩
      intro W hfin B ι
      classical
      letI : Finite W := hfin
      letI : Fintype W := Fintype.ofFinite W
      exact unorderedCyclicObstruction_noEPPAWitness_succ
        m b hm hb W B ι

/-- The author's exact frozen negative theorem is a specialization
at r=m=2, preserving its original unlabelled pair semantics. -/
theorem humanGraphsModuloComplementationFailEPPA :
    HumanTargets.graphsModuloComplementationFailEPPA :=
  graphsModuloComplementationFailEPPA_of_unordered
    allUnorderedBoundedEquivalencesFailEPPA

end EPPAReducts.BoundedEquivalence
