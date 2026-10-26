import EPPAReducts.BoundedEquivalence.OrderedNoSimultaneousExtensions
import EPPAReducts.BoundedEquivalence.OrderedWitnessAPI

/-!
# The ordered bounded-equivalence class fails ordinary EPPA

The explicit finite cyclic obstruction has r genuine partial
automorphisms. Every hypothetical finite unlabelled EPPA witness
would provide r full extensions; normalization by all the realized
old class labels contradicts the core/exterior coset theorem.
-/

namespace EPPAReducts.BoundedEquivalence

open EPPAReducts.HumanTargets

/-- The explicit ordered cyclic structure with r=b+1 exterior
vertices has no finite ordinary EPPA witness whenever r,m >= 2. -/
theorem orderedCyclicObstruction_noEPPAWitness_succ
    (m b : ℕ) (hm : 2 ≤ m) (hb : 2 ≤ b + 1)
    (W : Type) [Fintype W] [DecidableEq W]
    (B : OrderedBoundedEquivalence W (b + 1) m)
    (ι : Sum (ZMod (m * (b + 1))) (Fin (b + 1)) ↪ W) :
    ¬ IsOrderedBoundedEPPAWitness
        (orderedCyclicObstruction m (b + 1) hm hb) B ι := by
  classical
  have hmpos : 0 < m := by omega
  have hrone : 1 < b + 1 := by omega
  letI : NeZero (m * (b + 1)) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos hmpos (Nat.zero_lt_succ b))⟩
  let hmN : m ∣ m * (b + 1) := ⟨b + 1, rfl⟩
  let fA : InjectiveTuples
      (Sum (ZMod (m * (b + 1))) (Fin (b + 1))) (b + 1) → ZMod m :=
    fun t => orderedCoreExteriorColour
      m (m * (b + 1)) (b + 1) hmN hrone t.val
  let coreIn : ZMod (m * (b + 1)) ↪
      Sum (ZMod (m * (b + 1))) (Fin (b + 1)) :=
    ⟨Sum.inl, Sum.inl_injective⟩
  have hkernel : ∀ t u : InjectiveTuples
        (Sum (ZMod (m * (b + 1))) (Fin (b + 1))) (b + 1),
      (orderedCyclicObstruction m (b + 1) hm hb).sameClass.r t u ↔
        fA t = fA u := by
    intro t u
    change fA t = fA u ↔ fA t = fA u
    exact Iff.rfl
  have hsurjA : Function.Surjective fA := by
    intro c
    obtain ⟨t, ht⟩ :=
      orderedCyclicCoreExteriorColour_surjective
        m (b + 1) hmpos hrone c
    refine ⟨mapInjectiveTuple coreIn t, ?_⟩
    exact ht
  intro hWitness
  obtain ⟨fB, hB⟩ :=
    exists_ordered_extension_colours hmpos
      (orderedCyclicObstruction m (b + 1) hm hb)
      B ι fA hkernel hsurjA hWitness.1
  let hp (i : Fin (b + 1)) :=
    orderedCyclicObstruction_partialAut m (b + 1) hm hb i
  let existence (i : Fin (b + 1)) :=
    hWitness.2 (orderedCoreOnePartialShift i) (hp i)
  let g (i : Fin (b + 1)) : Equiv.Perm W :=
    Classical.choose (existence i)
  have hgAut (i : Fin (b + 1)) :
      IsOrderedBoundedAutomorphism B (g i) :=
    (Classical.choose_spec (existence i)).1
  have hgExt (i : Fin (b + 1)) :
      Extends ι (orderedCoreOnePartialShift i) (g i) :=
    (Classical.choose_spec (existence i)).2
  have hg (i : Fin (b + 1)) :
      g i ∈ orderedTupleKernelAutSubgroup fB :=
    (orderedBoundedAutomorphism_iff_kernelAut B fB hB.2 (g i)).mp
      (hgAut i)
  have hgcore (i : Fin (b + 1)) (s : ZMod (m * (b + 1))) :
      g i (ι (Sum.inl s)) = ι (Sum.inl (s + 1)) := by
    have h := hgExt i (Sum.inl s) (mem_orderedCoreOne_inl i s)
    simpa [orderedCoreOnePartialShift_apply, orderedCoreShift] using h
  have hfix (i : Fin (b + 1)) :
      g i (ι (Sum.inr i)) = ι (Sum.inr i) := by
    have hmem :
        (Sum.inr i : Sum (ZMod (m * (b + 1))) (Fin (b + 1))) ∈
          (orderedCoreOnePartialShift i).source :=
      (mem_orderedCoreOne_inr i i).mpr rfl
    have h := hgExt i (Sum.inr i) hmem
    simpa [orderedCoreOnePartialShift_apply, orderedCoreShift] using h
  have hext (t : InjectiveTuples
        (Sum (ZMod (m * (b + 1))) (Fin (b + 1))) (b + 1)) :
      fB (mapInjectiveTuple ι t) =
        orderedCoreExteriorColour m (m * (b + 1)) (b + 1)
          hmN hrone t.val := by
    exact hB.1 t
  exact orderedCyclicCore_exterior_extensions_impossible
    m b hm hb ι fB hext g hg hgcore hfix

/-- Every class of unlabelled equivalence relations on injective
ordered r-tuples having at most m classes fails EPPA, for r,m>=2:
one finite structure defeats all finite common extension witnesses. -/
theorem orderedBoundedEquivalencesFailEPPA
    (m r : ℕ) (hm : 2 ≤ m) (hr : 2 ≤ r) :
    ∃ (V : Type), Finite V ∧
      ∃ (A : OrderedBoundedEquivalence V r m),
        ∀ (W : Type), Finite W →
          ∀ (B : OrderedBoundedEquivalence W r m)
            (ι : V ↪ W),
              ¬ IsOrderedBoundedEPPAWitness A B ι := by
  refine ⟨Sum (ZMod (m * r)) (Fin r),
    orderedCyclicObstruction_carrierFinite m r hm hr,
    orderedCyclicObstruction m r hm hr, ?_⟩
  intro W hfin B ι
  classical
  letI : Finite W := hfin
  letI : Fintype W := Fintype.ofFinite W
  cases r with
  | zero => omega
  | succ b =>
      exact orderedCyclicObstruction_noEPPAWitness_succ
        m b hm hr W B ι

end EPPAReducts.BoundedEquivalence
