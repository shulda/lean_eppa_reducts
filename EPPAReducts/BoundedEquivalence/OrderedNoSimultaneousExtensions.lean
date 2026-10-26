import EPPAReducts.BoundedEquivalence.OrderedCoreCosetCollision
import EPPAReducts.BoundedEquivalence.OrderedExteriorLabels
import EPPAReducts.BoundedEquivalence.OrderedOldCoreShift

/-!
# The ordered cyclic obstruction: no simultaneous extensions

This is the last coset-versus-exterior-type contradiction. It is
formulated for an arbitrary finite ambient carrier and any auxiliary
labelling of its *unlabelled* tuple-equivalence relation that agrees
with the explicit old cyclic colouring. A later bridge obtains that
labelling from a hypothetical ordinary EPPA witness.
-/

namespace EPPAReducts.BoundedEquivalence

/-- A normalized auxiliary colouring on any finite extension of the
explicit ordered cyclic obstruction cannot support r automorphisms
which all shift the old core by one and individually fix the r
distinct exterior vertices. Neither the structure nor its
automorphisms have named colour relations. -/
theorem orderedCyclicCore_exterior_extensions_impossible
    (m b : ℕ) (hm : 2 ≤ m) (hb : 2 ≤ b + 1)
    {W : Type} [Fintype W] [DecidableEq W]
    (ι : Sum (ZMod (m * (b + 1))) (Fin (b + 1)) ↪ W)
    (fB : InjectiveTuples W (b + 1) → ZMod m)
    (hext : ∀ t : InjectiveTuples
        (Sum (ZMod (m * (b + 1))) (Fin (b + 1))) (b + 1),
      fB (mapInjectiveTuple ι t) =
        orderedCoreExteriorColour m (m * (b + 1)) (b + 1)
          (show m ∣ m * (b + 1) from ⟨b + 1, rfl⟩)
          (by omega : 1 < b + 1) t.val)
    (g : Fin (b + 1) → Equiv.Perm W)
    (hg : ∀ i, g i ∈ orderedTupleKernelAutSubgroup fB)
    (hgcore : ∀ (i : Fin (b + 1)) (s : ZMod (m * (b + 1))),
      g i (ι (Sum.inl s)) = ι (Sum.inl (s + 1)))
    (hfix : ∀ (i : Fin (b + 1)),
      g i (ι (Sum.inr i)) = ι (Sum.inr i)) :
    False := by
  classical
  have hmpos : 0 < m := by omega
  have hrone : 1 < b + 1 := by omega
  have hrpos : 0 < b + 1 := Nat.zero_lt_succ b
  letI : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  letI : NeZero (m * (b + 1)) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos hmpos hrpos)⟩
  let hmN : m ∣ m * (b + 1) := ⟨b + 1, rfl⟩
  let coreIn : ZMod (m * (b + 1)) ↪
      Sum (ZMod (m * (b + 1))) (Fin (b + 1)) :=
    ⟨Sum.inl, Sum.inl_injective⟩
  have hcoreMap
      (t : InjectiveTuples (ZMod (m * (b + 1))) (b + 1)) :
      mapInjectiveTuple (orderedEmbeddedCore ι) t =
        mapInjectiveTuple ι (mapInjectiveTuple coreIn t) := by
    apply Subtype.ext
    funext j
    rfl
  have hcoreColour
      (t : InjectiveTuples (ZMod (m * (b + 1))) (b + 1)) :
      fB (mapInjectiveTuple (orderedEmbeddedCore ι) t) =
        orderedCoreExteriorColour m (m * (b + 1)) (b + 1)
          hmN hrone (fun j => Sum.inl (t.val j)) := by
    rw [hcoreMap t]
    exact hext (mapInjectiveTuple coreIn t)
  have hsurjCore : Function.Surjective
      (fun t : InjectiveTuples (ZMod (m * (b + 1))) (b + 1) =>
        fB (mapInjectiveTuple (orderedEmbeddedCore ι) t)) := by
    intro c
    obtain ⟨t, ht⟩ :=
      orderedCyclicCoreExteriorColour_surjective
        m (b + 1) hmpos hrone c
    exact ⟨t, (hcoreColour t).trans ht⟩
  have hshiftCore
      (t : InjectiveTuples (ZMod (m * (b + 1))) (b + 1)) :
      fB (mapInjectiveTuple (orderedEmbeddedCore ι)
        (permuteOrderedTuple (orderedUnitCorePerm (m * (b + 1))) t)) =
        fB (mapInjectiveTuple (orderedEmbeddedCore ι) t) +
          (1 : ZMod m) := by
    calc
      fB (mapInjectiveTuple (orderedEmbeddedCore ι)
          (permuteOrderedTuple (orderedUnitCorePerm (m * (b + 1))) t)) =
        orderedCoreExteriorColour m (m * (b + 1)) (b + 1)
          hmN hrone
          (fun j => Sum.inl ((orderedUnitCorePerm (m * (b + 1))) (t.val j))) :=
        hcoreColour _
      _ = orderedCoreExteriorColour m (m * (b + 1)) (b + 1)
          hmN hrone (fun j => Sum.inl (t.val j)) + 1 :=
        orderedCoreExteriorColour_on_core_shift
          m (m * (b + 1)) (b + 1) hmN hrone t
      _ = fB (mapInjectiveTuple (orderedEmbeddedCore ι) t) + 1 := by
        rw [hcoreColour t]
  have hOne : (1 : ZMod m) ≠ 0 := by
    intro h
    have hm1 : m = 1 := ZMod.one_eq_zero_iff.mp h
    omega
  have hcore (i : Fin (b + 1)) (s : ZMod (m * (b + 1))) :
      g i ((orderedEmbeddedCore ι) s) =
        (orderedEmbeddedCore ι) ((orderedUnitCorePerm (m * (b + 1))) s) := by
    simpa [orderedEmbeddedCore, orderedUnitCorePerm,
      orderedColourTranslationPerm] using hgcore i s
  let a : Fin (b + 1) ↪ W :=
    ⟨fun i => ι (Sum.inr i), by
      intro i j h
      exact Sum.inr_injective (ι.injective h)⟩
  have ha (i : Fin (b + 1)) : g i (a i) = a i := hfix i
  obtain ⟨i, j, hij, ⟨l, hl⟩⟩ :=
    orderedKernel_core_extension_orbit_collision b fB
      (orderedEmbeddedCore ι) (orderedUnitCorePerm (m * (b + 1)))
      (1 : ZMod m) hOne hsurjCore hshiftCore a g hg hcore ha
  obtain ⟨core⟩ := cyclicCoreInjectiveTuple_nonempty
    m (b + 1) (b + 1) hmpos hrpos (le_refl _)
  exact (orderedExterior_not_coreFixer_related
    m (m * (b + 1)) (b + 1) hmN hm hrone ι
    fB hext hsurjCore core i j hij l) hl

end EPPAReducts.BoundedEquivalence
