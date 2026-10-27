import EPPAReducts.BoundedEquivalence.UnorderedWitnessAPI
import EPPAReducts.BoundedEquivalence.OrderedColourTranslationFixed
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel

/-!
# A constructive alternative to choosing cyclic-subset orbit representatives

When the modulus is m*t, translation by t increments the quotient
of the canonical residue by t, modulo m. This arithmetic lemma is
a first step toward an explicit equivariant colouring of unordered
t-subsets via their sum, avoiding abstract orbit selectors.
-/

namespace EPPAReducts.BoundedEquivalence

/-- The quotient of a canonical residue by t is a ZMod m colour.
Translation by t shifts that colour by exactly one. -/
theorem zmod_quotient_colour_shift
    (m t : ℕ) (hm : 2 ≤ m) (ht : 0 < t)
    (z : ZMod (m * t)) :
    ((z + (t : ZMod (m * t))).val / t : ZMod m) =
      (z.val / t : ZMod m) + 1 := by
  have hmpos : 0 < m := by omega
  letI : NeZero (m * t) := ⟨Nat.ne_of_gt (Nat.mul_pos hmpos ht)⟩
  have hlt : t < m * t := by
    simpa only [one_mul] using
      (Nat.mul_lt_mul_of_pos_right (by omega : 1 < m) ht)
  have hcast : (t : ZMod (m * t)).val = t :=
    ZMod.val_natCast_of_lt hlt
  have hmod :
      ((z.val + t) % (m * t)) / t =
        ((z.val + t) / t) % m := by
    simpa only [Nat.mul_comm m t] using
      (Nat.mod_mul_right_div_self (z.val + t) t m)
  calc
    ((z + (t : ZMod (m * t))).val / t : ZMod m) =
        (((z.val + t) % (m * t)) / t : ZMod m) := by
      rw [ZMod.val_add, hcast]
    _ = (((z.val + t) / t) % m : ZMod m) := by rw [hmod]
    _ = ((z.val / t + 1) % m : ZMod m) := by
      rw [Nat.add_div_right _ ht]
    _ = (z.val / t : ZMod m) + 1 := by simp

/-- The sum of the elements of an unordered subset, computed in
the ambient cyclic additive group. -/
def unorderedSubsetSum {N t : ℕ} (s : RSubsets (ZMod N) t) : ZMod N :=
  s.val.sum id

/-- A unit translation of every vertex adds precisely the
cardinality of the subset to its cyclic sum. -/
theorem unorderedSubsetSum_translate_one
    (N t : ℕ) (s : RSubsets (ZMod N) t) :
    unorderedSubsetSum
        (permuteRSubset (orderedColourTranslationPerm (1 : ZMod N)) s) =
      unorderedSubsetSum s + (t : ZMod N) := by
  simp [unorderedSubsetSum, permuteRSubset,
    orderedColourTranslationPerm, Finset.sum_map,
    Finset.sum_add_distrib, s.property]


/-- If m*t divides N, cyclic subset sums give an explicit ZMod m
colouring. The projection to ZMod (m*t) is a ring homomorphism;
no orbit representatives or quotient choices are used. -/
def unorderedCyclicSumColour
    {N m t : ℕ} (hdiv : m * t ∣ N)
    (s : RSubsets (ZMod N) t) : ZMod m :=
  (((ZMod.castHom hdiv (ZMod (m * t))) (unorderedSubsetSum s)).val / t :
    ZMod m)

/-- Every unit translation of a t-subset adds one to the cyclic
sum colouring, whenever m*t divides the ambient cyclic order. -/
theorem unorderedCyclicSumColour_translate_one
    (N m t : ℕ) (hm : 2 ≤ m) (ht : 0 < t)
    (hdiv : m * t ∣ N) (s : RSubsets (ZMod N) t) :
    unorderedCyclicSumColour hdiv
        (permuteRSubset (orderedColourTranslationPerm (1 : ZMod N)) s) =
      unorderedCyclicSumColour hdiv s + 1 := by
  unfold unorderedCyclicSumColour
  rw [unorderedSubsetSum_translate_one]
  have hcast :
      (ZMod.castHom hdiv (ZMod (m * t)))
        (unorderedSubsetSum s + (t : ZMod N)) =
      (ZMod.castHom hdiv (ZMod (m * t)))
        (unorderedSubsetSum s) + (t : ZMod (m * t)) := by
    change (ZMod.cast (unorderedSubsetSum s + (t : ZMod N)) : ZMod (m * t)) =
      (ZMod.cast (unorderedSubsetSum s) : ZMod (m * t)) + (t : ZMod (m * t))
    rw [ZMod.cast_add hdiv, ZMod.cast_natCast hdiv]
  rw [hcast]
  exact zmod_quotient_colour_shift m t hm ht _

/-- A map to a cyclic group that shifts by +1 under an endomap of a
nonempty carrier necessarily takes all m cyclic colour values.
It does not require the carrier endomap to have been factored into
translation orbits. -/
theorem zmod_colour_surjective_of_shift
    {U : Type} (m : ℕ) (hm : 0 < m)
    (u : U) (P : U → U) (f : U → ZMod m)
    (hshift : ∀ x : U, f (P x) = f x + 1) :
    Function.Surjective f := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let seq : ℕ → U := Nat.rec u (fun _ x => P x)
  have hseq (n : ℕ) : f (seq n) = f u + (n : ZMod m) := by
    induction n with
    | zero => simp [seq]
    | succ n ih =>
        calc
          f (seq (n + 1)) = f (P (seq n)) := rfl
          _ = f (seq n) + 1 := hshift _
          _ = (f u + (n : ZMod m)) + 1 := by rw [ih]
          _ = f u + ((n + 1 : ℕ) : ZMod m) := by
            push_cast
            abel
  intro c
  let n : ℕ := (c - f u).val
  refine ⟨seq n, ?_⟩
  rw [hseq n]
  change f u + (((c - f u).val : ℕ) : ZMod m) = c
  rw [ZMod.natCast_zmod_val]
  abel


/-- Every t ≤ N with N positive has a genuine unordered t-subset
of the cyclic carrier, including the empty subset for t=0. -/
theorem zmod_rSubsets_nonempty
    (N t : ℕ) (hN : 0 < N) (ht : t ≤ N) :
    Nonempty (RSubsets (ZMod N) t) := by
  classical
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hcard : t ≤ (Finset.univ : Finset (ZMod N)).card := by
    simpa only [Finset.card_univ, ZMod.card] using ht
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨⟨s, hs⟩⟩

/-- Whenever the cyclic core is big enough for a t-subset, the
explicit cyclic-sum colouring realizes ALL m auxiliary classes. -/
theorem unorderedCyclicSumColour_surjective
    (N m t : ℕ) (hN : 0 < N) (hm : 2 ≤ m)
    (ht : 0 < t) (htN : t ≤ N) (hdiv : m * t ∣ N) :
    Function.Surjective (unorderedCyclicSumColour hdiv) := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  obtain ⟨u⟩ := zmod_rSubsets_nonempty N t hN htN
  exact zmod_colour_surjective_of_shift m (by omega)
    u (fun s => permuteRSubset
      (orderedColourTranslationPerm (1 : ZMod N)) s)
    (unorderedCyclicSumColour hdiv)
    (unorderedCyclicSumColour_translate_one N m t hm ht hdiv)

/-- A common cyclic core large enough for the two subset sizes
r and r-1 and divisible by m times BOTH of those lengths. -/
def unorderedCommonCoreSize (m r : ℕ) : ℕ :=
  m * r * (r - 1)

theorem unorderedCommonCoreSize_pos
    (m r : ℕ) (hm : 2 ≤ m) (hr : 2 ≤ r) :
    0 < unorderedCommonCoreSize m r := by
  unfold unorderedCommonCoreSize
  exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)

theorem unorderedCommonCoreSize_ge
    (m r : ℕ) (hm : 2 ≤ m) (hr : 2 ≤ r) :
    r ≤ unorderedCommonCoreSize m r := by
  have h1 : 1 ≤ m := by omega
  have h2 : 1 ≤ r - 1 := by omega
  calc
    r = 1 * r * 1 := by omega
    _ ≤ m * r * (r - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right r h1) h2

theorem unorderedCommonCoreSize_dvd_r
    (m r : ℕ) :
    m * r ∣ unorderedCommonCoreSize m r :=
  ⟨r - 1, rfl⟩

theorem unorderedCommonCoreSize_dvd_pred
    (m r : ℕ) :
    m * (r - 1) ∣ unorderedCommonCoreSize m r := by
  refine ⟨r, ?_⟩
  simp [unorderedCommonCoreSize, mul_comm, mul_left_comm, mul_assoc]

/-- The same cyclic core supports surjective +1-equivariant
unordered subset colourings at BOTH arities needed for the
finite non-EPPA obstruction. -/
theorem unorderedCommonCore_two_surjective_colours
    (m r : ℕ) (hm : 2 ≤ m) (hr : 2 ≤ r) :
    Function.Surjective
      (unorderedCyclicSumColour (unorderedCommonCoreSize_dvd_r m r)) ∧
    Function.Surjective
      (unorderedCyclicSumColour (unorderedCommonCoreSize_dvd_pred m r)) := by
  have hN := unorderedCommonCoreSize_pos m r hm hr
  have hrN := unorderedCommonCoreSize_ge m r hm hr
  constructor
  · exact unorderedCyclicSumColour_surjective
      (unorderedCommonCoreSize m r) m r
      hN hm (by omega) hrN (unorderedCommonCoreSize_dvd_r m r)
  · exact unorderedCyclicSumColour_surjective
      (unorderedCommonCoreSize m r) m (r - 1)
      hN hm (by omega) (by omega) (unorderedCommonCoreSize_dvd_pred m r)

end EPPAReducts.BoundedEquivalence
