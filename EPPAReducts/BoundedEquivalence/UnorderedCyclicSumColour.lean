import EPPAReducts.BoundedEquivalence.UnorderedWitnessAPI
import EPPAReducts.BoundedEquivalence.OrderedColourTranslationFixed
import Mathlib.Data.ZMod.Basic

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
    simp
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

end EPPAReducts.BoundedEquivalence
