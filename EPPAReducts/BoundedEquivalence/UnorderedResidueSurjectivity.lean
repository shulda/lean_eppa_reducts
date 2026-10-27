import EPPAReducts.BoundedEquivalence.UnorderedResidueExteriorTypes
import Mathlib.Data.Fintype.EquivFin

/-!
# Explicit witnesses for every cyclic subset-sum residue

For 0 < t and N >= 2t, take the t-1 consecutive residues
0,...,t-2 and add one last residue t-1+i, i in Fin t.
All these are valid t-element subsets and their total sums
take every value modulo t. No orbit representatives are chosen.
-/

namespace EPPAReducts.BoundedEquivalence

/-- The first t-1 residues, embedded without modular collisions. -/
def unorderedResidueSmallEmbedding
    (N t : ℕ) (hbound : 2 * t ≤ N) :
    Fin (t - 1) ↪ ZMod N where
  toFun i := (i.val : ZMod N)
  inj' := by
    intro i j h
    apply Fin.ext
    have hi : i.val < N := by omega
    have hj : j.val < N := by omega
    have hh := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt hi,
      ZMod.val_natCast_of_lt hj] using hh

def unorderedResidueFirstSet
    (N t : ℕ) (hbound : 2 * t ≤ N) : Finset (ZMod N) :=
  (Finset.univ : Finset (Fin (t - 1))).map
    (unorderedResidueSmallEmbedding N t hbound)

/-- The variable last vertex is outside the fixed first t-1 ones. -/
theorem unorderedResidue_last_not_mem
    (N t : ℕ) (hbound : 2 * t ≤ N) (i : Fin t) :
    ((t - 1 + i.val : ℕ) : ZMod N) ∉
      unorderedResidueFirstSet N t hbound := by
  classical
  intro h
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp h
  change (j.val : ZMod N) =
    ((t - 1 + i.val : ℕ) : ZMod N) at hj
  have hjN : j.val < N := by omega
  have hlN : t - 1 + i.val < N := by omega
  have hv := congrArg ZMod.val hj
  have hnat : j.val = t - 1 + i.val := by
    simpa only [ZMod.val_natCast_of_lt hjN,
      ZMod.val_natCast_of_lt hlN] using hv
  omega

/-- A t-subset with a variable last vertex t-1+i. -/
def unorderedResidueWitness
    (N t : ℕ) (hbound : 2 * t ≤ N)
    (i : Fin t) : RSubsets (ZMod N) t := by
  classical
  let F := unorderedResidueFirstSet N t hbound
  let last : ZMod N := (t - 1 + i.val : ℕ)
  have hnot : last ∉ F :=
    unorderedResidue_last_not_mem N t hbound i
  refine ⟨insert last F, ?_⟩
  rw [Finset.card_insert_of_not_mem hnot]
  have hc : F.card = t - 1 := by
    change ((Finset.univ : Finset (Fin (t - 1))).map
      (unorderedResidueSmallEmbedding N t hbound)).card = t - 1
    simp
  rw [hc]
  omega

/-- Its subset-sum residue consists of one fixed contribution plus
the chosen variable vertex t-1+i. -/
theorem unorderedResidueWitness_value
    (N t : ℕ) (hbound : 2 * t ≤ N)
    (hdiv : t ∣ N) (i : Fin t) :
    unorderedSubsetResidue hdiv
        (unorderedResidueWitness N t hbound i) =
      ((t - 1 + i.val : ℕ) : ZMod t) +
        (ZMod.castHom hdiv (ZMod t))
          ((unorderedResidueFirstSet N t hbound).sum id) := by
  classical
  have hnot := unorderedResidue_last_not_mem N t hbound i
  change (ZMod.cast
      ((insert ((t - 1 + i.val : ℕ) : ZMod N)
        (unorderedResidueFirstSet N t hbound)).sum id) : ZMod t) =
    ((t - 1 + i.val : ℕ) : ZMod t) +
      (ZMod.cast
        ((unorderedResidueFirstSet N t hbound).sum id) : ZMod t)
  rw [Finset.sum_insert hnot, ZMod.cast_add hdiv,
    ZMod.cast_natCast hdiv]

/-- All t residues occur, so the indicator functions in the
previous module can be used unconditionally on a sufficiently
large divisible cyclic core. -/
theorem unorderedSubsetResidue_surjective
    (N t : ℕ) (ht : 0 < t)
    (hbound : 2 * t ≤ N) (hdiv : t ∣ N) :
    Function.Surjective (unorderedSubsetResidue hdiv) := by
  letI : NeZero t := ⟨Nat.ne_of_gt ht⟩
  let C : ZMod t :=
    (ZMod.castHom hdiv (ZMod t))
      ((unorderedResidueFirstSet N t hbound).sum id)
  intro c
  let i : Fin t := ⟨(c - C - (t - 1 : ZMod t)).val,
    ZMod.val_lt _⟩
  refine ⟨unorderedResidueWitness N t hbound i, ?_⟩
  calc
    unorderedSubsetResidue hdiv (unorderedResidueWitness N t hbound i) =
      ((t - 1 + i.val : ℕ) : ZMod t) + C :=
      unorderedResidueWitness_value N t hbound hdiv i
    _ = ((t - 1 : ℕ) : ZMod t) + (i.val : ZMod t) + C := by
      push_cast
      abel
    _ = c := by
      change ((t - 1 : ℕ) : ZMod t) +
        (((c - C - (t - 1 : ZMod t)).val : ℕ) : ZMod t) + C = c
      rw [ZMod.natCast_zmod_val]
      abel

end EPPAReducts.BoundedEquivalence
