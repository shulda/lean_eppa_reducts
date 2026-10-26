import EPPAReducts.BoundedEquivalence.OrderedKernelAutGroup
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# Fixed-vertex bound for a nontrivial class action on ordered tuples

If an automorphism of the unlabelled ordered r-tuple equivalence
permutes its auxiliary class names without fixed classes, then it
cannot fix r distinct vertices: the injective tuple on those
vertices would have to have both a fixed and a moved class.

This is the ordered-tuple analogue of ClassShiftFixed.lean and is
independent of the special cyclic obstruction construction.
-/

namespace EPPAReducts.BoundedEquivalence

/-- A fixed-point-free action on the auxiliary class names, when
compatible with an induced vertex permutation on injective ordered
r-tuples, forces fewer than r fixed vertices. -/
theorem orderedClassShift_fixedVertices_card_lt
    {V κ : Type} [Fintype V] [DecidableEq V] {r : ℕ}
    (f : InjectiveTuples V r → κ)
    (g : Equiv.Perm V) (shift : Equiv.Perm κ)
    (hshift : ∀ c : κ, shift c ≠ c)
    (hcompat : ∀ t : InjectiveTuples V r,
      f (permuteOrderedTuple g t) = shift (f t)) :
    (Finset.univ.filter (fun x : V => g x = x)).card < r := by
  classical
  letI : Fintype
      {x : V // x ∈ Finset.univ.filter (fun x : V => g x = x)} :=
    Fintype.ofFinite _
  by_contra hnot
  have hle : r ≤ (Finset.univ.filter (fun x : V => g x = x)).card :=
    Nat.le_of_not_gt hnot
  have hcard :
      Fintype.card (Fin r) ≤
        Fintype.card
          {x : V // x ∈ Finset.univ.filter (fun x : V => g x = x)} := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hle
  obtain ⟨e⟩ :
      Nonempty (Fin r ↪
        {x : V // x ∈ Finset.univ.filter (fun x : V => g x = x)}) :=
    Function.Embedding.nonempty_of_card_le hcard
  let t : InjectiveTuples V r :=
    ⟨fun i => (e i).val, by
      intro i j hij
      apply e.injective
      exact Subtype.ext hij⟩
  have hfix (i : Fin r) : g (e i).val = (e i).val :=
    (Finset.mem_filter.mp (e i).property).2
  have htuple : permuteOrderedTuple g t = t := by
    apply Subtype.ext
    funext i
    exact hfix i
  have hc : f t = shift (f t) := by
    simpa only [htuple] using hcompat t
  exact hshift (f t) hc.symm

end EPPAReducts.BoundedEquivalence
