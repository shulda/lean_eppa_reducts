import EPPAReducts.BoundedEquivalence.CosetOrbitIncidenceInjection
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The quantitative normalizer-coset fixed-orbit bound

Count the same incidence type in two ways: each selected, fixable,
L-orbit has exactly |L| incidences, while the entire normalizer
coset contributes at most b|L| incidences if each of its members
fixes at most b vertices. Cancelling |L| proves the desired
number-of-orbits bound, without choosing a quotient of orbits.
-/

namespace EPPAReducts.BoundedEquivalence

universe u

/-- The total number of twisted fixed-point incidences is bounded
by b times the cardinality of L if every coset member fixes at most
b vertices. -/
theorem card_cosetFixedIncidence_le
    {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    (L : Subgroup (Equiv.Perm Ω)) [Fintype L] (g : Equiv.Perm Ω) (b : ℕ)
    (hcap : ∀ l : L,
      (Finset.univ.filter (fun x : Ω => l.val (g x) = x)).card ≤ b) :
    Fintype.card (CosetFixedIncidence L g) ≤
      Fintype.card L * b := by
  classical
  calc
    Fintype.card (CosetFixedIncidence L g) =
        ∑ l : L, Fintype.card {x : Ω // l.val (g x) = x} := by
      exact Fintype.card_sigma
    _ = ∑ l : L,
        (Finset.univ.filter (fun x : Ω => l.val (g x) = x)).card := by
      apply Finset.sum_congr rfl
      intro l hl
      simp only [Fintype.card_subtype]
    _ ≤ ∑ _l : L, b := by
      apply Finset.sum_le_sum
      intro l hl
      exact hcap l
    _ = Fintype.card L * b := by simp

/-- Any family of pairwise orbit-inequivalent vertices fixed by
some member of the normalizer coset has cardinality at most b,
provided each coset member has at most b fixed vertices.
In particular this is the finite form of the coset-orbit lemma
needed for the non-EPPA contradiction. -/
theorem coset_fixable_orbit_representatives_card_le
    {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    (L : Subgroup (Equiv.Perm Ω))
    (g : Equiv.Perm Ω)
    (hg : g ∈ Subgroup.normalizer L)
    (b : ℕ)
    (hcap : ∀ l : L,
      (Finset.univ.filter (fun x : Ω => l.val (g x) = x)).card ≤ b)
    (R : Finset Ω)
    (hsep : ∀ x y : Ω, x ∈ R → y ∈ R →
      (∃ a : L, a.val x = y) → x = y)
    (hfix : ∀ x : Ω, x ∈ R →
      ∃ l : L, l.val (g x) = x) :
    R.card ≤ b := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  let e : OrbitTaggedIncidence L g R ≃
      ({x : Ω // x ∈ R} × L) :=
    (Equiv.sigmaCongrRight (fun (r : {x : Ω // x ∈ R}) =>
      cosetOrbitIncidenceEquivGroup L g hg r.val
        (hfix r.val r.property))).trans
      (Equiv.sigmaEquivProd _ _)
  have hcard :
      Fintype.card (OrbitTaggedIncidence L g R) =
        R.card * Fintype.card L := by
    calc
      Fintype.card (OrbitTaggedIncidence L g R) =
          Fintype.card ({x : Ω // x ∈ R} × L) :=
        Fintype.card_congr e
      _ = R.card * Fintype.card L := by
        simp [Fintype.card_prod]
  have hinj :
      Fintype.card (OrbitTaggedIncidence L g R) ≤
        Fintype.card (CosetFixedIncidence L g) :=
    Fintype.card_le_of_injective
      (orbitTaggedIncidenceEmbedding L g R hsep)
      (orbitTaggedIncidenceEmbedding L g R hsep).injective
  have hupper :
      Fintype.card (CosetFixedIncidence L g) ≤
        Fintype.card L * b :=
    card_cosetFixedIncidence_le L g b hcap
  have hmul : R.card * Fintype.card L ≤
      b * Fintype.card L := by
    calc
      R.card * Fintype.card L =
          Fintype.card (OrbitTaggedIncidence L g R) := hcard.symm
      _ ≤ Fintype.card (CosetFixedIncidence L g) := hinj
      _ ≤ Fintype.card L * b := hupper
      _ = b * Fintype.card L := Nat.mul_comm _ _
  have hpos : 0 < Fintype.card L := Fintype.card_pos
  exact (Nat.mul_le_mul_right_iff hpos).mp hmul

end EPPAReducts.BoundedEquivalence
