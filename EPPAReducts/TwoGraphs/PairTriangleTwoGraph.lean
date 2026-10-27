import EPPAReducts.TwoGraphs.ValuationTwoGraph
import EPPAReducts.TwoGraphs.RootingParity
import EPPAReducts.TwoGraphs.RawFourPointParity
import Mathlib.Tactic.FinCases

/-!
# The two-graph associated with an arbitrary colouring of unordered pairs

For a triple, add the three edge bits in F₂. The sum of all four
triple parities on a four-set is zero because every edge occurs twice.
The construction produces the *literal* finite-set four-point parity
specified in HumanTargets.TwoGraph.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

variable {V : Type} [DecidableEq V]

/-- A Boolean indicator of whether an element of F₂ is one. -/
private theorem boolBit_decide_one (z : ZMod 2) :
    boolBit (decide (z = 1)) = z := by
  classical
  fin_cases z
  · simp [boolBit, show (0 : ZMod 2) ≠ 1 by decide]
  · simp [boolBit]

/-- Form the triple parity of a completely arbitrary pair-bit function.
Non-triples are false, as required by the exact two-graph API. -/
noncomputable def pairParityTriple (c : Finset V → Bool) (s : Finset V) : Bool := by
  classical
  exact if s.card = 3 then
    decide (((s.powersetCard 2).sum (fun e => boolBit (c e))) = (1 : ZMod 2))
  else false

private theorem pairParityTriple_onlyTriples
    (c : Finset V → Bool) (s : Finset V)
    (hs : pairParityTriple c s = true) : s.card = 3 := by
  classical
  by_contra hne
  simp [pairParityTriple, hne] at hs

/-- Evaluation of the unordered triple: exactly the three pair bits. -/
theorem boolBit_pairParityTriple_three
    (c : Finset V → Bool) (a b d : V)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    boolBit (pairParityTriple c ({a, b, d} : Finset V)) =
      boolBit (c {a, b}) + boolBit (c {a, d}) + boolBit (c {b, d}) := by
  classical
  have hcard : ({a, b, d} : Finset V).card = 3 := by
    simp [hab, had, hbd]
  have h1 : ({a, b} : Finset V) ≠ {a, d} := by
    intro heq
    have hmem : b ∈ ({a, d} : Finset V) := by rw [← heq]; simp
    simpa [hab.symm, hbd] using hmem
  have h2 : ({a, b} : Finset V) ≠ {b, d} := by
    intro heq
    have hmem : a ∈ ({b, d} : Finset V) := by rw [← heq]; simp
    simpa [hab, had] using hmem
  have h3 : ({a, d} : Finset V) ≠ {b, d} := by
    intro heq
    have hmem : a ∈ ({b, d} : Finset V) := by rw [← heq]; simp
    simpa [hab, had] using hmem
  simp only [pairParityTriple]
  rw [if_pos hcard, boolBit_decide_one,
    powersetCard_two_of_triple a b d hab had hbd]
  simp [h1, h2, h3, add_assoc]

/-- Boolean four-point evenness of triangle parities. -/
theorem pairParityTriple_fourPointXor
    (c : Finset V → Bool)
    (a b d e : V)
    (hab : a ≠ b) (had : a ≠ d) (hae : a ≠ e)
    (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e) :
    Bool.xor
      (Bool.xor
        (Bool.xor (pairParityTriple c (triple a b d))
          (pairParityTriple c (triple a b e)))
        (pairParityTriple c (triple a d e)))
      (pairParityTriple c (triple b d e)) = false := by
  classical
  have hsum :
      boolBit (pairParityTriple c (triple a b d)) +
        boolBit (pairParityTriple c (triple a b e)) +
        boolBit (pairParityTriple c (triple a d e)) +
        boolBit (pairParityTriple c (triple b d e)) = 0 := by
    simpa only [triple,
      boolBit_pairParityTriple_three c a b d hab had hbd,
      boolBit_pairParityTriple_three c a b e hab hae hbe,
      boolBit_pairParityTriple_three c a d e had hae hde,
      boolBit_pairParityTriple_three c b d e hbd hbe hde,
      triangleOfPairs] using
        (triangleOfPairs_fourPoint
          (fun x y : V => boolBit (c {x, y})) a b d e)
  have hxor :
      boolBit (Bool.xor
        (Bool.xor
          (Bool.xor (pairParityTriple c (triple a b d))
            (pairParityTriple c (triple a b e)))
          (pairParityTriple c (triple a d e)))
        (pairParityTriple c (triple b d e))) = 0 := by
    simp only [boolBit_xor]
    exact hsum
  have hbool : ∀ t : Bool, boolBit t = 0 → t = false := by
    intro t ht
    cases t with
    | false => rfl
    | true =>
        have hne : (1 : ZMod 2) ≠ 0 := by decide
        exact False.elim (hne (by simpa [boolBit] using ht))
  exact hbool _ hxor

/-- Genuine four-set cardinality parity; not just an ordered cocycle law. -/
theorem pairParityTriple_fourPointEven
    (c : Finset V → Bool) (q : Finset V) (hq : q.card = 4) :
    (q.powerset.filter (fun s => pairParityTriple c s = true)).card % 2 = 0 := by
  classical
  obtain ⟨a, b, d, e, hab, had, hae, hbd, hbe, hde, rfl⟩ :=
    Finset.card_eq_four.mp hq
  have hfiltered :
      (({a, b, d, e} : Finset V).powerset.filter
        (fun s => pairParityTriple c s = true)) =
      (({a, b, d, e} : Finset V).powersetCard 3).filter
        (fun s => pairParityTriple c s = true) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨hs, ht⟩
      exact ⟨⟨hs, pairParityTriple_onlyTriples c s ht⟩, ht⟩
    · rintro ⟨⟨hs, _⟩, ht⟩
      exact ⟨hs, ht⟩
  rw [hfiltered, powersetCard_three_of_quadruple
    a b d e hab had hae hbd hbe hde]
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ :=
    four_triple_subsets_distinct a b d e hab had hae hbd hbe hde
  apply (four_filter_even_iff_xor
    (f := pairParityTriple c)
    ({a, b, d} : Finset V) ({a, b, e} : Finset V)
    ({a, d, e} : Finset V) ({b, d, e} : Finset V)
    h12 h13 h14 h23 h24 h34).2
  simpa only [triple] using
    (pairParityTriple_fourPointXor c a b d e hab had hae hbd hbe hde)

/-- Every pair-bit colouring yields an actual two-graph. -/
noncomputable def twoGraphOfPairBits (c : Finset V → Bool) : TwoGraph V where
  isTriple := pairParityTriple c
  onlyTriples := pairParityTriple_onlyTriples c
  fourPointEven := pairParityTriple_fourPointEven c

end EPPAReducts.TwoGraphs
