import EPPAReducts.TwoGraphs.PairTriangleTwoGraph
import EPPAReducts.TwoGraphs.ModuloComplementation

/-!
# Rooted two-graph associated with an unlabelled pair colouring

The new vertex is isolated in the underlying graph; an unordered
triple is coloured by the parity of its three edge colours. This
module constructs a genuine four-point-even two-graph, not merely
an arbitrary 3-uniform hypergraph.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets
open EPPAReducts.BoundedEquivalence

variable {V : Type}

/-- Forget the distinguished optional root, retaining each old vertex. -/
noncomputable def dropRoot (s : Finset (Option V)) : Finset V := by
  classical
  exact s.biUnion (fun o => match o with | none => ∅ | some x => {x})

@[simp] theorem dropRoot_two_old
    [DecidableEq V] (x y : V) :
    dropRoot ({some x, some y} : Finset (Option V)) =
      ({x, y} : Finset V) := by
  classical
  simp [dropRoot]

/-- Pair bits on the rooted carrier: every edge through the root is
zero and old-old edges have the original Boolean class label. -/
noncomputable def rootedPairBit
    (c : UnorderedPairs V → Bool)
    (s : Finset (Option V)) : Bool := by
  classical
  exact if h : (dropRoot s).card = 2 ∧ none ∉ s then
    c ⟨dropRoot s, h.1⟩
  else false

@[simp] theorem rootedPairBit_root
    [DecidableEq V] (c : UnorderedPairs V → Bool) (x : V) :
    rootedPairBit c ({none, some x} : Finset (Option V)) = false := by
  classical
  simp [rootedPairBit]

@[simp] theorem rootedPairBit_old
    [DecidableEq V] (c : UnorderedPairs V → Bool) (x y : V) (hxy : x ≠ y) :
    rootedPairBit c ({some x, some y} : Finset (Option V)) =
      c ⟨{x, y}, by simp [hxy]⟩ := by
  classical
  have hd : dropRoot ({some x, some y} : Finset (Option V)) =
      ({x, y} : Finset V) := dropRoot_two_old x y
  have hh :
      (dropRoot ({some x, some y} : Finset (Option V))).card = 2 ∧
        none ∉ ({some x, some y} : Finset (Option V)) := by
    simp [hd, hxy]
  unfold rootedPairBit
  rw [dif_pos hh]
  congr 1
  exact Subtype.ext hd

/-- A graph representative on V induces a two-graph on Option V. -/
noncomputable def rootedTwoGraph (c : UnorderedPairs V → Bool) :
    TwoGraph (Option V) := by
  classical
  exact twoGraphOfPairBits (rootedPairBit c)

private theorem boolBit_injective : Function.Injective boolBit := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolBit]

/-- The triples containing the root encode exactly the old graph. -/
theorem rootedTwoGraph_on_root
    [DecidableEq V] (c : UnorderedPairs V → Bool) (x y : V) (hxy : x ≠ y) :
    (rootedTwoGraph c).isTriple (triple none (some x) (some y)) =
      c ⟨{x, y}, by simp [hxy]⟩ := by
  classical
  apply boolBit_injective
  change boolBit (pairParityTriple (rootedPairBit c)
    ({none, some x, some y} : Finset (Option V))) =
      boolBit (c ⟨{x, y}, by simp [hxy]⟩)
  rw [boolBit_pairParityTriple_three (rootedPairBit c)
      none (some x) (some y) (by simp) (by simp) (by simpa using hxy)]
  simp [rootedPairBit_root, rootedPairBit_old, boolBit]

/-- The non-root triples are the XOR of their three old edges. -/
theorem rootedTwoGraph_on_old
    [DecidableEq V] (c : UnorderedPairs V → Bool) (x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    boolBit ((rootedTwoGraph c).isTriple
      (triple (some x) (some y) (some z))) =
      boolBit (c ⟨{x, y}, by simp [hxy]⟩) +
      boolBit (c ⟨{x, z}, by simp [hxz]⟩) +
      boolBit (c ⟨{y, z}, by simp [hyz]⟩) := by
  classical
  change boolBit (pairParityTriple (rootedPairBit c)
    ({some x, some y, some z} : Finset (Option V))) = _
  rw [boolBit_pairParityTriple_three (rootedPairBit c)
    (some x) (some y) (some z)
    (by simpa using hxy) (by simpa using hxz) (by simpa using hyz)]
  simp [rootedPairBit_old, hxy, hxz, hyz]

end EPPAReducts.TwoGraphs
