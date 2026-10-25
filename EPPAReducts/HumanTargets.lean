import Mathlib.Data.Finset.Powerset
import Mathlib.GroupTheory.Perm.Basic

/-!
# Human-readable certification targets

This is an **independent specification**, not a proof. It uses finite sets,
bijections, equivalence relations, and permutations rather than the internal
valuation construction or the general AllThoseEPPA interface.

The two propositions at the bottom are the targets for final certification.
Declaring them as propositions does **not** prove them.
-/

namespace EPPAReducts.HumanTargets

/-- The unordered triple of vertices x, y, and z. -/
noncomputable def triple {V : Type} (x y z : V) : Finset V := by
  classical
  exact {x, y, z}

/-- A two-graph: unordered triples with the four-point even-parity property.
Bool is used only as the indicator function of the hyperedge set. -/
structure TwoGraph (V : Type) where
  isTriple : Finset V → Bool
  onlyTriples : ∀ s, isTriple s = true → s.card = 3
  fourPointEven : ∀ q : Finset V, q.card = 4 →
    (q.powerset.filter (fun s => isTriple s = true)).card % 2 = 0

/-- A vertex injection is induced exactly when it preserves and reflects
the distinguished triples. -/
def IsInducedTwoGraphEmbedding {V W : Type}
    (A : TwoGraph V) (B : TwoGraph W) (ι : V ↪ W) : Prop :=
  ∀ x y z : V,
    A.isTriple (triple x y z) =
      B.isTriple (triple (ι x) (ι y) (ι z))

/-- A partial bijection between two subsets of one carrier. The bijection
is defined only on its domain, without dummy values outside that domain. -/
structure PartialBijection (V : Type) where
  source : Finset V
  target : Finset V
  bijection : {x : V // x ∈ source} ≃ {x : V // x ∈ target}

/-- Its optional-value interpretation. -/
noncomputable def PartialBijection.apply? {V : Type}
    (p : PartialBijection V) (x : V) : Option V := by
  classical
  exact if hx : x ∈ p.source then
    some ((p.bijection ⟨x, hx⟩).val)
  else
    none

/-- r = q ∘ p, with the whole range of p exactly the domain of q. -/
def IsComposition {V : Type}
    (p q r : PartialBijection V) : Prop :=
  p.target = q.source ∧
  r.source = p.source ∧
  r.target = q.target ∧
  ∀ x : V, r.apply? x = (p.apply? x).bind q.apply?

/-- Isomorphism between two induced sub-two-graphs. -/
def IsTwoGraphPartialAutomorphism {V : Type}
    (A : TwoGraph V) (p : PartialBijection V) : Prop :=
  ∀ x y z : {v : V // v ∈ p.source},
    A.isTriple (triple x.val y.val z.val) =
      A.isTriple (triple (p.bijection x).val
                         (p.bijection y).val
                         (p.bijection z).val)

/-- A vertex permutation which is actually an automorphism of the two-graph. -/
def IsTwoGraphAutomorphism {V : Type}
    (A : TwoGraph V) (g : Equiv.Perm V) : Prop :=
  ∀ x y z : V,
    A.isTriple (triple x y z) =
      A.isTriple (triple (g x) (g y) (g z))

/-- A permutation g of the witness extends the partial bijection p along
the chosen embedding ι of the old vertices. -/
def Extends {V W : Type}
    (ι : V ↪ W) (p : PartialBijection V) (g : Equiv.Perm W) : Prop :=
  ∀ (x : V) (hx : x ∈ p.source),
    g (ι x) = ι ((p.bijection ⟨x, hx⟩).val)

/-- All data demanded of a coherent EPPA witness: one common finite
extension and a *simultaneous compositional* choice of automorphisms. -/
structure CoherentTwoGraphWitness {V : Type} (A : TwoGraph V) where
  W : Type
  finiteW : Finite W
  B : TwoGraph W
  inclusion : V ↪ W
  induced : IsInducedTwoGraphEmbedding A B inclusion
  extension : (p : PartialBijection V) →
    IsTwoGraphPartialAutomorphism A p → Equiv.Perm W
  isAutomorphism : ∀ p hp, IsTwoGraphAutomorphism B (extension p hp)
  extends : ∀ p hp, Extends inclusion p (extension p hp)
  coherent : ∀ (p q r : PartialBijection V)
      (hp : IsTwoGraphPartialAutomorphism A p)
      (hq : IsTwoGraphPartialAutomorphism A q)
      (hr : IsTwoGraphPartialAutomorphism A r),
    IsComposition p q r →
      ∀ w : W,
        extension r hr w = extension q hq (extension p hp w)

/-- TARGET A: Every finite two-graph has coherent EPPA. -/
def twoGraphsHaveCoherentEPPA : Prop :=
  ∀ (V : Type), Finite V → ∀ (A : TwoGraph V),
    Nonempty (CoherentTwoGraphWitness A)

/-! ## Graphs modulo global complementation -/

/-- Unordered pairs of distinct vertices. -/
abbrev UnorderedPairs (V : Type) := {s : Finset V // s.card = 2}

/-- Transport an unordered pair through an injective map. -/
def mapPair {V W : Type} (ι : V ↪ W)
    (s : UnorderedPairs V) : UnorderedPairs W :=
  ⟨s.val.map ι, by simpa using s.property⟩

/-- An equivalence relation on unordered pairs with at most two classes.
The existential Boolean labelling is *not* part of the relation's language:
automorphisms may exchange the two classes. -/
structure GraphModuloComplementation (V : Type) where
  sameClass : Setoid (UnorderedPairs V)
  atMostTwoClasses : ∃ label : UnorderedPairs V → Bool,
    ∀ e f, sameClass.r e f ↔ label e = label f

/-- A vertex injection is induced if it preserves and reflects the
equality of equivalence classes, not their auxiliary names. -/
def IsInducedPairEmbedding {V W : Type}
    (A : GraphModuloComplementation V)
    (B : GraphModuloComplementation W) (ι : V ↪ W) : Prop :=
  ∀ e f : UnorderedPairs V,
    A.sameClass.r e f ↔
      B.sameClass.r (mapPair ι e) (mapPair ι f)

/-- The natural inclusion of a subset in its ambient carrier. -/
def subtypeEmbedding {V : Type} (D : Finset V) :
    {x : V // x ∈ D} ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- Compose an equivalence with an embedding. -/
def equivThenEmbedding {X Y Z : Type} (e : X ≃ Y)
    (ι : Y ↪ Z) : X ↪ Z :=
  ⟨fun x => ι (e x), by
    intro x y h
    apply e.injective
    exact ι.injective h⟩

/-- A partial automorphism of the *unlabelled* pair-class equivalence.
It may exchange the two equivalence classes. -/
def IsPairPartialAutomorphism {V : Type}
    (A : GraphModuloComplementation V) (p : PartialBijection V) : Prop :=
  ∀ e f : UnorderedPairs {x : V // x ∈ p.source},
    A.sameClass.r (mapPair (subtypeEmbedding p.source) e)
                  (mapPair (subtypeEmbedding p.source) f) ↔
    A.sameClass.r
      (mapPair (equivThenEmbedding p.bijection
        (subtypeEmbedding p.target)) e)
      (mapPair (equivThenEmbedding p.bijection
        (subtypeEmbedding p.target)) f)

/-- Treat a total bijection as an embedding, for mapping unordered pairs. -/
def embeddingOfEquiv {V W : Type} (g : V ≃ W) : V ↪ W :=
  ⟨g, g.injective⟩

/-- A permutation preserves the unlabelled pair-class equivalence. -/
def IsPairAutomorphism {V : Type}
    (B : GraphModuloComplementation V) (g : Equiv.Perm V) : Prop :=
  ∀ e f : UnorderedPairs V,
    B.sameClass.r e f ↔
      B.sameClass.r (mapPair (embeddingOfEquiv g) e)
                    (mapPair (embeddingOfEquiv g) f)

/-- A common finite EPPA witness B for all partial automorphisms of A. -/
def IsPairEPPAWitness {V W : Type}
    (A : GraphModuloComplementation V)
    (B : GraphModuloComplementation W) (ι : V ↪ W) : Prop :=
  IsInducedPairEmbedding A B ι ∧
    ∀ (p : PartialBijection V),
      IsPairPartialAutomorphism A p →
      ∃ (g : Equiv.Perm W),
        IsPairAutomorphism B g ∧ Extends ι p g

/-- TARGET B: Finite graphs modulo global complementation fail EPPA.
There is a finite A and *no finite* induced extension B which extends all
partial automorphisms of A. -/
def graphsModuloComplementationFailEPPA : Prop :=
  ∃ (V : Type), Finite V ∧
    ∃ (A : GraphModuloComplementation V),
      ∀ (W : Type), Finite W →
        ∀ (B : GraphModuloComplementation W) (ι : V ↪ W),
          ¬ IsPairEPPAWitness A B ι

end EPPAReducts.HumanTargets
