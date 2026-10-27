import EPPAReducts.TwoGraphs.RootingColourShift
import EPPAReducts.TwoGraphs.PairParityMapTransport

/-!
# Pairwise F₂ gauge law for a root-fixing lifted partial bijection

A literal unlabelled pair-class partial automorphism changes every old
pair label by a common Boolean XOR bit. With a new isolated root,
this is exactly a uniform F₂ edge shift plus a gauge supported at the
root. No class colours are added to the language of the structure.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- The rooted source domain of a literal partial bijection. -/
abbrev RootLiftDomain {V : Type} (p : PartialBijection V) :=
  {u : Option V // u ∈ rootedSupport p.source}

/-- The original vertex map on the domain containing the root. -/
def rootLiftSource {V : Type} (p : PartialBijection V) :
    RootLiftDomain p ↪ Option V :=
  subtypeEmbedding (rootedSupport p.source)

/-- The lifted partial map, evaluated as an injective map into the
same root-adjoined carrier. -/
def rootLiftTarget {V : Type} (p : PartialBijection V) :
    RootLiftDomain p ↪ Option V :=
  equivThenEmbedding (liftRootPartial p).bijection
    (subtypeEmbedding (rootedSupport p.target))

/-- The root-supported gauge term is δ at the new root, zero elsewhere. -/
def rootGauge {V : Type} (p : PartialBijection V)
    (δ : Bool) (u : RootLiftDomain p) : ZMod 2 :=
  if u.val = none then boolBit δ else 0

private theorem twice_zmod2 (d : ZMod 2) : d + d = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc
    d + d = 2 * d := by ring
    _ = 0 := by rw [h2]; simp

/-- The actual rooted pair-colour transformations satisfy the common
uniform-shift plus root-gauge equation. The result is for every two
DISTINCT vertices of the true rooted partial domain. -/
theorem rootLift_pairGauge
    {V : Type} [DecidableEq V]
    (c : UnorderedPairs V → Bool)
    (p : PartialBijection V) (δ : Bool)
    (hshift :
      ∀ e : UnorderedPairs {v : V // v ∈ p.source},
        c (mapPair (equivThenEmbedding p.bijection
          (subtypeEmbedding p.target)) e) =
        Bool.xor
          (c (mapPair (subtypeEmbedding p.source) e)) δ)
    (u v : RootLiftDomain p) (huv : u ≠ v) :
    boolBit (rootedPairBit c
      {rootLiftTarget p u, rootLiftTarget p v}) =
      boolBit (rootedPairBit c
        {rootLiftSource p u, rootLiftSource p v}) +
          boolBit δ + rootGauge p δ u + rootGauge p δ v := by
  classical
  change
    boolBit (rootedPairBit c
      {((liftRootPartial p).bijection u).val,
        ((liftRootPartial p).bijection v).val}) =
    boolBit (rootedPairBit c {u.val, v.val}) +
      boolBit δ +
      (if u.val = none then boolBit δ else 0) +
      (if v.val = none then boolBit δ else 0)
  rcases u with ⟨u, hu⟩
  rcases v with ⟨v, hv⟩
  cases u with
  | none =>
      cases v with
      | none =>
          exact False.elim (huv (by rfl))
      | some y =>
          have hy : y ∈ p.source :=
            (mem_rootedSupport_some p.source y).mp hv
          have hr :
              ((liftRootPartial p).bijection ⟨none, hu⟩).val = none := by
            simpa using liftRootPartial_root p
          have hy' :
              ((liftRootPartial p).bijection ⟨some y, hv⟩).val =
                some ((p.bijection ⟨y, hy⟩).val) := by
            simpa using liftRootPartial_old p y hy
          rw [hr, hy']
          simp only [if_true, Option.some_ne_none, ↓reduceIte,
            rootedPairBit_root]
          simp [twice_zmod2]
  | some x =>
      have hx : x ∈ p.source :=
        (mem_rootedSupport_some p.source x).mp hu
      have hx' :
          ((liftRootPartial p).bijection ⟨some x, hu⟩).val =
            some ((p.bijection ⟨x, hx⟩).val) := by
        simpa using liftRootPartial_old p x hx
      cases v with
      | none =>
          have hr :
              ((liftRootPartial p).bijection ⟨none, hv⟩).val = none := by
            simpa using liftRootPartial_root p
          rw [hr, hx']
          have swap (y : V) :
              ({some y, none} : Finset (Option V)) =
                ({none, some y} : Finset (Option V)) := by
            ext z
            simp [or_comm]
          rw [swap x, swap ((p.bijection ⟨x, hx⟩).val)]
          simp only [rootedPairBit_root]
          simp [twice_zmod2]
      | some y =>
          have hy : y ∈ p.source :=
            (mem_rootedSupport_some p.source y).mp hv
          have hxy : x ≠ y := by
            intro h
            subst y
            exact huv (by rfl)
          have hy' :
              ((liftRootPartial p).bijection ⟨some y, hv⟩).val =
                some ((p.bijection ⟨y, hy⟩).val) := by
            simpa using liftRootPartial_old p y hy
          let px : V := (p.bijection ⟨x, hx⟩).val
          let py : V := (p.bijection ⟨y, hy⟩).val
          have hpxy : px ≠ py := by
            intro heq
            have hs :
                p.bijection ⟨x, hx⟩ = p.bijection ⟨y, hy⟩ :=
              Subtype.ext heq
            have h := p.bijection.injective hs
            exact hxy (congrArg Subtype.val h)
          let e : UnorderedPairs {z : V // z ∈ p.source} :=
            ⟨{⟨x, hx⟩, ⟨y, hy⟩}, by
              have hsub : (⟨x, hx⟩ : {z : V // z ∈ p.source}) ≠
                  ⟨y, hy⟩ := by
                intro heq
                exact hxy (congrArg Subtype.val heq)
              simp [hsub]⟩
          have hsrc :
              mapPair (subtypeEmbedding p.source) e =
                (⟨{x, y}, by simp [hxy]⟩ : UnorderedPairs V) := by
            apply Subtype.ext
            simp [e, mapPair, subtypeEmbedding]
          have hdst :
              mapPair (equivThenEmbedding p.bijection
                (subtypeEmbedding p.target)) e =
                (⟨{px, py}, by simp [hpxy]⟩ : UnorderedPairs V) := by
            apply Subtype.ext
            simp [e, mapPair, equivThenEmbedding, subtypeEmbedding, px, py]
          have hcol := hshift e
          rw [hsrc, hdst] at hcol
          have hb := congrArg boolBit hcol
          rw [boolBit_xor] at hb
          rw [hx', hy']
          rw [rootedPairBit_old c px py hpxy,
              rootedPairBit_old c x y hxy]
          simpa [px, py] using hb

end EPPAReducts.TwoGraphs
