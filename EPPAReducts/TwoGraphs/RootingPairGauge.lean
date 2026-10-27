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
noncomputable def rootLiftSource {V : Type} (p : PartialBijection V) :
    RootLiftDomain p ↪ Option V :=
  subtypeEmbedding (rootedSupport p.source)

/-- The lifted partial map, evaluated as an injective map into the
same root-adjoined carrier. -/
noncomputable def rootLiftTarget {V : Type} (p : PartialBijection V) :
    RootLiftDomain p ↪ Option V :=
  equivThenEmbedding (liftRootPartial p).bijection
    (subtypeEmbedding (rootedSupport p.target))

/-- Direct evaluation of the two rooted embeddings. Keeping the maps opaque
when rewriting avoids instance-sensitive semireducible subtype casts. -/
@[simp] theorem rootLiftSource_none {V : Type}
    (p : PartialBijection V) (h : none ∈ rootedSupport p.source) :
    rootLiftSource p ⟨none, h⟩ = none := rfl

@[simp] theorem rootLiftSource_some {V : Type}
    (p : PartialBijection V) (x : V)
    (h : some x ∈ rootedSupport p.source) :
    rootLiftSource p ⟨some x, h⟩ = some x := rfl

@[simp] theorem rootLiftTarget_none {V : Type}
    (p : PartialBijection V) (h : none ∈ rootedSupport p.source) :
    rootLiftTarget p ⟨none, h⟩ = none := by
  change ((liftRootPartial p).bijection ⟨none, h⟩).val = none
  simpa using liftRootPartial_root p

@[simp] theorem rootLiftTarget_some {V : Type}
    (p : PartialBijection V) (x : V)
    (h : some x ∈ rootedSupport p.source) :
    rootLiftTarget p ⟨some x, h⟩ =
      some ((p.bijection ⟨x, (mem_rootedSupport_some p.source x).mp h⟩).val) := by
  change ((liftRootPartial p).bijection ⟨some x, h⟩).val =
    some ((p.bijection
      ⟨x, (mem_rootedSupport_some p.source x).mp h⟩).val)
  simpa using liftRootPartial_old p x
    ((mem_rootedSupport_some p.source x).mp h)

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
          rw [rootLiftTarget_none p hu,
            rootLiftTarget_some p y hv,
            rootLiftSource_none p hu,
            rootLiftSource_some p y hv]
          simpa [rootGauge, rootedPairBit_root, boolBit] using
            (twice_zmod2 (boolBit δ)).symm
  | some x =>
      have hx : x ∈ p.source :=
        (mem_rootedSupport_some p.source x).mp hu
      cases v with
      | none =>
          rw [rootLiftTarget_some p x hu,
            rootLiftTarget_none p hv,
            rootLiftSource_some p x hu,
            rootLiftSource_none p hv]
          have swap (y : V) :
              ({some y, none} : Finset (Option V)) =
                ({none, some y} : Finset (Option V)) := by
            ext z
            simp [or_comm]
          rw [swap x, swap ((p.bijection ⟨x, hx⟩).val)]
          simpa [rootGauge, rootedPairBit_root, boolBit] using
            (twice_zmod2 (boolBit δ)).symm
      | some y =>
          have hy : y ∈ p.source :=
            (mem_rootedSupport_some p.source y).mp hv
          have hxy : x ≠ y := by
            intro h
            subst y
            exact huv (by rfl)
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
          rw [rootLiftTarget_some p x hu,
            rootLiftTarget_some p y hv,
            rootLiftSource_some p x hu,
            rootLiftSource_some p y hv]
          rw [rootedPairBit_old c px py hpxy,
              rootedPairBit_old c x y hxy]
          simpa [rootGauge, px, py] using hb

end EPPAReducts.TwoGraphs
