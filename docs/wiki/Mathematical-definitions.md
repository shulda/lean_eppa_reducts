# Mathematical definitions and semantic conventions

## EPPA and coherent EPPA

An **ordinary EPPA-witness** for a finite relational structure $A$ is a finite $B$ with an *induced* embedding $\iota:A\hookrightarrow B$ such that **all** partial automorphisms $p$ of $A$ extend to automorphisms $g_p$ of **the same** $B$. In the negative results, non-EPPA means that one finite $A$ defeats every possible finite $B$ and induced embedding.

**Coherent EPPA** additionally requires a simultaneous choice $p\mapsto\Phi(p)$ such that $\Phi(q\circ p)=\Phi(q)\circ\Phi(p)$ for composable partial maps. In the checked standalone specification, the source of $p$ equals the target of $q$, and composition is literal on the full partial domain. The empty partial bijection and the empty input structure are included.

## The exact two-graph API

[`HumanTargets.TwoGraph V`](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/HumanTargets.lean) is an indicator of subsets, true only on subsets of cardinality 3, with the requirement that every 4-subset contains an **even** number of true triples. An embedding preserves and reflects all distinguished triples. A partial automorphism is an isomorphism of induced substructures, not merely a permutation of vertices with a chosen domain.

The checked coherent-EPPA witness has a finite carrier, an actual new two-graph, an induced vertex embedding, and a coherent extension assignment.

## At most $m$ unlabelled equivalence classes

For each $r,m\ge 2$, the unordered version places an equivalence on `RSubsets V r`, the subtype of vertex sets of cardinality exactly $r$. The ordered version places it on **injective** $r$-tuples.

The notation $\le m$ is deliberate: a structure need not use all $m$ classes. An explicit obstruction **does** realize all $m$ labels on a core, but this is a fact about the chosen obstruction, not an extra assumption imposed on arbitrary ambient structures.

In the proofs, auxiliary `Fin m` or `ZMod m` colours *present* an unlabelled equivalence by equality of colours. They are not relation symbols and are not fixed by automorphisms.

## Two distinct complementation issues

- **Graphs modulo complementation** use an equivalence relation on unordered pairs, with at most two classes.
- **Two-graphs modulo complementation** use an equivalence relation on unordered triples whose classes admit a two-graph representative, also with at most two classes.

They are *not* the ordinary graph/two-graph classes, and their automorphism groups differ. Both complementation classes have now been formalized as genuine unlabelled class-equivalence structures; each has a separately checked ordinary non-EPPA theorem. The three-uniform class carries the additional assertion that its class relation admits a four-point-even two-graph representative.

## Paper correspondence

The source-facing independent specifications are in [`HumanTargets.lean`](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/HumanTargets.lean). The mathematical equivalence between the frozen graph-modulo-complementation target and the general arity-two subset-equivalence API is **proved in Lean**, not merely described in prose.

## The five named classes

The [verified classification](Five-reduct-classification.md) uses precisely finite simple graphs ($\mathcal G$), pure finite sets ($\mathcal S$), finite two-graphs ($\mathcal T$), unlabelled pair-class equivalences ($\mathcal G^\pm$) and unlabelled triple-class equivalences admitting a two-graph representative ($\mathcal T^\pm$). These are five different mathematical input classes with independently meaningful EPPA specifications. The table is a proved conjunction; Thomas's theorem enumerating all first-order reducts is external.
