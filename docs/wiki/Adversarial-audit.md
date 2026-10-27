# Adversarial statement and scope audit

The following checks compare the formal declaration signatures and proof dependencies with the mathematical claims independently. The unpublished source document was inspected privately; **no manuscript, bibliography or proof-note extract is published here**.

| Risk | Verified resolution |
| --- | --- |
| Ordinary EPPA presented as coherent EPPA | The positive two-graph target explicitly has a single `extension` function and a `coherent` composition field. |
| Coherence on full automorphisms only | The target ranges over *all* partial bijections preserving induced triples, including distinct source and target subsets. |
| Empty two-graph silently excluded | The final theorem quantifies over all finite vertex types; the proof has an empty-case construction. |
| A fixed choice of graph representative masquerading as a graph modulo complementation | The negative human target uses **equality of pair classes**. Automorphisms may interchange classes. |
| Exactly $m$ classes replacing at most $m$ | The general class has at most $m$ classes. Only the constructed obstruction realizes all $m$. |
| Ordered tuples confused with unordered subsets | Separate definitions, partial-automorphism notions, obstruction constructions and terminal theorems are used. |
| One inconvenient extension mistaken for non-EPPA | The non-EPPA conclusions quantify over **every** finite ambient structure and every induced embedding. |
| The fifth reduct misrepresented as an arbitrary ternary equivalence | The actual interface requires a representative satisfying the literal four-point even-parity law; automorphisms preserve **equality of unnamed triple classes**. |
| Root-fixed extensions misused without proof | The lifted partial map fixes the new root by construction, and the full ambient automorphism extends that exact map, hence fixes the image of the root. |
| A conditional statement mistaken for fifth-reduct non-EPPA | The final `twoGraphsModuloFailEPPA` does not take `RootedPartialLiftProperty` as a hypothesis: `allRootedPartialLifts` supplies a checked proof. |
| Binary-relational coherent EPPA confused with simple-graph coherent EPPA | The proof constructs a literal finite `SimpleGraph` witness by symmetrization and transports induced embedding, all ambient automorphisms, equivalence invariance and coherent composition. |
| A hardcoded yes/no table mistakenly called formalized classification | Every cell is a quantified EPPA/coherent EPPA proposition; the terminal Lean theorem proves the conjunction of all ten. |
| Thomas's enumeration mistakenly presented as proved | Only the EPPA statuses of five specified finite classes are proved; that they exhaust all first-order reducts is a separate external mathematical input. |
| Private manuscript accidentally included | The CI rejects tracked `.tex`, `.bib`, `.sty` and `.cls` files; the public repository contains only separately written Lean and documentation. |

## Intentional discrepancy in the proof, not in the theorem

The coherent two-graph proof takes an ambient index of size $n!$, while the manuscript construction describes a smaller least-common-multiple index. Since $n!$ is divisible by every $1,\ldots,n$, this gives a different (possibly larger) finite witness with **exactly the same claimed property**. There is no size bound in the main theorem that would be affected.

## Original baseline scope versus extended certification

- The particular six-vertex graph modulo complementation obstruction as a standalone minimal/example theorem. The general negative theorem uses another finite obstruction and is strictly sufficient for non-EPPA.
- The rooting reduction **is now formally proved**; see [its adversarial source and quantifier audit](Rooting-reduction.md) and [integrated CI #40517057037](https://github.com/shulda/lean_eppa_reducts/actions/runs/40517057037).
- The full five-reduct EPPA/coherent-EPPA table **is now proved** as [`fiveReductEPPAClassification`](Five-reduct-classification.md).
- Independent formal proofs of the classical five-reduct *model-theoretic list* (Thomas) or of every historical free-amalgamation EPPA theorem, which are external ingredients in the paper's classification.

These must not be labelled `proved` merely because corresponding informal implications are standard. The rooting work has added and audited precise Lean declarations. The final five-reduct EPPA/coherent-EPPA table passed [main CI #40529501919](https://github.com/shulda/lean_eppa_reducts/actions/runs/40529501919) at `9178c621d64c`. Thomas's reduct exhaustion theorem is not among the audited declarations.

## Audit boundary

A successful kernel check establishes the elaborated **Lean proposition**; it cannot by itself establish that an independently worded theorem in a manuscript has exactly that semantics. Conversely, reading the manuscript does not replace kernel proof. Both checks are recorded separately.
