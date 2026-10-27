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
| Private manuscript accidentally included | The CI rejects tracked `.tex`, `.bib`, `.sty` and `.cls` files; the public repository contains only separately written Lean and documentation. |

## Intentional discrepancy in the proof, not in the theorem

The coherent two-graph proof takes an ambient index of size $n!$, while the manuscript construction describes a smaller least-common-multiple index. Since $n!$ is divisible by every $1,\ldots,n$, this gives a different (possibly larger) finite witness with **exactly the same claimed property**. There is no size bound in the main theorem that would be affected.

## Items that a green baseline CI does *not* certify

- The particular six-vertex graph modulo complementation obstruction as a standalone minimal/example theorem. The general negative theorem uses another finite obstruction and is strictly sufficient for non-EPPA.
- The rooting reduction from two-graphs modulo complementation to pair-equivalence graphs.
- The full classification table of the five reducts as one standalone Lean theorem.
- Independent formal proofs of the classical five-reduct *model-theoretic list* (Thomas) or of every historical free-amalgamation EPPA theorem, which are external ingredients in the paper's classification.

These must not be labelled `proved` merely because corresponding informal implications are standard. The new rooting/classification work should eventually add precise Lean declarations and then update this page with CI references.

## Audit boundary

A successful kernel check establishes the elaborated **Lean proposition**; it cannot by itself establish that an independently worded theorem in a manuscript has exactly that semantics. Conversely, reading the manuscript does not replace kernel proof. Both checks are recorded separately.
