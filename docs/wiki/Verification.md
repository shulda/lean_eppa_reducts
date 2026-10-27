# Verification and reproducibility

## Full five-reduct EPPA/coherent-EPPA classification (main)

- **Exact source commit:** [`9178c621d64cea2e73e65b725bacbd3fc9648ada`](https://github.com/shulda/lean_eppa_reducts/commit/9178c621d64cea2e73e65b725bacbd3fc9648ada).
- **Full GitHub Actions build and axiom audit:** [CI #40529501919](https://github.com/shulda/lean_eppa_reducts/actions/runs/40529501919) — **success**, 27 October 2026.
- **Imported declarations audited:** **1,338**; trusted logical axioms only `propext`, `Classical.choice`, `Quot.sound`.
- **Terminal theorem:** [`EPPAReducts.Classification.fiveReductEPPAClassification`](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/Classification/FiveReductEPPA.lean) : `FiveReductEPPAClassification`.
- **Coverage:** genuine induced/coherent finite witnesses for graphs, sets and two-graphs; ordinary and coherent non-EPPA for graph/two-graph global-complementation reducts.
- **Boundary:** Thomas's exhaustive theorem that these are all first-order reducts, and the manuscript's particular six-vertex illustrative obstruction, are not formally proved as such.

## Latest integrated certification — rooting reduction

- **Main commit:** [`3f35830e34938d91fd082c5f9c9ef47b8e371c98`](https://github.com/shulda/lean_eppa_reducts/commit/3f35830e34938d91fd082c5f9c9ef47b8e371c98).
- **Exact full build/axiom audit:** [CI #40517057037](https://github.com/shulda/lean_eppa_reducts/actions/runs/40517057037) — success on that SHA, 27 October 2026.
- **1,290 audited declarations** under `EPPAReducts`; only `propext`, `Classical.choice`, `Quot.sound`.
- **New terminal proofs:** `graphsModuloHaveEPPA_of_twoGraphsModulo`, `twoGraphsModuloNotHaveEPPA`, `twoGraphsModuloFailEPPA`. The missing rooting partial-lift proposition is proved, not an assumption.
- **Proof scope:** positive graph coherent EPPA and the combined five-reduct classification table are not certified by this particular CI run.

## Original audited baseline

- **Repository:** [`shulda/lean_eppa_reducts`](https://github.com/shulda/lean_eppa_reducts).
- **Complete source commit:** [`d12d133a37d909837c6fbf4c7409f699f2918264`](https://github.com/shulda/lean_eppa_reducts/commit/d12d133a37d909837c6fbf4c7409f699f2918264).
- **Exact GitHub Actions run:** [Lean CI #40471101713](https://github.com/shulda/lean_eppa_reducts/actions/runs/40471101713) — **success** (27 October 2026).
- **Axiom audit:** **1,121** imported declarations; only `propext`, `Classical.choice`, and `Quot.sound` allowed. The full job log confirms that the audit completed successfully.
- **Build root:** [`EPPAReducts.lean`](https://github.com/shulda/lean_eppa_reducts/blob/d12d133a37d909837c6fbf4c7409f699f2918264/EPPAReducts.lean), explicitly importing all terminal positive and negative theorem modules.

The workflow rejects `sorry`, `admit` and custom `axiom` declarations in project sources; it also prevents accidental tracking of the private manuscript file types. The workflow's `axiom-audit` checks the imported Lean dependency graph, not only a displayed theorem signature.

## Reproduce locally

```sh
git clone https://github.com/shulda/lean_eppa_reducts.git
cd lean_eppa_reducts
git checkout 9178c621d64cea2e73e65b725bacbd3fc9648ada
lake exe cache get
lake build
```

The pinned toolchain is Lean **v4.34.1** with a pinned Mathlib and `AllThoseEPPA` dependency. An audit on a later branch must be cited using its own exact commit and successful run. Cancelled intermediate workflows do not constitute certification.

## Trust levels

1. **Lean kernel:** proved declarations in the imported root, no unchecked logical axioms beyond the allowlist.
2. **Independent semantic check:** inspection of definition fields, quantifiers, induced embeddings, class-label semantics and the unpublished mathematical source, without publishing source text.
3. **External mathematical facts:** classical results used in the manuscript's final classification. They are not claimed to be proved in this Lean repository merely by citing them.

The GitHub Wiki pages are editable explanations; the source of truth is always the exact Lean theorem declaration at its audited commit.
