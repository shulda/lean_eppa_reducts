# Verification and reproducibility

## Audited baseline

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
git checkout d12d133a37d909837c6fbf4c7409f699f2918264
lake exe cache get
lake build
```

The pinned toolchain is Lean **v4.34.1** with a pinned Mathlib and `AllThoseEPPA` dependency. An audit on a later branch must be cited using its own exact commit and successful run. Cancelled intermediate workflows do not constitute certification.

## Trust levels

1. **Lean kernel:** proved declarations in the imported root, no unchecked logical axioms beyond the allowlist.
2. **Independent semantic check:** inspection of definition fields, quantifiers, induced embeddings, class-label semantics and the unpublished mathematical source, without publishing source text.
3. **External mathematical facts:** classical results used in the manuscript's final classification. They are not claimed to be proved in this Lean repository merely by citing them.

The GitHub Wiki pages are editable explanations; the source of truth is always the exact Lean theorem declaration at its audited commit.
