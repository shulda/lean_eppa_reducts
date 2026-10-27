# Publish the source-controlled documentation to the GitHub Wiki

The Markdown pages under [`docs/wiki/`](https://github.com/shulda/lean_eppa_reducts/tree/main/docs/wiki) are the authoritative, version-controlled Wiki source. They follow the pattern used by `lean_all_those_eppa_classes` and `lean_eppa_semigeneric`.

The [publishing workflow](https://github.com/shulda/lean_eppa_reducts/blob/main/.github/workflows/publish-wiki.yml) runs on `main` when Wiki sources change, on Wiki `gollum` events and on manual dispatch. The job has `contents: write` permissions **only for Wiki publishing**; the Lean proof CI remains read-only.

## First-page initialization

GitHub can show **Wiki enabled** before its independent `.wiki.git` repository exists. If the publishing workflow reports that the Wiki is not initialized:

1. Open the [EPPA reducts Wiki](https://github.com/shulda/lean_eppa_reducts/wiki) while signed into GitHub.
2. Create a page named **Home** and save it once. Temporary text is sufficient.
3. The `gollum` hook or a manual [Publish EPPA reducts Wiki](https://github.com/shulda/lean_eppa_reducts/actions/workflows/publish-wiki.yml) run can then synchronize the source pages.
4. Verify an actual successful publishing action before treating the GitHub Wiki tab as synchronized.

The publishing action copies `docs/wiki/README.md` to `Home.md` and includes the other pages and sidebar. Editing Wiki pages directly can be overwritten by the next source-controlled sync.

**Confidentiality:** the workflow publishes only independently written Markdown documentation. No private research draft or proof notes are part of `docs/wiki/`.
