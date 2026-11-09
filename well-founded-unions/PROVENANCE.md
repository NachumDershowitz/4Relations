# Recovery and source preservation

Prepared 9 November 2026 from read-only inspection of existing local material.
`SOURCE_FILES.json` records each collected file, its relative source label, and
its SHA-256 **at collection**. `SHA256SUMS` records the final package bytes.

* `publication-clone`: the clean existing `4Relations-publication` clone on the
  Desktop, branch `wfu-publication-2026-11-08`, commit
  `56596ea54d3bd5c6e1fd195fa236746a4992f428`. The handoff's Documents path no longer
  exists. Finite evidence and standalone counterexample were taken from this
  clone with their original relative structure.
* `october-supplement`: the existing `Documents/ChatGPT/Four Relations` project,
  dated 20 October 2026. Its four Rocq source files, proof verification script,
  failed statement-comparison baseline, diagnostics, and historical reports
  were collected separately. This is not the November general certificate.
* The specified project output directory contained the older
  `four_relations_complete_package.zip` (197 entries),
  `four_relation_progress_revised_package.zip` (16 entries), and
  `four_relation_paper_package.zip` (136 entries). Their manifests showed older
  finite/periodic work, not the named general checkers. No manuscript package or
  unrelated ordinal-diagram development was substituted or copied.

The named `WellFoundedUnions_revised.zip`, `WellFoundedUnions_generalized.zip`,
`WellFoundedUnions_complete.zip`, `Four_Well_Founded_Relations_revised_bundle.zip`,
and `WellFoundedUnions_corrected_source.zip` were not found in Downloads, the
specified project output, the Desktop/Documents project locations, or the
accessible Dropbox and cloud filename search. OneDrive and Trash locations were
inaccessible, so the search does not establish that these files are absent from
every possible storage location. No original archive was changed.

One portability edit was made to a copied diagnostic helper:
`supplement-2026-10-20/checks/z3_runner.py` now imports `os` and honors `LIBZ3`
before shared-library discovery. The original hash remains in SOURCE_FILES.json;
the final hash is in SHA256SUMS. This locates the installed Z3 library without
changing any theorem, assertion, SMT problem, expected result, or solver option.
All four current Rocq sources, the original proof verifier, finite encoders,
recorded finite tables, and saved final SMT inputs remain byte-for-byte copies.

Prior diagnostic outputs are under `historical/`. Fresh diagnostics run in an
isolated source copy; only outputs actually generated there are collected into
`validation/`. The failed baseline is never compiled as a current proof.
Historical absolute paths in metadata identify the original environment; no
file from those paths is copied merely because the metadata mentions it.

The top-level `verify.py`, `verify_integrity.py`, documentation, and packaging
support are new. The manifest excludes itself to avoid a circular checksum;
the external ZIP checksum covers the complete archive, including its manifest.
Existing source notices are retained without adding a license. No Rocq/Z3
runtime, third-party class/style file, manuscript, cache, or compiled proof
object is distributed.
