# Source provenance and local repairs

The original archives and local repositories were read without modification.
`SOURCE_FILES.json` lists the relative origin and SHA-256 of every collected file
at collection. `SHA256SUMS` covers the final artifact bytes. `ARCHIVES.json`
identifies both newly supplied ZIPs and the current-paper source used for theorem
correspondence, without including that manuscript.

The principal source is `WellFoundedUnions_generalized.zip`, supplied from iCloud
Drive's Trash. Its 5 November 2026 record contains 7,583 certificate inferences
and 114 named theorems, with successful standalone replay and explicitly false
Rocq acceptance flags. The full `formal/` and `supplement/` source structures are
preserved under `general/`. Original logs, `CHECKED.json`, distribution hashes and
release-check descriptions are under `historical/generalized-2026-11-05/`.
The original manuscript, build files, bibliography/class/style files, and PDF
were excluded. The original formal manifest and proof-term export are unchanged.

`WellFoundedUnions_clean_revision_source.zip`, also supplied from iCloud Drive's
Trash, supplied only `checks/check_reset.py` and its saved JSON record. The script
is under `reset/checks/`; the record is under `historical/reset-clean-revision/`.
Its manuscript theorem statements were read for the map, without editing or
packaging the paper. The original five-relation output file was not in the
supplied generalized ZIP; the source program was recovered, and the complete
9,765,625-tuple computation was freshly rerun and recorded.

The clean Desktop publication clone, branch `wfu-publication-2026-11-08` at
`56596ea54d3bd5c6e1fd195fa236746a4992f428`, supplied the separate counterexample
and finite-search material. Their relative paths and source bytes are preserved.
The October development came from `Documents/ChatGPT/Four Relations`; it remains
separate under `supplement-2026-10-20/`, with historical reports under `historical/`.
Its failed baseline is retained solely for checking the preservation of 92
original theorem statements and is not compiled as a current proof.

Three small changes affect copied original programs:

- Both October and general `checks/z3_runner.py` helpers now import `os` and
  honor `LIBZ3` before shared-library discovery. No solver assertion, expected
  result, or option changed.
- `general/supplement/checks/exhaustive_three_points.py` creates its output
  directory before writing its result. The archive omitted that directory; the
  first run reached the write and failed. The failed log and successful rerun
  are both preserved.

No mathematical proof, certificate, exporter, formal manifest, theorem premise,
finite encoder, historical search result, or saved final SMT input was changed.
Current orchestration, documentation, source/assumption audits, and packaging
scripts are new. Full checks run on temporary copies and retain complete logs,
while excluding all generated proof objects and binaries from the package.

`validation/2026-11-09-initial/` and `validation/2026-11-09-full-scope/` are earlier
checkpoints from before the two archives were supplied. Their missing-component
statuses are historical. `validation/general-2026-11-09/` records the first
new-archive runs, including the repaired output-directory failure.
`validation/2026-11-09-complete/` is the final integrated verification record.
Current status is in the top-level STATUS.md and its final RESULT.json.

Historical distribution manifests may refer to original manuscript files that
are intentionally absent here. Only the top-level SHA256SUMS is the manifest
for this paper-free package. Existing notices are retained without new licensing;
no third-party runtime, manuscript class/style, or unrelated ordinal-diagram
project is redistributed.
