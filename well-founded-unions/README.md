# Well-founded unions: recovered proofs and tests

Prepared 9 November 2026. **This is an incomplete recovery package, not the
complete November general-certificate artifact.** Read [STATUS.md](STATUS.md)
and [MISSING_COMPONENTS.json](MISSING_COMPONENTS.json) before citing its scope.
No manuscript, PDF, LaTeX source, proof object, runtime binary, or credential is
included. Nothing in this preparation has been published.

| Directory | Contents |
| --- | --- |
| `formal_proofs/` | Standalone countable four-relation counterexample from the existing publication clone |
| `supplement-2026-10-20/rocq/` | Separate October finite-termination, height, branching, and abstract-rank development; typed statement audits |
| `supplement-2026-10-20/scripts/` | Fresh compilation, all-declaration assumption audit, and independent kernel-check runner |
| `supplement-2026-10-20/checks/` | Exhaustive small tests and local SMT diagnostic programs |
| `supplement-2026-10-20/originals/` | Failed historical source used only to check that all 92 original theorem statements are preserved |
| `finite/` | Original encoders, coverage tables, audit, and exact inputs/outputs for the last two search branches |
| `verification/` | Portable 722-case saved-result audit |
| `validation/` | Fresh commands, versions, exit statuses, complete logs, and experimental results |
| `historical/` | Earlier reports and diagnostic records; never evidence of a new run |

From this directory, with Python 3 and Rocq 9.1.1 (`rocq` and `rocqchk`) on PATH:

```sh
python3 verify.py --scope recovered
```

This checks the manifest, audits saved finite results, compiles and independently
kernel-checks both recovered Rocq developments, audits proof assumptions and
statement preservation, and reruns both exhaustive small tests. It returns
nonzero on any failed check. Builds use temporary copies; archived files and
historical reports remain unchanged. Logs are kept in the temporary directory
printed at completion. Use `--log-dir /path/to/new-directory` to retain them at
a chosen location outside this artifact.

To also run the local SMT diagnostics with Z3 installed:

```sh
python3 verify.py --scope recovered --with-smt
```

The helper accepts a `z3` executable on PATH or a shared library specified by
`LIBZ3`. The fresh run used the locally installed Z3 4.12.2 library. It does not
redistribute that library. Python optimization (`-O`) is rejected because the
original audits use assertions.

```sh
python3 verify.py
```

The default **full requested scope currently exits 2** after checking recovered
material, because the general certificate/checkers, five-relation experiment,
reset check, and current theorem correspondence remain unavailable. It must not
be presented as a full-package pass. Integration of the missing checks is still
required; merely deleting the missing-components list cannot establish a pass.

For integrity or the historical search audit alone:

```sh
python3 verify_integrity.py
python3 verification/verify_results.py
```

The 722 total is 150 nine-point cases plus 572 ten-point terminal obligations.
The audit verifies saved outcomes, coverage, exit codes where recorded, and exact
regeneration of both final inputs. It does not rerun the historical searches or
check SMT proof certificates. Earlier leaves are represented by tables; only
the last two branches have exact inputs and raw solver output in this recovery.
The incomplete component-mask exploration contributes no terminal leaves.

Both final inputs can separately be replayed by a compatible Z3 executable:

```sh
z3 finite/completion/runs/v7_a3_baseline/input.smt2
z3 finite/completion/runs/v8_a4_baseline/input.smt2
```

They contain a 300-second timeout. `unknown` is not `unsat`. These reruns were
not performed during this preparation. The fresh SMT results in `validation/`
are the separate local folding/height diagnostics.

The source inventory is [SOURCE_FILES.json](SOURCE_FILES.json); collection
choices and the single portability change are in [PROVENANCE.md](PROVENANCE.md).
The requested paper-number mapping remains unresolved; verified source symbols
and explicit exclusions are in [THEOREM_MAP.md](THEOREM_MAP.md).

Existing source notices are retained. No new license or third-party library is
introduced by this package.

To rebuild the deterministic ZIP and its external checksum after reviewing any
source changes, use `python3 package.py --output-dir ../bundles`. The internal
manifest covers every distributed file except itself; the external ZIP checksum
covers that manifest too. The packaging command refuses paper and compiled-proof
files. The validation records include checks that altered evidence and an
intentionally invalid proof in disposable copies cause verification to fail.
