# Well-founded unions: formal proofs and experiments

Complete source-only verification artifact prepared 9 November 2026. The paper
is excluded. [STATUS.md](STATUS.md) distinguishes custom replay, established-kernel
acceptance, archived solver outcomes, and fresh experiments.

| Directory | Contents |
| --- | --- |
| `general/formal/` | Certificate, two independent checkers, generators, 18 exact-statement audits, 30 regression tests, reproducible Rocq proof-term export |
| `general/supplement/` | Five-relation C++ experiment, representative/height tests, supplementary SMT diagnostics and harness regressions |
| `formal_proofs/` | Separate infinite four-relation counterexample in Rocq |
| `finite/` | Encoders, saved coverage tables, and exact inputs/outputs for the final two finite-search branches |
| `reset/checks/` | Small reset-example test, explicitly bounded testing |
| `supplement-2026-10-20/` | Additional older Rocq development and its tests, retained separately |
| `verification/` | Current orchestration and portable saved-result audit |
| `validation/2026-11-09-complete/` | Complete fresh verification, commands, versions, exit statuses, assumption records, and experiments |
| `historical/` | Original reports, source manifests, and saved diagnostics |

From this directory, with Python 3, Rocq 9.1.1 (`rocq` and `rocqchk`), and a C++17
compiler on PATH:

```sh
python3 verify.py
```

To include all supplementary SMT diagnostics, with Z3 available:

```sh
python3 verify.py --with-smt
```

This is the command run for the complete validation. The Z3 helper accepts an
executable on PATH or an installed shared library specified by `LIBZ3`. `CXX` can
name the C++ compiler. No compiler, solver, library, or compiled proof object is
redistributed. The tested toolchain is Python 3.14.5, Rocq 9.1.1 / OCaml 5.4.1,
Apple clang 21.0.0, and Z3 4.12.2 (library distribution 4.12.2.0).

The verifier returns nonzero on failure, uses fresh temporary build directories,
and leaves archived sources and reports unchanged. It prints the log directory;
`--log-dir /path/to/new-directory` retains logs at a chosen location. Python `-O`
is rejected at the top level because some original bounded tests use assertions.
The independent certificate checker and adversarial tests also run under `-O`
where their supplied scripts explicitly test that checks cannot be disabled.

The full run checks both certificate implementations, exact statements, regression
rejections, byte-for-byte regeneration, fresh Rocq compilation, independent kernel
checking, assumptions of all 114 named general theorems, the separate counterexample,
the October supplement, archived finite coverage, all 9,765,625 five-tuples,
representative/height diagnostics, and the reset test. With `--with-smt`, it also
runs the local folding/rank and symbolic counterexample diagnostics.

For integrity or saved finite evidence alone:

```sh
python3 verify_integrity.py
python3 verification/verify_results.py
```

The 722-case count is 150 nine-point cases plus 572 ten-point terminal obligations.
These are audited saved outcomes, not freshly rerun searches. The audit checks
coverage, recorded exit codes, and exact regeneration of both final inputs.
Only the last two branches have full saved SMT inputs and raw output here;
earlier leaves are represented by tables. Z3 proof certificates for these searches
are not independently verified. The incomplete component-mask exploration adds
no terminal leaves.

The final historical calls can separately be replayed with a compatible Z3:

```sh
z3 finite/completion/runs/v7_a3_baseline/input.smt2
z3 finite/completion/runs/v8_a4_baseline/input.smt2
```

Each input sets a 300-second timeout. `unknown` is not `unsat`. The reset check
covers 162 sample states and specified additional transitions/runs; it is not a
proof on the infinite domain. See the exact theorem correspondence and explicit
formalization limits in [THEOREM_MAP.md](THEOREM_MAP.md).

`general/formal/check.sh` deliberately records only custom replay and leaves its
Rocq flags false. `general/formal/check_rocq.sh` writes a separate kernel-success
record. The original export header also describes its historical uncompiled
state. Both are preserved for byte-for-byte reproducibility; current kernel
acceptance is established by the fresh logs and aggregate result, not by changing
those historical descriptions.

`SOURCE_FILES.json` records source hashes at collection; `SHA256SUMS` covers final
artifact bytes. Rebuild the deterministic ZIP and external checksum with
`python3 package.py --output-dir ../bundles`. Existing notices remain in place;
no new license is imposed. All paper, LaTeX, third-party manuscript support,
caches, and compiled objects are excluded.
