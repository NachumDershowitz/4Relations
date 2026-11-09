# Well-founded unions: formal proofs and experiments

This branch distributes formal proofs, tests, experimental evidence, and
verification records for well-founded unions. The current tree excludes paper
files. Earlier commits and releases retain their existing contents.

The complete artifact is in [well-founded-unions/](well-founded-unions/README.md).
Its [theorem map](well-founded-unions/THEOREM_MAP.md) and
[verification status](well-founded-unions/STATUS.md) identify the exact scope.

| Path | Contents |
| --- | --- |
| `well-founded-unions/general/formal/` | Certificate, two replay checkers, generators, audits, regressions, and Rocq proof-term export |
| `well-founded-unions/general/supplement/` | Five-relation experiment and supplementary diagnostics |
| `well-founded-unions/reset/` | Bounded reset-example check |
| `well-founded-unions/validation/2026-11-09-complete/` | Fresh complete verification and experiment records |
| `formal_proofs/`, `finite/`, `verification/` | Original counterexample, finite-search evidence, and portable archive audit |
| `MANIFEST.json` | Checksums of the current proof-and-test tree |

## Reproduce verification

Python 3, Rocq 9.1.1 (`rocq` and `rocqchk`), and a C++17 compiler are required.
With Z3 installed, the full validation command is:

```sh
python3 verification/verify_archive.py
python3 well-founded-unions/verify.py --with-smt
```

Omit `--with-smt` to skip the supplementary SMT diagnostics. All general proof,
Rocq, finite-coverage, five-tuple, regression, and bounded reset checks still run.
See the artifact README for LIBZ3/CXX overrides and individual checks.

Fresh validation passed: 7,583 inferences and 114 named general theorems replay
in both independent checkers; 18 exact statements and 30 regression tests pass;
the certificate and Rocq export regenerate exactly; Rocq compiles and independently
kernel-checks the export. Of the 114 named theorems, 63 are closed and 51 use only
classical excluded middle. The separate infinite counterexample is axiom-free.
The October development remains separately identified and kernel-checked.

The archived search audit covers 722 cases and exactly regenerates the last two
SMT inputs. It does not rerun historical solver calls or check their proof
certificates. The five-relation experiment was freshly rerun on all 9,765,625
ordered tuples, finding no counterexample. The reset check is bounded testing.
The rank theorems use an explicit abstract well-order/canonical-rank interface;
set-theoretic ordinals and rank existence are not constructed here.

## Publication scope

Only proofs, tests, supporting evidence, and documentation belong in the current
publication tree. `/paper/` is ignored to prevent accidental re-addition. The
current branch contains the complete verified proof-and-test artifact and excludes
the former paper folder.
No existing repository history or release has been replaced.

Use [CITATION.cff](CITATION.cff) for attribution and identify the exact commit or
verified release when citing the artifact.
