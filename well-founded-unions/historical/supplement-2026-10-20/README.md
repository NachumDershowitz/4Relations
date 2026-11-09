# Four Relations: submission and verification supplement

Revised on 20 October 2026 for Nachum Dershowitz's *Four Well-Founded Relations:
Finite Termination and Infinite Nontermination*.

The original positive theorem is attributed to Jeremy Dawson, Nachum Dershowitz,
and Rajeev Goré (IJCAR 2018). This supplement verifies the alternative-condition
termination results and the countable counterexample.

## Deliverables

- `manuscript/Four_Well_Founded_Relations.tex`: revised LMCS source, with its
  bibliography, LMCS class, and bibliography style in the same directory.
- `output/pdf/Four_Well_Founded_Relations.pdf`: compiled manuscript.
- `rocq/`: complete proof development and typed statement audits.
- `logs/final/`: fresh compilation, independent `rocqchk`, and **every declared
  constant's** `Print Assumptions` record; `RESULT.json` records source hashes.
- `ASSUMPTIONS.txt`: logical and mathematical assumptions and their scope.
- `MATHEMATICAL_REVIEW.txt`: correspondence, dependencies, and independent review.
- `CHANGES.txt`: concise account of mathematical and editorial changes.
- `finite/`, `verification/`: the original finite-search evidence and coverage audit.
- `checks/`: supplementary SMT inputs, recorded outcomes, and executable diagnostics.
- `originals/`, `PROVENANCE.json`: source versions and prior failed verification runs.

## Reproduce the proofs

Requirements: Python 3 and Rocq 9.1.1 with its standard library, including
`rocq` and `rocqchk` on `PATH`. No external Rocq package or solver is needed.

```sh
python3 scripts/verify.py
```

This builds in `build/rocq` from copies of the `.v` sources, not old proof objects.
It compiles all four source files, checks the typed statement aliases, compares
the 92 original theorem statements with the failed baseline, generates a complete
assumption audit, and runs the standalone `rocqchk` on all modules.
The result is successful only when `logs/final/RESULT.json` contains
`"kernel_verified": true`. It rejects new axioms and proof bypasses, and allows
only the already-used `Stdlib.Logic.Classical_Prop.classic` in the assumption
output. Kernel checking remains the decisive test.

The current successful run audits 183 declarations: 130 are closed under the
global context; 53 depend only on classical excluded middle. The counterexample
is axiom-free. The rank theorem has explicit rank-order hypotheses; it is not
a construction of set-theoretic ordinals.

## Reproduce the PDF

Requirements: pdfLaTeX, BibTeX, and the LaTeX packages loaded by `lmcs.cls`.

```sh
python3 scripts/build_pdf.py
```

On macOS the script prefers `/Library/TeX/texbin`; elsewhere it uses `PATH`.
`PDFLATEX` and `BIBTEX` can specify executable paths. It performs the bibliography
pass and three LaTeX passes and rejects undefined references and overfull boxes.
The tested toolchain is TeX Live 2023. The supplied LMCS class is v0.93.
The preprint's unused first-page masthead is suppressed with a standard
`\thispagestyle{empty}`; the class itself is unchanged.

## Check computational evidence

```sh
python3 verification/verify_results.py
python3 checks/exhaustive_three_points.py
python3 checks/exhaustive_original_conditions.py
```

These commands use only Python's standard library. They reproduce the historical
coverage audit and small exhaustive diagnostics. The historical audit reports
150 nine-point roots and 572 ten-point terminal obligations. It checks recorded
outcomes, exit statuses, partitions, and exact regeneration of the final inputs.
It does **not** rerun the historical solver calls or verify SMT proof certificates.

Optional fresh SMT diagnostics, with Z3 installed:

```sh
python3 checks/check_folding_obligations.py
python3 checks/check_height_obligations.py
```

The scripts find a `z3` executable or its shared library. This machine had no
usable Z3 installation, so the supplement retains and clearly labels the
original Z3 4.13.3 diagnostic results. The original final search calls used
Z3 4.12.2.0 and can be replayed with:

```sh
z3 finite/completion/runs/v7_a3_baseline/input.smt2
z3 finite/completion/runs/v8_a4_baseline/input.smt2
```

The saved timeout may yield `unknown` on another system; that is never counted
as `unsat`. None of these computations is a premise of the Rocq termination
theorems.

## Archive

```sh
python3 scripts/package.py
python3 verification/verify_archive.py
```

The first command writes a deterministic source ZIP and a SHA-256 manifest.
Check integrity before rerunning tools that regenerate logs or diagnostics.
Rebuilds may change timings, PDF metadata, and compiled object bytes; the proof
source hashes and mathematical statements are the reproducibility anchors.

The original release remains separately cited at
<https://github.com/NachumDershowitz/4Relations/releases/tag/v1.0.0>.
The new supplement is cited as material accompanying this manuscript; it has not
been uploaded or submitted to a journal. When depositing it publicly, a persistent
identifier can replace that descriptive citation. The journal's author guidance is
at <https://lmcs.episciences.org/page/authors-latex-style>.
