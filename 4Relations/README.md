# Four Relations: companion archive

Companion materials for Nachum Dershowitz, **Four Well-Founded Relations: A Sufficient Rule, an Infinite Counterexample, and a Finite Bound**.

- [Read the paper](paper/Four_Well_Founded_Relations.pdf)
- [Rocq formal proof](formal_proofs/FourRelationsCounterexample.v)
- [Finite-search verification record](verification/finite_results.json)
- [Version 1.0.0](https://github.com/NachumDershowitz/4Relations/releases/tag/v1.0.0)

The paper gives a countably infinite counterexample to the proposed replacement condition: all four relations are individually well-founded, but their union has a two-cycle. The concrete counterexample is formally proved in Rocq. A separate computer-assisted finite search excludes counterexamples on at most ten points.

## Contents

| Path | Contents |
| --- | --- |
| `paper/` | Current PDF, editable LaTeX, full-width vector figure, build script |
| `formal_proofs/` | Standalone `.v` proof, compilation/kernel-check script, verification records |
| `finite/computation/` | Original Boolean and bit-vector encoders and saved result tables |
| `finite/completion/` | Original coverage audit; exact inputs, outputs, and metadata for the two final UNSAT runs |
| `verification/` | Portable archive integrity and finite-coverage checks and their recorded output |
| `MANIFEST.json` | SHA-256 hashes and sizes of the distributed files |
| `CITATION.cff` | Citation metadata for the archive |

## Check the archive and finite coverage

Python 3's standard library is sufficient:

```sh
python3 verification/verify_archive.py
```

This checks every distributed file against the manifest and reruns the finite-coverage audit. To run the coverage audit alone:

```sh
python3 verification/verify_results.py
```

The expected result is `PASS`, with:

- 150 nine-point root cases, all recorded UNSAT;
- 316 ten-point roots: 312 close directly and four require refinement;
- 260 refinements, of which 240 close directly;
- 20 residual cases: 18 close in the residual table and two in the final whole-branch runs;
- **572 terminal ten-point obligations**, with none unresolved.

The ten-point total consists of 280 cases with cycle length at least three and 292 length-two leaves (`32 + 240 + 18 + 2`). The exact-size reduction in the paper covers all smaller cardinalities.

The audit checks exact case coverage, recorded statuses and exit codes, and byte-for-byte regeneration and hashes of the two final SMT inputs. It runs the original audit on temporary copies, preserving the archived evidence. It does not rerun the solver or independently check Z3 proof certificates. Earlier terminal outcomes are supplied as result tables; the final two runs additionally include exact SMT-LIB inputs and raw solver output.

`finite/computation/escc_v7w3F_results.tsv` records an earlier incomplete component-mask exploration. It is retained as provenance and contributes no leaves to the completed cover. The two whole-branch UNSAT results make further component splitting unnecessary.

## Check the formal proof

With Rocq installed:

```sh
sh formal_proofs/check.sh
```

Verified with **Rocq 9.1.1**, compiled with OCaml 5.4.1. The script compiles the source and runs the independent `rocq check` verifier in a temporary directory. The combined theorem reports:

```text
Closed under the global context
```

It proves all four individual well-foundedness claims, the three stronger interaction inclusions, conditions (P0), (P1), (Q2), the two-cycle, an explicit infinite alternating chain, and the failure of forward well-foundedness of the union. It has no axiomatic dependencies or unfinished proofs and imports only Stdlib. Its `WF` definition uses the converse of Rocq's predecessor relation so that it expresses forward termination, as in the paper.

The source retains internal abbreviations `E` and `F`; the paper writes their unions explicitly. The Rocq development proves the concrete infinite counterexample, not the finite SMT exclusion theorem.

## Rerun the final SMT calls

The recorded runs used Z3 **4.12.2.0**, seed zero, the default solver, and a 300-second timeout. They returned UNSAT in 154.338 and 119.612 seconds on the recorded machine. With a compatible `z3` executable:

```sh
z3 finite/completion/runs/v7_a3_baseline/input.smt2
z3 finite/completion/runs/v8_a4_baseline/input.smt2
```

The saved timeout is part of each input; a different machine or solver version can time out. `unknown` is not an UNSAT result.

The archived encoders and original runner remain byte-for-byte copies of the previous research package. Their original direct entry points contain machine-specific library defaults. Replaying the saved `.smt2` inputs as above avoids those defaults. Machine paths in run metadata identify the original environment; no Z3 or other runtime binary is redistributed.

## Rebuild the paper

With a TeX distribution containing pdfLaTeX and TikZ:

```sh
cd paper
sh build.sh
```

The script runs LaTeX twice and writes `paper/Four_Well_Founded_Relations.pdf`. On macOS it prefers MacTeX's executable if present; `PDFLATEX` can specify another executable.

## Provenance and citation

The finite encoders, result tables, and completed whole-branch records come from the September 2026 research package. This release adds the Rocq formalization, the revised note, and a portable wrapper that also audits the nine-point cover. Earlier drafts' claim of 256 completed component-mask leaves is replaced by the complete whole-branch evidence actually distributed here.

Use the citation metadata in `CITATION.cff` and cite the versioned release rather than an evolving working copy. The repository is [NachumDershowitz/4Relations](https://github.com/NachumDershowitz/4Relations).
