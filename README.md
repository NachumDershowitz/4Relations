# Well-founded unions: formal proofs and tests

This branch contains formal proof sources, test programs, saved experimental
evidence, and verification records. Paper files are excluded from the current
branch. Earlier commits and releases remain unchanged and may retain them.

The recovered November preparation is in
[well-founded-unions/](well-founded-unions/README.md). Its
[status](well-founded-unions/STATUS.md) explicitly records missing source
components; it is not a complete recovery of the general certificate development.

| Path | Contents |
| --- | --- |
| `well-founded-unions/` | Recovered October Rocq development, counterexample, tests, evidence, fresh logs, theorem-map limitations, and checksums |
| `formal_proofs/` | Original standalone infinite-counterexample source and checker |
| `finite/` | Original encoders, saved result tables, and final SMT inputs/outputs |
| `verification/` | Root manifest and saved finite-coverage verification |
| `MANIFEST.json` | SHA-256 hashes and sizes for the current tracked source package |

## Verification

With Python 3 and Rocq 9.1.1 (`rocq` and `rocqchk`) installed:

```sh
python3 verification/verify_archive.py
python3 well-founded-unions/verify.py --scope recovered
```

The first command checks current package integrity and the historical finite
coverage audit. The second compiles and independently kernel-checks the recovered
proofs, audits assumptions and statement preservation, and reruns the exhaustive
small tests. Add `--with-smt` with Z3 installed to repeat the local SMT diagnostics.
The default full-scope command deliberately exits 2 until missing evidence is
recovered and integrated; see the detailed status before citing coverage.

Freshly checked results include the axiom-free infinite counterexample and the
separate October development's 183 declarations (130 closed; 53 using only
classical excluded middle). The saved-result audit checks 150 nine-point cases
plus 572 ten-point terminal obligations. It regenerates the final two inputs
exactly, but does not rerun historical SMT searches or check Z3 proof certificates.
Fresh local SMT checks are separate evidence. Full logs and experimental records
are included under `well-founded-unions/validation/`.

## Publication scope

Only proofs, tests, supporting evidence, and documentation belong in this
branch's publication package. `paper/` is ignored to prevent accidental additions.
No source history or existing release has been rewritten. No release of this
recovery has been published; the user's final approval is required.

The November general certificate and independent replay checkers, the original
five-relation experiment, the reset check, and an authoritative current-paper
numbering map remain unavailable. The recovered October proof is explicitly
identified as a distinct development.

Use [CITATION.cff](CITATION.cff) for repository attribution and identify the exact
commit or a verified release when citing checked artifacts.
