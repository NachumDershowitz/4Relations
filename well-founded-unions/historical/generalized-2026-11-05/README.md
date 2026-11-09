# Well-Founded Unions on Finite and Infinite Sets

The manuscript and formal certificate establish:

- Acyclicity of the union of any finite ordered family of acyclic relations on a finite domain, under the generalized interaction conditions.
- Well-foundedness on arbitrary domains under mixed uniform and pointwise internal-height conditions, and under finite branching with shortened internal conditions.
- Removal of a successor-ordinal top layer, the minimum-layer rank theorem, and the nonzero limit-layer obstruction for arbitrary finite families.
- A mixed criterion permitting uniform finite heights with all shortcuts at some indices, and canonical zero-or-successor ranks at first-relation-minimal immortal points with shortened conditions at other indices.

Read `manuscript/WellFoundedUnions.pdf`. All mathematical statements and notation are also in the LaTeX source and `formal/STATEMENT.md`.

## Reproduce the formal checks

```sh
sh check.sh
```

Only Python 3 is needed. The script checks source hashes, independently replays the certificate in two implementations, audits 18 exact statements, runs 30 regression tests, and regenerates the certificate and explicit proof terms byte for byte. The successful run is recorded in `formal/CHECKED.json` and `formal/logs/`.

The checkers are project-specific implementations of classical higher-order natural deduction. Their correctness is part of the trust base. They are not established proof-assistant kernels. No Rocq compilation or Rocq kernel success is claimed. `formal/check_rocq.sh` separately attempts that validation, using an existing Rocq 9 installation, and never writes a success marker on failure.

## Rebuild the paper

```sh
sh build.sh
```

The bibliography output is supplied, with hashes, for systems without BibTeX. The bibliography has two research references; no archival self-citation is required. The source retains colored relations, tight restriction-harpoon spacing, and dots after quantified variable lists.

## Scope

`formal/THEOREM_MAP.md` maps the manuscript statements to checked declarations. The ordinal proofs assume an explicitly supplied well-order and the canonical-rank equations, as hypotheses of general theorems. They do not construct a set-theoretic ordinal library. The height proofs encode finite iteration of successor-preimage closure, which is the path-length height convention in the paper. A checked bridge identifies the maximal serial subset in the certificate with the nonaccessible points used in the manuscript.

The explicit infinite counterexample is proved in the paper, but is not one of the theorems in the certificate. Supplementary finite searches are independent of all general proofs.
