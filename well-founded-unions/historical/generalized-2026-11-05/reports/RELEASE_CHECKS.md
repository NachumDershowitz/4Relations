# Manuscript and formal-proof release checks

The manuscript was rebuilt with pdfLaTeX using the supplied, hash-checked bibliography output. It contains 12 pages. All references and citations resolve. There are no overfull horizontal boxes. Two inherited first-page LMCS vertical-box warnings remain; the rendered pages have no clipping or overlaps. All pages were inspected, and the conclusion and both references now fit on the final page.

Finite-domain conclusions explicitly state acyclicity. The arbitrary-domain mixed-height, finite-branching and ordinal criteria state well-foundedness. All symbolic quantifiers retain dots and restriction harpoons retain the supplied spacing.

The supplied combined certificate passed both standalone checker implementations, 18 exact-statement audits, and 30 regression tests. It contains 7,583 inference steps and 114 closed named theorems. Byte-for-byte regeneration of the certificate and Rocq proof-term export succeeded.

The ordinal results are proved at an explicit abstract well-order and canonical-rank interface. The ambient ordinal construction and rank assignment are not constructed in this certificate. The infinite counterexample is not part of this certificate.

A separate Rocq attempt exited 127 at compiler detection. No Rocq compilation or established-kernel acceptance is claimed. The checkers are project-specific implementations; their correctness remains part of the trust base.

The supplement's finite and SMT programs are supplied as independent diagnostics. They were not used as premises for the general proofs and were not rerun in this release.
