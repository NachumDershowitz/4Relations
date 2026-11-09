# Theorem correspondence and its limits

The current paper, *Well-Founded Unions on Finite and Infinite Sets*, and its
authoritative general-development `THEOREM_MAP.md` were not recovered. Numbered
correspondences must be checked against their exact statements, not inferred
from an older manuscript or from matching topic names.

| Requested current-paper item | Correspondence status |
| --- | --- |
| Proposition 3.1 | Unresolved: current statement/map unavailable |
| Theorem 4.2 | Unresolved: current statement/map unavailable |
| Lemma 5.1 | Unresolved: current statement/map unavailable |
| Lemma 5.2 | Unresolved: current statement/map unavailable |
| Theorem 5.3 | Unresolved: current statement/map unavailable |
| Corollary 5.4 | Unresolved: current statement/map unavailable |
| Lemma 5.5 | Unresolved: current statement/map unavailable |
| Theorem 5.6 | Unresolved: current statement/map unavailable |
| Corollary 5.7 | Unresolved: current statement/map unavailable |
| Corollary 5.8 | Unresolved: current statement/map unavailable |

The following source-level map **is** supported by fresh compilation and the
typed aliases in `supplement-2026-10-20/rocq/Audit.v`. These are separate October
results; this table does not assign them to the current paper's numbers.

| Checked statement/topic | Source symbol |
| --- | --- |
| Countable infinite counterexample; four individual WF claims; interaction inclusions; explicit infinite chain and non-WF union | `FourRelationsCounterexample.v`: `FourRelations.FourRelationsCounterexample` |
| Finite carrier termination under WF A/B/C/D and P0/P1/Q2 | `FourRelations.v`: `finite_termination` |
| Finite acyclic formulation | `finite_acyclic_four_relations` |
| Finite set of immortal B-targets from A-minimal immortal points | `finite_escape_target_termination` |
| Finite targets for an explicitly given representative core | `Refinements.v`: `finite_representative_core_impossible` |
| Uniform finite B-height on A-minimal immortal points | `bounded_immortal_height_termination` |
| Uniform finite height of a representative core | `Refinements.v`: `bounded_representative_core_impossible` |
| Unbounded finite B-path lengths at minimal immortal points, under stronger P1 | `minimal_immortal_unbounded` |
| Pointwise height termination, under stronger P1 | `pointwise_minimal_height_termination`, `pointwise_height_termination` |
| Finite branching termination, under stronger P1 | `finitely_branching_termination` |
| Reachable failure of finite branching; local branching criterion | `Refinements.v`: `minimal_immortal_reaches_infinite_branching`, `locally_finitely_branching_termination` |
| Least attained abstract rank has a nonempty lower segment with no greatest member | `least_rank_is_nonzero_limit` |
| Specialized detour / transitive subunion facts | `detour_tail`, `transitive_subunion_wf` |
| Accessibility excludes an explicit infinite forward chain | `well_founded_has_no_infinite_chain` |

Unqualified symbols above are in `supplement-2026-10-20/rocq/FourRelations.v`.
The standalone counterexample also appears under `formal_proofs/`; both copies
are retained with their source structure and checked separately.

Conventions: `P x y` is a forward edge; `WF P` is accessibility for the converse
relation. Composition is left to right. `bad P x` is nonaccessibility;
`cut I P` restricts both endpoints. P0/P1/Q2 are expanded in the typed finite
statement audit. `P1_strong` removes the F-shortcut alternative from P1; it is a
genuine stronger premise for the pointwise/branching results. The full printed
types and assumption records are in `validation/.../october-proof-details/`.

Not formalized in this recovered package: the general published Jumping,
Tripartite, Detour, Preferential Jumping and Rearrangement theorems in their full
generality; set-theoretic ordinal construction and canonical-rank existence;
finite-search normal-form completeness, exact-size reduction, encoder correctness
and SMT proof certificates; the missing five-relation experiment and reset
example on an infinite domain. Specialized facts actually used by the October
proofs are proved internally. No claim is made about what the missing November
certificate development may formalize.
