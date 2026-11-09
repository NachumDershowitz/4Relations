# Theorem map to the supplied current paper

Checked against the theorem statements and labels in `WellFoundedUnions/WFU.tex`
inside the supplied `WellFoundedUnions_clean_revision_source.zip`, together with
the original general-development map and independent exact-statement audits.
The manuscript is read only for correspondence and is not distributed here.

| Current paper result | Formal coverage |
| --- | --- |
| Proposition 3.1: infinite four-relation counterexample | `formal_proofs/FourRelationsCounterexample.v`: `FourRelations.FourRelationsCounterexample`; `num_injective` and `enumerate_surjective` establish the carrier facts |
| Theorem 4.2: finite acyclicity | `arbitrary_finite_acyclic_family_has_acyclic_union`; `arbitrary_finite_acyclic_family_termination` |
| Lemma 5.1: transitive subrelations | `family_union_transitive_subrelations_well_founded` |
| Lemma 5.2: height elimination | `uniform_height_representative_elimination`, with the family transitive-subrelation and restriction results; its pointwise companion is `pointwise_height_representative_elimination` |
| Theorem 5.3: mixed height criteria | `arbitrary_family_mixed_height_termination` |
| Corollary 5.4: finite branching | `finitely_branching_internal_relations_terminate`; `arbitrary_finite_family_branching_termination` |
| Lemma 5.5: successor-layer elimination | `successor_ordinal_layer_elimination` |
| Theorem 5.6: minimum layer rank | `minimum_rank_stratum_has_representatives`; `minimum_layer_rank_is_not_a_successor`; `zero_minimum_rank_clears_the_stage` |
| Corollary 5.7: nonzero limit-layer obstruction | `arbitrary_family_limit_rank_obstruction` |
| Corollary 5.8: mixed height/ordinal criterion | `arbitrary_family_mixed_height_and_ordinal_termination` |

Unqualified symbols are in `general/formal/proof.json` and exported under the
same names in `general/formal/WellFoundedUnionsProofTerms.v`. Each named theorem
has no undischarged certificate hypotheses. Its explicit mathematical premises
remain universally quantified in its statement. Fresh Rocq acceptance is recorded
in `validation/2026-11-09-complete/general-details/`.

Additional coverage includes `zero_or_successor_internal_ranks_imply_termination`,
`immortal_iff_nonaccessible`, `well_founded_excludes_forward_chain`, finite
reachability, representative elimination, and the final two-relation stage.
The independent audit modules reconstruct 18 exact statements without importing
proof generators. The full 114-theorem inventory is in the certificate and the
fresh per-theorem assumption audit.

Composition is left to right. Well-foundedness uses accessibility for forward
steps (the converse of Rocq's predecessor relation). The maximal serial set in
the certificate is proved equivalent to nonaccessibility. Height is encoded by
finite iterations of successor-preimage closure from the empty predicate. A
uniform bound shares one iterate; a pointwise bound selects an iterate after
the point is quantified. Intermediate stages may mix the alternatives. Shortened
conditions genuinely remove the tail-shortcut alternative; these stronger
premises are not interchangeable with the full conditions.

Ordinal results assume an explicit strict total order whose converse is
well-founded, rank decrease on edges, and the least-strict-upper-bound law:
if every B-successor has rank below alpha, the source rank is at most alpha.
Zero has no predecessor; a successor has an immediate predecessor with no
intermediate value. The checked results use this interface. They do not construct
set-theoretic ordinals or canonical rank assignments.

Not claimed as separately formalized here: the cited published Jumping, Tripartite,
Detour, Preferential Jumping and Rearrangement results in full generality; the
construction of ordinals/ranks; finite-search normalization and encoder
correctness; independent proof-certificate checking of saved SMT UNSAT answers;
and the general infinite reset-system argument. Its executable check is bounded.
The four-relation least-rank corollary is a specialization of the general layer
result plus final-pair argument, not a separate general-certificate export under
a four-relation name. The older October Rocq development, including its local
branching refinements, remains separately identified in `supplement-2026-10-20/`.
