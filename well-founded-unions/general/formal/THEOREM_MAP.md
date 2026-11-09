# Manuscript to certificate map

| Manuscript result | Checked declarations |
|---|---|
| Theorem 4.2: finite acyclicity | `arbitrary_finite_acyclic_family_has_acyclic_union`, `arbitrary_finite_acyclic_family_termination` |
| Theorem 5.3: mixed internal-height criterion | `arbitrary_family_mixed_height_termination` |
| Corollary 5.4: finite branching | `finitely_branching_internal_relations_terminate`, `arbitrary_finite_family_branching_termination` |
| Lemma 5.5: successor-layer elimination | `successor_ordinal_layer_elimination` |
| Theorem 5.6: minimum layer rank | `minimum_rank_stratum_has_representatives`, `minimum_layer_rank_is_not_a_successor`, `zero_minimum_rank_clears_the_stage` |
| Corollary 5.7: nonzero limit-layer obstruction | `arbitrary_family_limit_rank_obstruction` |
| Corollary 5.8: mixed height/ordinal criterion | `arbitrary_family_mixed_height_and_ordinal_termination` |
| All internal stages use the ordinal alternative | `zero_or_successor_internal_ranks_imply_termination` |
| Accessibility convention and immortal set | `immortal_iff_nonaccessible`, `well_founded_excludes_forward_chain` |

Supporting checked lemmata include:

- `family_union_transitive_subrelations_well_founded`;
- `successor_layer_removal_preserves_representatives`;
- `uniform_height_representative_elimination` and `pointwise_height_representative_elimination`;
- `serial_domain_with_eliminable_internal_stages_impossible`;
- `well_ordered_ranks_attain_a_minimum`;
- `successor_rank_has_predecessor_rank_successor`;
- `path_into_predecessor_rank_is_one_edge`;
- `final_two_relations_no_branching_needed`.

The four-relation minimum-rank corollary is the i=1 specialization of the
checked general layer result together with the final-pair argument. It is
proved in the manuscript, not separately exported under a four-relation name.

The explicit infinite counterexample and the construction of set-theoretic
ordinals are not covered by this certificate. The ordinal results are checked
at the stated abstract well-order/canonical-rank interface.
