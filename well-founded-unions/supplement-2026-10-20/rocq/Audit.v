(** Compile this file only after FourRelations.v.  These typed aliases fix the
    principal theorem statements independently of the proof-script headings. *)
From Stdlib Require Import List.
From FourRelations Require Import FourRelations.
From FourRelations Require Import Refinements.
Unset Implicit Arguments.

Definition audited_core_finite_statement :
  forall (X : Type) (A B C D : rel X) (S : X -> Prop),
  (forall x, S x -> minimal_immortal A B C D x) ->
  (forall z, bad (R0 A B C D) z -> exists t, S t /\
    forall x, S x -> E0 B C D x z -> E0 B C D x t) ->
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1 A B C D -> Q2 B C D ->
  (exists x, S x) ->
  (exists l : list X, forall x z,
    S x -> B x z -> bad (R0 A B C D) z -> In z l) -> False
  := @finite_representative_core_impossible.

Definition audited_core_height_statement :
  forall (X : Type) (A B C D : rel X) (S : X -> Prop),
  (forall x, S x -> minimal_immortal A B C D x) ->
  (forall z, bad (R0 A B C D) z -> exists t, S t /\
    forall x, S x -> E0 B C D x z -> E0 B C D x t) ->
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1 A B C D -> Q2 B C D ->
  (exists x, S x) ->
  (exists h, forall x, S x ->
    height_le (cut (bad (R0 A B C D)) B) h x) -> False
  := @bounded_representative_core_impossible.

Definition audited_local_branching_statement :
  forall (X : Type) (A B C D : rel X),
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1_strong A B C D -> Q2 B C D ->
  forall x, minimal_immortal A B C D x ->
  exists y, star (cut (bad (R0 A B C D)) B) x y /\
    ~ (exists l : list X, forall z,
      cut (bad (R0 A B C D)) B y z -> In z l)
  := @minimal_immortal_reaches_infinite_branching.

Definition audited_finite_statement :
  forall (X : Type) (A B C D : rel X),
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1 A B C D -> Q2 B C D ->
  (exists l : list X, forall x, In x l) -> WF (R0 A B C D)
  := @finite_termination.

Definition audited_finite_image_statement :
  forall (X : Type) (A B C D : rel X),
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1 A B C D -> Q2 B C D ->
  (exists l : list X, forall x z,
    minimal_immortal A B C D x -> B x z ->
    bad (R0 A B C D) z -> In z l) -> WF (R0 A B C D)
  := @finite_escape_target_termination.

Definition audited_uniform_height_statement :
  forall (X : Type) (A B C D : rel X),
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1 A B C D -> Q2 B C D ->
  (exists h, forall x, minimal_immortal A B C D x ->
    height_le (cut (bad (R0 A B C D)) B) h x) -> WF (R0 A B C D)
  := @bounded_immortal_height_termination.

Definition audited_pointwise_statement :
  forall (X : Type) (A B C D : rel X),
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1_strong A B C D -> Q2 B C D ->
  (forall x, exists h, height_le B h x) -> WF (R0 A B C D)
  := @pointwise_height_termination.

Definition audited_unbounded_minimal_points_statement :
  forall (X : Type) (A B C D : rel X),
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1_strong A B C D -> Q2 B C D ->
  forall x, minimal_immortal A B C D x ->
  forall n, long (cut (bad (R0 A B C D)) B) n x
  := @minimal_immortal_unbounded.

Definition audited_finite_branching_statement :
  forall (X : Type) (A B C D : rel X),
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1_strong A B C D -> Q2 B C D ->
  finitely_branching B -> WF (R0 A B C D)
  := @finitely_branching_termination.

(** This alias expands the union, well-foundedness convention, composition,
    and every alternative in all three interaction conditions.  It does not
    reuse P0, P1, Q2, R0, E0, F0, plus, or WF from the proof file.  Only the
    explicitly inductive finite-path relation [star] is shared. *)
Definition audited_expanded_finite_statement :
  forall (X : Type) (A B C D : X -> X -> Prop),
  well_founded (fun y x => A x y) ->
  well_founded (fun y x => B x y) ->
  well_founded (fun y x => C x y) ->
  well_founded (fun y x => D x y) ->
  (forall x y z, (B x y \/ C x y \/ D x y) -> A y z ->
    (exists u, A x u /\
      star (fun s t => A s t \/ B s t \/ C s t \/ D s t) u z) \/
    (B x z \/ C x z \/ D x z)) ->
  (forall x y z, (C x y \/ D x y) -> B y z ->
    (exists u, A x u /\
      star (fun s t => A s t \/ B s t \/ C s t \/ D s t) u z) \/
    (exists u, B x u /\ star B u z) \/ (C x z \/ D x z)) ->
  (forall x y z, D x y -> C y z ->
    (exists u, B x u /\
      star (fun s t => B s t \/ C s t \/ D s t) u z) \/
    (exists u, C x u /\ star C u z) \/ D x z) ->
  (exists l : list X, forall x, In x l) ->
  well_founded (fun y x => A x y \/ B x y \/ C x y \/ D x y)
  := @finite_termination.

Check audited_expanded_finite_statement.
Print Assumptions audited_expanded_finite_statement.
Redirect "assumptions_audited_expanded_finite_statement"
  Print Assumptions audited_expanded_finite_statement.

Check audited_finite_statement.
Print Assumptions audited_finite_statement.
Redirect "assumptions_audited_finite_statement" Print Assumptions audited_finite_statement.
Check audited_finite_image_statement.
Print Assumptions audited_finite_image_statement.
Redirect "assumptions_audited_finite_image_statement" Print Assumptions audited_finite_image_statement.
Check audited_uniform_height_statement.
Print Assumptions audited_uniform_height_statement.
Redirect "assumptions_audited_uniform_height_statement" Print Assumptions audited_uniform_height_statement.
Check audited_pointwise_statement.
Print Assumptions audited_pointwise_statement.
Redirect "assumptions_audited_pointwise_statement" Print Assumptions audited_pointwise_statement.
Check audited_unbounded_minimal_points_statement.
Print Assumptions audited_unbounded_minimal_points_statement.
Redirect "assumptions_audited_unbounded_minimal_points_statement" Print Assumptions audited_unbounded_minimal_points_statement.
Check audited_finite_branching_statement.
Print Assumptions audited_finite_branching_statement.
Redirect "assumptions_audited_finite_branching_statement" Print Assumptions audited_finite_branching_statement.
Check least_rank_is_nonzero_limit.
Print Assumptions least_rank_is_nonzero_limit.
Redirect "assumptions_least_rank_is_nonzero_limit" Print Assumptions least_rank_is_nonzero_limit.
Check finite_acyclic_four_relations.
Print Assumptions finite_acyclic_four_relations.
Redirect "assumptions_finite_acyclic_four_relations" Print Assumptions finite_acyclic_four_relations.
Check detour_tail.
Print Assumptions detour_tail.
Redirect "assumptions_detour_tail" Print Assumptions detour_tail.
Check transitive_subunion_wf.
Print Assumptions transitive_subunion_wf.
Redirect "assumptions_transitive_subunion_wf" Print Assumptions transitive_subunion_wf.
Check well_founded_has_no_infinite_chain.
Print Assumptions well_founded_has_no_infinite_chain.
Redirect "assumptions_well_founded_has_no_infinite_chain" Print Assumptions well_founded_has_no_infinite_chain.
