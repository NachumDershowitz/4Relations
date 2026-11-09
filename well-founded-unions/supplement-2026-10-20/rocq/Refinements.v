(** Local refinements of the finite-target, height, and branching criteria.
    No statement in FourRelations.v is changed. *)
From Stdlib Require Import Classical List Arith.
From FourRelations Require Import FourRelations.
Import ListNotations.
Unset Implicit Arguments.

Section Cores.
Context {X : Type}.
Variables A B C D : rel X.
Let I := bad (R0 A B C D).
Let a := cut I A.
Let b := cut I B.
Let c := cut I C.
Let d := cut I D.
Variable S : X -> Prop.
Hypothesis Sub : forall x, S x -> minimal_immortal A B C D x.
Hypothesis Rep : forall z, I z -> exists t, S t /\
  forall x, S x -> E0 B C D x z -> E0 B C D x t.

Lemma core_representatives : representatives b c d I S.
Proof.
  intros z Iz. destruct (Rep z Iz) as [t [St Ht]].
  exists t; split; [exact St |].
  intros x Sx Exz.
  apply (cut_E_equiv A B C D) in Exz.
  apply (cut_E_equiv A B C D).
  split; [exact (proj1 (Sub x Sx)) |].
  split; [apply Ht; [exact Sx |exact (proj1 (proj2 Exz))] |].
  exact (proj1 (Sub t St)).
Qed.

Theorem finite_representative_core_impossible :
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1 A B C D -> Q2 B C D ->
  (exists x, S x) ->
  (exists l : list X, forall x z, S x -> B x z -> I z -> In z l) ->
  False.
Proof.
  intros WA WB WC WD H0 H1 H2 NE [l Cover].
  eapply (finite_active_impossible a b c d I).
  - apply cut_well_founded; exact WB.
  - apply cut_well_founded; exact WC.
  - apply cut_well_founded; exact WD.
  - apply P1_restrict; exact H1.
  - apply Q2_restrict; exact H2.
  - exact (cut_domain A B C D).
  - exact (cut_serial A B C D).
  - apply Nat.le_refl with (n := length l).
  - exact NE.
  - intros x Sx; apply cut_minimal_equiv; apply Sub; exact Sx.
  - exact core_representatives.
  - intros z [x [Sx [_ [Bxz Iz]]]]. eapply Cover; eauto.
Qed.

Theorem bounded_representative_core_impossible :
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1 A B C D -> Q2 B C D ->
  (exists x, S x) ->
  (exists h, forall x, S x -> height_le b h x) -> False.
Proof.
  intros WA WB WC WD H0 H1 H2 NE [h Bound].
  eapply (bounded_representatives_impossible a b c d I).
  - apply cut_well_founded; exact WC.
  - apply cut_well_founded; exact WD.
  - apply P1_restrict; exact H1.
  - apply Q2_restrict; exact H2.
  - exact (cut_domain A B C D).
  - exact (cut_serial A B C D).
  - exact NE.
  - intros x Sx; apply cut_minimal_equiv; apply Sub; exact Sx.
  - exact core_representatives.
  - exact Bound.
Qed.
End Cores.

Section LocalBranching.
Context {X : Type}.

Lemma long_reachable_cut (P : rel X) a :
  forall n x, star P a x -> long P n x ->
  long (cut (star P a) P) n x.
Proof.
  induction n as [|n IH]; intros x Reach L.
  - exact Logic.I.
  - destruct L as [y [Pxy Ly]].
    assert (Ry : star P a y).
    { eapply star_trans; [exact Reach |apply star_one; exact Pxy]. }
    exists y; split.
    + split; [exact Reach |split; assumption].
    + apply IH; assumption.
Qed.

Lemma reachable_finitely_branching_height (P : rel X) a :
  WF P ->
  (forall x, star P a x ->
    exists l : list X, forall y, P x y -> In y l) ->
  exists h, height_le P h a.
Proof.
  intros W Branch.
  set (Q := cut (star P a) P).
  assert (WQ : WF Q).
  { eapply wf_mono; [|exact W]. intros x y [_ [H _]]; exact H. }
  assert (BQ : finitely_branching Q).
  { intro x; destruct (classic (star P a x)) as [Rx |Nx].
    - destruct (Branch x Rx) as [l Cover]. exists l.
      intros y [_ [Pxy _]]; apply Cover; exact Pxy.
    - exists []; intros y [Rx _]; contradiction. }
  destruct (finitely_branching_wf_height Q WQ BQ a) as [h Hh].
  exists h; intro L; apply Hh.
  apply long_reachable_cut; [apply star_refl |exact L].
Qed.

Theorem minimal_immortal_reaches_infinite_branching
    (A B C D : rel X) :
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1_strong A B C D -> Q2 B C D ->
  forall x, minimal_immortal A B C D x ->
  exists y, star (cut (bad (R0 A B C D)) B) x y /\
    ~ (exists l : list X, forall z,
         cut (bad (R0 A B C D)) B y z -> In z l).
Proof.
  intros WA WB WC WD H0 Hs H2 x Mx.
  apply NNPP; intro None.
  assert (Branch : forall y,
      star (cut (bad (R0 A B C D)) B) x y ->
      exists l : list X, forall z,
        cut (bad (R0 A B C D)) B y z -> In z l).
  { intros y Ry; apply NNPP; intro Ny; apply None; exists y; auto. }
  assert (Wb : WF (cut (bad (R0 A B C D)) B)).
  { eapply wf_mono; [|exact WB]. intros u v [_ [H _]]; exact H. }
  destruct (reachable_finitely_branching_height _ x Wb Branch) as [h Hh].
  apply Hh. eapply minimal_immortal_unbounded; eauto.
Qed.

Corollary locally_finitely_branching_termination
    (A B C D : rel X) :
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1_strong A B C D -> Q2 B C D ->
  (forall x, minimal_immortal A B C D x ->
    forall y, star (cut (bad (R0 A B C D)) B) x y ->
      exists l : list X, forall z,
        cut (bad (R0 A B C D)) B y z -> In z l) ->
  WF (R0 A B C D).
Proof.
  intros WA WB WC WD H0 Hs H2 Branch.
  apply pointwise_minimal_height_termination; try assumption.
  intros x Mx; apply reachable_finitely_branching_height.
  - eapply wf_mono; [|exact WB]. intros u v [_ [H _]]; exact H.
  - apply Branch; exact Mx.
Qed.
End LocalBranching.
