(** Four Relations: the countable counterexample from Theorem 2 of
    Nachum Dershowitz, "Four Well-Founded Relations: A Sufficient Rule,
    an Infinite Counterexample, and a Finite Bound".

    Checked with Rocq 9.1.1 and its standard library.
    Compile: rocq compile FourRelationsCounterexample.v
    Independently check: rocq check FourRelationsCounterexample

    Composition is LEFT TO RIGHT.  The paper's well-foundedness concerns
    FORWARD chains; Rocq's [well_founded] therefore applies to the converse
    relation.  This convention is explicit in [WF] below.
*)

From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Lia
  Relations.Relation_Operators Wellfounded.Inclusion.

Module FourRelations.

Inductive vertex : Type :=
| num : nat -> vertex
| p : vertex
| q : vertex.

Definition relation := vertex -> vertex -> Prop.
Definition union (P Q : relation) : relation :=
  fun x y => P x y \/ Q x y.
Definition comp (P Q : relation) : relation :=
  fun x z => exists y, P x y /\ Q y z.
Definition included (P Q : relation) : Prop :=
  forall x y, P x y -> Q x y.
Definition star (P : relation) : relation := clos_refl_trans vertex P.
Definition plus (P : relation) : relation := clos_trans vertex P.
Definition WF (P : relation) : Prop :=
  well_founded (fun y x => P x y).
Definition infinite_chain (P : relation) (f : nat -> vertex) : Prop :=
  forall n, P (f n) (f (S n)).

(** These constructors specify exactly the edges in equation (1).
    There are no implicit reflexive or transitive edges. *)
Inductive A : relation :=
| A_even : forall k, A (num (2 * k)) q
| A_odd : forall k, A (num (2 * k + 1)) p.

Inductive B : relation :=
| B_even : forall k, B p (num (2 * k))
| B_odd : forall k, B q (num (2 * k + 1))
| B_down : forall n, B (num (S n)) (num n).

Inductive C : relation :=
| C_qp : C q p.

Inductive D : relation :=
| D_pq : D p q
| D_zero_p : D (num 0) p.

Definition F : relation := union C D.
Definition E : relation := union B F.
Definition R : relation := union A E.

(** The natural-number summand is infinite and the whole carrier is
    explicitly countable. *)
Theorem num_injective : forall n m, num n = num m -> n = m.
Proof. intros n m H; now injection H. Qed.

Definition enumerate (n : nat) : vertex :=
  match n with 0 => p | 1 => q | S (S k) => num k end.

Theorem enumerate_surjective : forall x, exists n, enumerate n = x.
Proof.
  intros [n | |].
  - exists (S (S n)); reflexivity.
  - exists 0; reflexivity.
  - exists 1; reflexivity.
Qed.

(** Individual well-foundedness.  Finite ranks suffice for A, C and D.
    B needs a separate proof: p and q have arbitrarily long finite
    B-descents, corresponding to ordinal rank omega in the paper. *)
Lemma WF_of_rank (P : relation) (rank : vertex -> nat) :
  (forall x y, P x y -> rank y < rank x) -> WF P.
Proof.
  intro H; unfold WF.
  apply (wf_incl vertex (fun y x => P x y) (ltof vertex rank)).
  - intros y x Hxy; exact (H x y Hxy).
  - apply well_founded_ltof.
Qed.

Definition rank_A (x : vertex) : nat :=
  match x with num _ => 1 | _ => 0 end.
Definition rank_C (x : vertex) : nat :=
  match x with q => 1 | _ => 0 end.
Definition rank_D (x : vertex) : nat :=
  match x with num 0 => 2 | p => 1 | _ => 0 end.

Theorem A_well_founded : WF A.
Proof.
  apply (WF_of_rank A rank_A).
  intros x y H; destruct H; cbn; lia.
Qed.

Lemma B_num_accessible : forall n, Acc (fun y x => B x y) (num n).
Proof.
  induction n as [|n IH]; constructor; intros y H.
  - inversion H.
  - inversion H; subst; exact IH.
Qed.

Theorem B_well_founded : WF B.
Proof.
  intros [n | |].
  - apply B_num_accessible.
  - constructor; intros y H; inversion H; subst; apply B_num_accessible.
  - constructor; intros y H; inversion H; subst; apply B_num_accessible.
Qed.

Theorem C_well_founded : WF C.
Proof.
  apply (WF_of_rank C rank_C).
  intros x y H; destruct H; cbn; lia.
Qed.

Theorem D_well_founded : WF D.
Proof.
  apply (WF_of_rank D rank_D).
  intros x y H; destruct H; cbn; lia.
Qed.

Theorem A_squared_empty : forall x y z, A x y -> A y z -> False.
Proof. intros x y z H; destruct H; intro H; inversion H. Qed.
Theorem C_squared_empty : forall x y z, C x y -> C y z -> False.
Proof. intros x y z H; destruct H; intro H; inversion H. Qed.
Theorem D_cubed_empty :
  forall w x y z, D w x -> D x y -> D y z -> False.
Proof.
  intros w x y z H1 H2 H3.
  inversion H1; subst; inversion H2; subst; inversion H3.
Qed.

(** The three stronger, endpoint-preserving interaction inclusions. *)
Theorem EA_in_AF_or_F : included (comp E A) (union (comp A F) F).
Proof.
  intros x z [y [Hxy Hyz]].
  destruct Hyz as [k | k].
  - destruct Hxy as [HB | [HC | HD]].
    + inversion HB; subst; try lia.
      * right; right; constructor.
      * left; exists p; split.
        -- change (A (num (S (2 * k))) p).
           replace (S (2 * k)) with (2 * k + 1) by lia; constructor.
        -- right; constructor.
    + inversion HC.
    + inversion HD.
  - destruct Hxy as [HB | [HC | HD]].
    + inversion HB; subst; try lia.
      * right; left; constructor.
      * left; exists q; split.
        -- change (A (num (S (2 * k + 1))) q).
           replace (S (2 * k + 1)) with (2 * S k) by lia; constructor.
        -- left; constructor.
    + inversion HC.
    + inversion HD.
Qed.

Theorem FB_in_BB_or_ABB :
  included (comp F B) (union (comp B B) (comp A (comp B B))).
Proof.
  intros x z [y [[HC | HD] HB]].
  - destruct HC. inversion HB; subst.
    left; exists (num (2 * k + 1)); split.
    + constructor.
    + replace (2 * k + 1) with (S (2 * k)) by lia; constructor.
  - destruct HD; inversion HB; subst.
    + left; exists (num (2 * S k)); split.
      * constructor.
      * replace (2 * S k) with (S (2 * k + 1)) by lia; constructor.
    + right; exists q; split.
      * exact (A_even 0).
      * exists (num (2 * k + 1)); split.
        -- constructor.
        -- replace (2 * k + 1) with (S (2 * k)) by lia; constructor.
Qed.

Theorem DC_in_BD : included (comp D C) (comp B D).
Proof.
  intros x z [y [HD HC]].
  destruct HD; inversion HC; subst.
  exists (num 0); split; [exact (B_even 0) | constructor].
Qed.

(** The conditions (P0), (P1), (Q2), with precisely the paper's closures. *)
Definition P0 : Prop := included (comp E A) (union (comp A (star R)) E).
Definition P1 : Prop :=
  included (comp F B) (union (comp A (star R)) (union (plus B) F)).
Definition Q2 : Prop :=
  included (comp D C) (union (comp B (star E)) (union (plus C) D)).

Lemma B_in_R : included B R.
Proof. intros x y H; right; left; exact H. Qed.
Lemma F_in_R : included F R.
Proof. intros x y H; right; right; exact H. Qed.
Lemma D_in_E : included D E.
Proof. intros x y H; right; right; exact H. Qed.

Theorem satisfies_P0 : P0.
Proof.
  intros x z H.
  destruct (EA_in_AF_or_F x z H) as [[y [HA HF]] | HF].
  - left; exists y; split; [exact HA |].
    apply rt_step; now apply F_in_R.
  - right; right; exact HF.
Qed.

Theorem satisfies_P1 : P1.
Proof.
  intros x z H.
  destruct (FB_in_BB_or_ABB x z H) as [[y [HB1 HB2]] | [y [HA HBB]]].
  - right; left; apply t_trans with y; now apply t_step.
  - left; exists y; split; [exact HA |].
    destruct HBB as [w [HB1 HB2]].
    apply rt_trans with w; apply rt_step; now apply B_in_R.
Qed.

Theorem satisfies_Q2 : Q2.
Proof.
  intros x z H.
  destruct (DC_in_BD x z H) as [y [HB HD]].
  left; exists y; split; [exact HB |].
  apply rt_step; now apply D_in_E.
Qed.

(** A concrete two-cycle and an explicit infinite forward R-chain. *)
Theorem R_two_cycle : R p q /\ R q p.
Proof.
  split.
  - right; right; right; constructor.
  - right; right; left; constructor.
Qed.

Fixpoint alternating (n : nat) : vertex :=
  match n with
  | 0 => p
  | S k => match alternating k with p => q | _ => p end
  end.

Lemma alternating_is_p_or_q : forall n, alternating n = p \/ alternating n = q.
Proof.
  induction n as [|n IH]; cbn; [now left |].
  destruct IH as [H | H]; rewrite H; [now right | now left].
Qed.

Theorem alternating_infinite_R_chain : infinite_chain R alternating.
Proof.
  intro n; cbn.
  destruct (alternating_is_p_or_q n) as [H | H]; rewrite H;
    apply R_two_cycle.
Qed.

(** Accessibility excludes infinite forward chains constructively. *)
Lemma accessible_no_infinite_chain (P : relation) (x : vertex) :
  Acc (fun y x => P x y) x ->
  forall f, f 0 = x -> infinite_chain P f -> False.
Proof.
  intro Hacc; induction Hacc as [x Hnext IH].
  intros f Hzero Hchain.
  assert (Hstep : P x (f 1)).
  { rewrite <- Hzero; exact (Hchain 0). }
  exact (IH (f 1) Hstep (fun n => f (S n)) eq_refl
    (fun n => Hchain (S n))).
Qed.

Theorem R_not_well_founded : ~ WF R.
Proof.
  intro Hwf.
  exact (accessible_no_infinite_chain R p (Hwf p) alternating
    eq_refl alternating_infinite_R_chain).
Qed.

(** Main result, bundling every claim of the counterexample. *)
Theorem FourRelationsCounterexample :
  WF A /\ WF B /\ WF C /\ WF D /\
  included (comp E A) (union (comp A F) F) /\
  included (comp F B) (union (comp B B) (comp A (comp B B))) /\
  included (comp D C) (comp B D) /\
  P0 /\ P1 /\ Q2 /\
  (R p q /\ R q p) /\
  infinite_chain R alternating /\ ~ WF R.
Proof.
  repeat apply conj.
  - exact A_well_founded.
  - exact B_well_founded.
  - exact C_well_founded.
  - exact D_well_founded.
  - exact EA_in_AF_or_F.
  - exact FB_in_BB_or_ABB.
  - exact DC_in_BD.
  - exact satisfies_P0.
  - exact satisfies_P1.
  - exact satisfies_Q2.
  - exact (proj1 R_two_cycle).
  - exact (proj2 R_two_cycle).
  - exact alternating_infinite_R_chain.
  - exact R_not_well_founded.
Qed.

End FourRelations.

Print Assumptions FourRelations.FourRelationsCounterexample.
