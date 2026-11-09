(** Four Relations: finite-image and finite-height termination theorems.

    Forward convention: [A x y] is an edge from x to y.
    [WF A] is standard accessibility-based well-foundedness of the converse.

    This development uses classical propositional logic, but not a choice axiom.
    The representatives used below are existential, not a selected function.

    Reproduce compilation, the full assumption audit, and independent rocqchk
    with [python3 scripts/verify.py] from the archive root. The resulting
    logs/final/RESULT.json records the checked source hashes and outcome.
*)
From Stdlib Require Import Classical List Arith Lia Bool.
Import ListNotations.
Unset Implicit Arguments.

Definition rel (X : Type) := X -> X -> Prop.
Definition cup {X} (P Q : rel X) : rel X := fun x y => P x y \/ Q x y.
Definition flip {X} (P : rel X) : rel X := fun x y => P y x.
Definition WF {X} (P : rel X) := well_founded (flip P).
Definition normal {X} (P : rel X) x := forall y, ~ P x y.
Definition bad {X} (P : rel X) x := ~ Acc (flip P) x.
Definition cut {X} (J : X -> Prop) (P : rel X) : rel X :=
  fun x y => J x /\ P x y /\ J y.

Inductive star {X} (P : rel X) : rel X :=
| star_refl : forall x, star P x x
| star_cons : forall x y z, P x y -> star P y z -> star P x z.
Arguments star_refl {X P} x.
Arguments star_cons {X P x y z} _ _.
Definition plus {X} (P : rel X) x z :=
  exists y, P x y /\ star P y z.

Section Basic.
Context {X : Type}.

Lemma star_one (P : rel X) x y : P x y -> star P x y.
Proof. intro H; exact (star_cons H (star_refl y)). Qed.
Lemma star_trans (P : rel X) x y z :
  star P x y -> star P y z -> star P x z.
Proof. intros H K; induction H; eauto using star_cons. Qed.
Lemma star_mono (P Q : rel X) :
  (forall x y, P x y -> Q x y) ->
  forall x y, star P x y -> star Q x y.
Proof. intros H x y K; induction K; eauto using star_refl, star_cons. Qed.
Lemma plus_one (P : rel X) x y : P x y -> plus P x y.
Proof. intro H; exists y; split; auto using star_refl. Qed.
Lemma plus_star (P : rel X) x y : plus P x y -> star P x y.
Proof. intros [z [H K]]; exact (star_cons H K). Qed.
Lemma plus_mono (P Q : rel X) :
  (forall x y, P x y -> Q x y) ->
  forall x y, plus P x y -> plus Q x y.
Proof.
  intros H x y [z [K L]]; exists z; split; eauto using star_mono.
Qed.
Lemma plus_trans (P : rel X) x y z :
  plus P x y -> plus P y z -> plus P x z.
Proof.
  intros [u [H K]] L; exists u; split; auto.
  eapply star_trans; [exact K | apply plus_star; exact L].
Qed.
Lemma plus_split (P : rel X) x z :
  plus P x z -> P x z \/ exists y, P x y /\ plus P y z.
Proof.
  intros [y [H K]]; destruct K as [y | y u z K L].
  - left; exact H.
  - right; exists y; split; auto. exists u; auto.
Qed.

Lemma acc_mono (P Q : rel X)
    (H : forall x y, P x y -> Q x y) x :
  Acc (flip Q) x -> Acc (flip P) x.
Proof.
  intro K; induction K as [x K IH].
  constructor; intros y L; apply IH; apply H; exact L.
Qed.
Lemma wf_mono (P Q : rel X) :
  (forall x y, P x y -> Q x y) -> WF Q -> WF P.
Proof. intros H K x; eapply acc_mono; eauto. Qed.
Lemma acc_star (P Q : rel X)
    (H : forall x y, P x y -> Q x y) x y :
  star P x y -> Acc (flip Q) x -> Acc (flip Q) y.
Proof.
  intro K; induction K as [x | x y z K L IH]; intro A.
  - exact A.
  - apply IH. destruct A as [A]. apply A. apply H. exact K.
Qed.
Lemma wf_plus (P : rel X) : WF P -> WF (plus P).
Proof.
  intros W x. induction (W x) as [x K IH].
  constructor; intros y [z [H L]].
  eapply (acc_star P (plus P)).
  - intros a b E; apply plus_one; exact E.
  - exact L.
  - apply IH; exact H.
Qed.

Lemma wf_minimum (P : rel X) (U : X -> Prop) :
  WF P -> (exists x, U x) ->
  exists x, U x /\ forall y, P x y -> ~ U y.
Proof.
  intros W [x H]. revert H.
  induction (W x) as [x K IH]; intro H.
  destruct (classic (exists y, P x y /\ U y)) as [[y [L M]] | N].
  - apply (IH y L M).
  - exists x; split; [exact H | firstorder].
Qed.
Lemma wf_no_serial (P : rel X) (U : X -> Prop) :
  WF P -> (exists x, U x) ->
  (forall x, U x -> exists y, U y /\ P x y) -> False.
Proof.
  intros W N H.
  destruct (wf_minimum P U W N) as [x [K L]].
  destruct (H x K) as [y [M E]]; exact (L y E M).
Qed.
Lemma wf_irrefl (P : rel X) : WF P -> forall x, ~ P x x.
Proof.
  intros W x H.
  eapply (wf_no_serial P (fun y => y = x)).
  - exact W.
  - exists x; reflexivity.
  - intros y ->; exists x; auto.
Qed.
Lemma wf_normal_form (P : rel X) :
  WF P -> forall x, exists y, star P x y /\ normal P y.
Proof.
  intros W x; induction (W x) as [x K IH].
  destruct (classic (exists y, P x y)) as [[y H] | H].
  - destruct (IH y H) as [z [L M]]. exists z; split;
      [exact (star_cons H L) | exact M].
  - exists x; split; [apply star_refl | firstorder].
Qed.
Lemma bad_step (P : rel X) x y : P x y -> bad P y -> bad P x.
Proof.
  intros H K A; destruct A as [A]; apply K; apply A; exact H.
Qed.
Lemma bad_star (P : rel X) x y : star P x y -> bad P y -> bad P x.
Proof.
  intro H; induction H; intro K; eauto using bad_step.
Qed.
Lemma bad_mono (P Q : rel X) :
  (forall x y, P x y -> Q x y) ->
  forall x, bad P x -> bad Q x.
Proof.
  intros H x K L; apply K; eapply acc_mono; eauto.
Qed.
Lemma bad_successor (P : rel X) x :
  bad P x -> exists y, P x y /\ bad P y.
Proof.
  intro H. apply NNPP; intro N. apply H. constructor; intros y K.
  apply NNPP; intro L. apply N; exists y; auto.
Qed.
Lemma not_wf_has_bad (P : rel X) :
  ~ WF P -> exists x, bad P x.
Proof.
  intro H; apply NNPP; intro N; apply H; intro x.
  apply NNPP; intro K; apply N; exists x; exact K.
Qed.

(** Minimal-successor argument, used to prove the required detour instance.
    The rerouting premise is required only at P-minimal points of K. *)
Lemma serial_rerouting_impossible (P Q : rel X) (K : X -> Prop) :
  WF P -> WF Q -> (exists x, K x) ->
  (forall x, K x -> exists y, K y /\ (P x y \/ Q x y)) ->
  (forall x y z,
      K x -> (forall t, P x t -> ~ K t) ->
      Q x y -> P y z -> K z -> Q x z) -> False.
Proof.
  intros WP WQ NK HS HR.
  set (M := fun x => K x /\ forall y, P x y -> ~ K y).
  assert (NM : exists x, M x).
  { destruct (wf_minimum P K WP NK) as [x H]; exists x; exact H. }
  destruct (wf_minimum Q M WQ NM) as [x [[Kx Px] Qx]].
  destruct (HS x Kx) as [y [Ky [Pxy | Qxy]]].
  - exact (Px y Pxy Ky).
  - set (V := fun t => Q x t /\ K t).
    assert (NV : exists t, V t) by (exists y; split; assumption).
    destruct (wf_minimum P V WP NV) as [t [[Qxt Kt] Pt]].
    assert (Mt : M t).
    { split; [exact Kt |]. intros z Ptz Kz.
      apply (Pt z Ptz). split; [eapply HR; eauto | exact Kz]. }
    exact (Qx t Qxt Mt).
Qed.

(** The weak Jumping criterion QP subset P+ union Q, proved here. *)
Lemma weak_jumping (P Q : rel X) :
  WF P -> WF Q ->
  (forall x y z, Q x y -> P y z -> plus P x z \/ Q x z) ->
  WF (cup P Q).
Proof.
  intros WP WQ H. apply NNPP; intro N.
  destruct (not_wf_has_bad _ N) as [a Ha].
  eapply (serial_rerouting_impossible P Q (bad (cup P Q))).
  - exact WP.
  - exact WQ.
  - exists a; exact Ha.
  - intros x Kx; destruct (bad_successor _ x Kx) as [y [E Ky]].
    exists y; auto.
  - intros x y z Kx Px Qxy Pyz Kz.
    destruct (H x y z Qxy Pyz) as [[u [Pxu Suz]] | Qxz]; auto.
    exfalso; apply (Px u Pxu).
    eapply bad_star; [|exact Kz].
    eapply star_mono; [|exact Suz]. unfold cup; firstorder.
Qed.

(** Exactly the constriction instance needed in the finite theorem.
    It is proved, not postulated or imported as a paper lemma. *)
Lemma detour_tail (B C D : rel X) :
  WF C -> WF D ->
  (forall x y z, D x y -> C y z ->
     (exists u, B x u /\ star (cup B (cup C D)) u z) \/
     plus C x z \/ D x z) ->
  WF (fun x y => (C x y \/ D x y) /\
       forall z, B x z -> ~ bad (cup B (cup C D)) z).
Proof.
  intros WC WD H2.
  set (E := cup B (cup C D)).
  set (G := fun x => forall z, B x z -> ~ bad E z).
  set (Q := fun x y => D x y /\ G x).
  assert (WQ : WF Q).
  { eapply wf_mono; [|exact WD]; firstorder. }
  assert (WH : WF (cup C Q)).
  { apply NNPP; intro N.
    destruct (not_wf_has_bad _ N) as [a Ha].
    eapply (serial_rerouting_impossible C Q (bad (cup C Q))).
    - exact WC.
    - exact WQ.
    - exists a; exact Ha.
    - intros x Kx; destruct (bad_successor _ x Kx) as [y [L Ky]].
      exists y; auto.
    - intros x y z Kx Px [Dxy Gx] Cyz Kz.
      destruct (H2 x y z Dxy Cyz) as [[u [Bxu Suz]] | [Cxz | Dxz]].
      + exfalso; apply (Gx u Bxu).
        eapply bad_star; [exact Suz |].
        eapply bad_mono; [|exact Kz].
        unfold Q, E, cup; firstorder.
      + destruct Cxz as [u [Cxu Suz]].
        exfalso; apply (Px u Cxu).
        eapply bad_star; [|exact Kz].
        eapply star_mono; [|exact Suz]. unfold cup; firstorder.
      + split; assumption. }
  eapply wf_mono; [|exact WH]. unfold Q, G, E, cup; firstorder.
Qed.

(** A finite set in an acyclic transitive relation has a predecessor-free point.
    The set is represented by a covering list; no decidable equality is needed. *)
Lemma finite_source (T : rel X) :
  (forall x, ~ T x x) ->
  (forall x y z, T x y -> T y z -> T x z) ->
  forall (V : X -> Prop) (l : list X),
    (forall x, V x -> In x l) -> (exists x, V x) ->
    exists z, V z /\ forall y, V y -> ~ T y z.
Proof.
  intros IR TR V l.
  assert (H : (forall x, In x l -> ~ V x) \/
      exists z, In z l /\ V z /\
        forall y, In y l -> V y -> ~ T y z).
  { induction l as [|a l IH].
    - left; simpl; tauto.
    - destruct (classic (V a)) as [Va | Na].
      + destruct IH as [Empty | [z [Iz [Vz Min]]]].
        * right; exists a; simpl; repeat split; auto.
          intros y [Eq | Iy] Vy Tya.
          -- subst y; exact (IR a Tya).
          -- exact (Empty y Iy Vy).
        * destruct (classic (T a z)) as [Taz | Naz].
          -- right; exists a; simpl; repeat split; auto.
             intros y [Eq | Iy] Vy Tya.
             ++ subst y; exact (IR a Tya).
             ++ apply (Min y Iy Vy); eapply TR; eauto.
          -- right; exists z; simpl; repeat split; auto.
             intros y [Eq | Iy] Vy Tyz.
             ++ subst y; exact (Naz Tyz).
             ++ exact (Min y Iy Vy Tyz).
      + destruct IH as [Empty | [z [Iz [Vz Min]]]].
        * left; simpl; intros x [Eq | Ix]; [subst x; exact Na | apply Empty; exact Ix].
        * right; exists z; simpl; repeat split; auto.
          intros y [Eq | Iy] Vy Tyz.
          -- subst y; exact (Na Vy).
          -- exact (Min y Iy Vy Tyz). }
  intros Cover Nonempty.
  destruct H as [Empty | [z [Iz [Vz Min]]]].
  - destruct Nonempty as [x Vx]; exfalso; eapply Empty; eauto.
  - exists z; split; [exact Vz |]. intros y Vy; apply Min; auto.
Qed.

(** Finiteness connects the usual graph formulation (no directed cycle)
    to standard accessibility, without adding a choice principle. *)
Lemma finite_acyclic_wf (P : rel X) :
  (exists l : list X, forall x, In x l) ->
  (forall x, ~ plus P x x) -> WF P.
Proof.
  intros [l All] AC. apply NNPP; intro N.
  destruct (not_wf_has_bad P N) as [a Ha].
  assert (IR : forall x, ~ flip (plus P) x x) by exact AC.
  assert (TR : forall x y z,
      flip (plus P) x y -> flip (plus P) y z -> flip (plus P) x z).
  { intros x y z H K; unfold flip in *; eapply plus_trans; eauto. }
  assert (Cover : forall x, bad P x -> In x l) by auto.
  destruct (finite_source (flip (plus P)) IR TR (bad P) l Cover
    (ex_intro _ a Ha)) as [z [Hz Min]].
  destruct (bad_successor P z Hz) as [y [Pzy Hy]].
  apply (Min y Hy); unfold flip; apply plus_one; exact Pzy.
Qed.

Lemma star_cut (J : X -> Prop) (P : rel X) :
  (forall x y, P x y -> J y -> J x) ->
  forall x y, star P x y -> J y -> J x /\ star (cut J P) x y.
Proof.
  intros Back x y H; induction H as [x | x y z Pxy Syz IH]; intro Jz.
  - split; [exact Jz | apply star_refl].
  - destruct (IH Jz) as [Jy L].
    assert (Jx : J x) by (eapply Back; eauto).
    split; [exact Jx |]. eapply star_cons; [unfold cut; eauto |exact L].
Qed.
Lemma plus_cut (J : X -> Prop) (P : rel X) :
  (forall x y, P x y -> J y -> J x) ->
  forall x y, plus P x y -> J y -> J x /\ plus (cut J P) x y.
Proof.
  intros Back x y [z [Pxz Szy]] Jy.
  destruct (star_cut J P Back _ _ Szy Jy) as [Jz H].
  assert (Jx : J x) by (eapply Back; eauto).
  split; [exact Jx |]. exists z; split; [unfold cut; auto |exact H].
Qed.
End Basic.

(** A transitive subrelation of a union of two well-founded relations is
    well-founded.  This is a derived theorem, not a new assumption. *)
Lemma transitive_subunion_wf {X} (T C D : rel X) :
  WF C -> WF D ->
  (forall x y, T x y -> C x y \/ D x y) ->
  (forall x y z, T x y -> T y z -> T x z) -> WF T.
Proof.
  intros WC WD Sub Trans.
  set (P := fun x y => T x y /\ C x y).
  set (Q := fun x y => T x y /\ D x y).
  assert (WP : WF P).
  { eapply wf_mono; [|exact WC]. unfold P; firstorder. }
  assert (WQ : WF Q).
  { eapply wf_mono; [|exact WD]. unfold Q; firstorder. }
  assert (W : WF (cup P Q)).
  { apply weak_jumping; [exact WP |exact WQ |].
    intros x y z [Txy Dxy] [Tyz Cyz].
    assert (Txz : T x z) by (eapply Trans; eauto).
    destruct (Sub x z Txz) as [Cxz | Dxz].
    - left; apply plus_one; split; assumption.
    - right; split; assumption. }
  eapply wf_mono; [|exact W].
  intros x y Txy; destruct (Sub x y Txy); unfold cup, P, Q; auto.
Qed.

(** [long P n x] means that at least n consecutive P-steps are possible
    starting at x.  In particular [long P 0 x] holds at every point. *)
Fixpoint long {X} (P : rel X) (n : nat) (x : X) : Prop :=
  match n with
  | 0 => True
  | S k => exists y, P x y /\ long P k y
  end.
Definition height_le {X} (P : rel X) (n : nat) (x : X) : Prop :=
  ~ long P (Datatypes.S n) x.

Section PathLengths.
Context {X : Type}.
Lemma long_down (P : rel X) n :
  forall x, long P (Datatypes.S n) x -> long P n x.
Proof.
  induction n as [|n IH]; intros x H.
  - exact I.
  - destruct H as [y [Pxy Hy]]. exists y; split; [exact Pxy |].
    apply IH; exact Hy.
Qed.
Lemma long_le (P : rel X) n m :
  n <= m -> forall x, long P m x -> long P n x.
Proof.
  intro H; induction H as [|m H IH]; intros x L.
  - exact L.
  - apply IH; apply long_down; exact L.
Qed.
Lemma long_mono (P Q : rel X) :
  (forall x y, P x y -> Q x y) ->
  forall n x, long P n x -> long Q n x.
Proof.
  intros Sub n; induction n as [|n IH]; intros x H.
  - exact I.
  - destruct H as [y [Pxy Hy]]. exists y; split; eauto.
Qed.
Lemma star_long (P : rel X) x y :
  star P x y -> forall n, long P n y -> long P n x.
Proof.
  intro Path; induction Path as [x |x y z Pxy Pyz IH]; intros n H.
  - exact H.
  - apply (long_down P n x). exists y; split; [exact Pxy |].
    apply IH; exact H.
Qed.
Lemma plus_long (P : rel X) x y :
  plus P x y -> forall n, long P n y -> long P (Datatypes.S n) x.
Proof.
  intros [z [Pxz Pzy]] n H. exists z; split; [exact Pxz |].
  eapply star_long; eauto.
Qed.
Lemma height_edge (P : rel X) n x y :
  height_le P (Datatypes.S n) x -> P x y -> height_le P n y.
Proof.
  intros H Pxy Ly. apply H. exists y; split; assumption.
Qed.
Lemma height_mono (P Q : rel X) :
  (forall x y, P x y -> Q x y) ->
  forall n x, height_le Q n x -> height_le P n x.
Proof.
  intros Sub n x H L; apply H. eapply long_mono; eauto.
Qed.
Lemma height_implies_acc (P : rel X) n :
  forall x, height_le P n x -> Acc (flip P) x.
Proof.
  induction n as [|n IH]; intros x H; constructor; intros y Pxy.
  - exfalso; apply H. exists y; split; [exact Pxy |exact I].
  - apply IH. eapply height_edge; eauto.
Qed.
Lemma bounded_implies_wf (P : rel X) :
  (forall x, exists n, height_le P n x) -> WF P.
Proof.
  intros Bound x; destruct (Bound x) as [n H].
  eapply height_implies_acc; exact H.
Qed.

(** A finite family of pointwise bounds has a common bound.  This elementary
    list induction is also used to avoid dependent choice in the finitely
    branching corollary. *)
Lemma finite_family_bound (P : rel X) (l : list X) :
  (forall x, In x l -> exists n, height_le P n x) ->
  exists n, forall x, In x l -> height_le P n x.
Proof.
  induction l as [|a l IH]; intro Bound.
  - exists 0; intros x H; contradiction.
  - destruct (Bound a (or_introl eq_refl)) as [n Hn].
    destruct (IH (fun x Hx => Bound x (or_intror Hx))) as [m Hm].
    exists (n + m). intros x [Eq |Hx] L.
    + subst x; apply Hn. eapply (long_le P (Datatypes.S n) (Datatypes.S (n + m))); [lia |exact L].
    + apply (Hm x Hx). eapply (long_le P (Datatypes.S m) (Datatypes.S (n + m))); [lia |exact L].
Qed.
Definition finitely_branching (P : rel X) :=
  forall x, exists l : list X, forall y, P x y -> In y l.
Lemma finitely_branching_wf_height (P : rel X) :
  WF P -> finitely_branching P ->
  forall x, exists n, height_le P n x.
Proof.
  intros W Branch x; induction (W x) as [x Ax IH].
  destruct (Branch x) as [l Cover].
  assert (Family : forall y, In y l ->
      exists n, P x y -> height_le P n y).
  { intros y Hy; destruct (classic (P x y)) as [Pxy |Nxy].
    - destruct (IH y Pxy) as [n Hn]; exists n; auto.
    - exists 0; intros Pxy; contradiction. }
  assert (Bound : exists n, forall y, In y l ->
      P x y -> height_le P n y).
  { clear Cover. revert Family. induction l as [|a l IL]; intro Family.
    - exists 0; intros y Hy; contradiction.
    - destruct (Family a (or_introl eq_refl)) as [n Hn].
      destruct (IL (fun y Hy => Family y (or_intror Hy))) as [m Hm].
      exists (n + m); intros y [Eq |Hy] Pxy L.
      + subst y; apply (Hn Pxy). eapply (long_le P (Datatypes.S n) (Datatypes.S (n + m))); [lia |exact L].
      + apply (Hm y Hy Pxy). eapply (long_le P (Datatypes.S m) (Datatypes.S (n + m))); [lia |exact L]. }
  destruct Bound as [n Bound]. exists (Datatypes.S n).
  intros [y [Pxy Ly]]. apply (Bound y (Cover y Pxy) Pxy); exact Ly.
Qed.
End PathLengths.

Definition R0 {X} (A B C D : rel X) := cup A (cup B (cup C D)).
Definition E0 {X} (B C D : rel X) := cup B (cup C D).
Definition F0 {X} (C D : rel X) := cup C D.
Definition P0 {X} (A B C D : rel X) :=
  forall x y z, E0 B C D x y -> A y z ->
    (exists u, A x u /\ star (R0 A B C D) u z) \/ E0 B C D x z.
Definition P1 {X} (A B C D : rel X) :=
  forall x y z, F0 C D x y -> B y z ->
    (exists u, A x u /\ star (R0 A B C D) u z) \/
    plus B x z \/ F0 C D x z.
Definition P1_strong {X} (A B C D : rel X) :=
  forall x y z, F0 C D x y -> B y z ->
    (exists u, A x u /\ star (R0 A B C D) u z) \/ plus B x z.
Lemma P1_strong_implies {X} (A B C D : rel X) :
  P1_strong A B C D -> P1 A B C D.
Proof.
  unfold P1_strong, P1.
  intros H x y z Fxy Byz.
  destruct (H x y z Fxy Byz) as [HA | HB].
  - left; exact HA.
  - right; left; exact HB.
Qed.
Definition Q2 {X} (B C D : rel X) :=
  forall x y z, D x y -> C y z ->
    (exists u, B x u /\ star (E0 B C D) u z) \/
    plus C x z \/ D x z.

Section SerialDomain.
Context {X : Type}.
Variables A B C D : rel X.
Variable J : X -> Prop.
Let F := F0 C D.
Let E := E0 B C D.
Let R := R0 A B C D.
Hypotheses (WA : WF A) (WB : WF B) (WC : WF C) (WD : WF D).
Hypotheses (H0 : P0 A B C D) (H1 : P1 A B C D) (H2 : Q2 B C D).
Hypothesis Domain : forall x y, R x y -> J x /\ J y.
Hypothesis Serial : forall x, J x -> exists y, R x y.

Definition M x := J x /\ normal A x.
Definition representatives (S : X -> Prop) :=
  forall z, J z -> exists t, S t /\
    forall x, S x -> E x z -> E x t.
Definition active (S : X -> Prop) z := exists x, S x /\ B x z.

Lemma E_irrefl : forall x, ~ E x x.
Proof.
  intros x H; destruct H as [H | [H | H]];
    [exact (wf_irrefl B WB x H) | exact (wf_irrefl C WC x H) |
     exact (wf_irrefl D WD x H)].
Qed.
Lemma E_to_normal x z t :
  normal A x -> E x z -> star A z t -> E x t.
Proof.
  intros Nx Exz Path; revert Exz.
  induction Path as [z | z u t Azu Sut IH]; intro Exz; auto.
  apply IH. destruct (H0 x z u Exz Azu) as [[v [Axv L]] | Exu].
  - exfalso; exact (Nx v Axv).
  - exact Exu.
Qed.
Lemma initial_representatives : representatives M.
Proof.
  intros z Jz.
  destruct (wf_normal_form A WA z) as [t [Path Nt]].
  assert (Jt : J t).
  { revert Jz; induction Path as [z | z u t Azu Sut IH]; intro Jz.
    - exact Jz.
    - exact (IH Nt (proj2 (Domain z u (or_introl Azu)))). }
  exists t; split; [split; assumption |].
  intros x [_ Nx] Exz; eapply E_to_normal; eauto.
Qed.
Lemma representatives_serial (S : X -> Prop) :
  (forall x, S x -> M x) -> representatives S ->
  forall x, S x -> exists y, S y /\ E x y.
Proof.
  intros Sub Rep x Sx.
  destruct (Sub x Sx) as [Jx Nx].
  destruct (Serial x Jx) as [z [Axz | Exz]].
  - exfalso; exact (Nx z Axz).
  - assert (Jz : J z) by (exact (proj2 (Domain x z (or_intror Exz)))).
    destruct (Rep z Jz) as [t [St Et]].
    exists t; split; [exact St | apply Et; assumption].
Qed.
Lemma empty_active_impossible (S : X -> Prop) :
  (exists x, S x) -> (forall x, S x -> M x) ->
  representatives S -> (forall z, ~ active S z) -> False.
Proof.
  intros NE Sub Rep Empty.
  pose proof (detour_tail B C D WC WD H2) as Barrier.
  eapply (wf_no_serial _ S Barrier NE).
  intros x Sx.
  destruct (representatives_serial S Sub Rep x Sx) as [y [Sy Exy]].
  assert (NB : forall z, ~ B x z).
  { intros z Bxz; apply (Empty z); exists x; auto. }
  exists y; split; [exact Sy |]. split.
  - destruct Exy as [Bxy | Fxy]; [exfalso; exact (NB y Bxy) | exact Fxy].
  - intros z Bxz; exfalso; exact (NB z Bxz).
Qed.

(** One complete folding step. *)
Lemma fold_step (S : X -> Prop) z :
  (forall x, S x -> M x) -> representatives S ->
  active S z -> (forall y, active S y -> ~ plus B y z) ->
  exists (S' : X -> Prop),
    (exists x, S' x) /\
    (forall x, S' x -> S x) /\
    representatives S' /\
    (forall u, active S' u -> active S u /\ u <> z).
Proof.
  intros Sub Rep Vz Min.
  destruct Vz as [w [Sw Bwz]].
  assert (Jz : J z).
  { exact (proj2 (Domain w z (or_intror (or_introl Bwz)))). }
  destruct (Rep z Jz) as [t [St Target]].
  assert (Ntz : ~ B t z).
  { intro Btz; apply (E_irrefl t). apply Target; [exact St |left; exact Btz]. }
  assert (Collapse : forall x, S x -> plus B x z -> B x z).
  { intros x Sx Path; destruct (plus_split B x z Path) as [Bxz | [y [Bxy Pyz]]]; auto.
    exfalso; apply (Min y); [exists x; auto |exact Pyz]. }
  assert (Transfer : forall x y, S x -> S y -> B y z -> E x y -> E x t).
  { intros x y Sx Sy Byz Exy. apply Target; [exact Sx |].
    destruct Exy as [Bxy | Fxy].
    - exfalso; apply (Min y); [exists x; auto |apply plus_one; exact Byz].
    - destruct (H1 x y z Fxy Byz) as [[u [Axu L]] | [Pxz | Fxz]].
      + exfalso; exact (proj2 (Sub x Sx) u Axu).
      + left; apply Collapse; assumption.
      + right; exact Fxz. }
  set (S' := fun x => S x /\ ~ B x z).
  exists S'; split.
  - exists t; split; assumption.
  - split.
    + intros x [Sx _]; exact Sx.
    + split.
      * intros v Jv.
        destruct (Rep v Jv) as [u [Su Urep]].
        destruct (classic (B u z)) as [Buz | Nuz].
        -- exists t; split; [split; assumption |].
           intros x [Sx Nx] Exv.
           eapply Transfer; [exact Sx | exact Su | exact Buz |].
           apply Urep; [exact Sx | exact Exv].
        -- exists u; split; [split; assumption |].
           intros x [Sx Nx] Exv. apply Urep; assumption.
      * intros u [x [[Sx Nx] Bxu]]; split.
        -- exists x; auto.
        -- intro Eq; subst u; exact (Nx Bxu).
Qed.

Lemma finite_active_impossible :
  forall n (l : list X) (S : X -> Prop),
    length l <= n ->
    (exists x, S x) -> (forall x, S x -> M x) ->
    representatives S ->
    (forall z, active S z -> In z l) -> False.
Proof.
  induction n as [|n IH]; intros l S Len NE Sub Rep Cover.
  - apply (empty_active_impossible S NE Sub Rep).
    intros z Vz. specialize (Cover z Vz).
    destruct l; simpl in *; [contradiction |lia].
  - destruct (classic (exists z, active S z)) as [NV | Empty].
    + destruct (finite_source (plus B)
        (wf_irrefl (plus B) (wf_plus B WB)) (plus_trans B)
        (active S) l Cover NV) as [z [Vz Min]].
      destruct (fold_step S z Sub Rep Vz Min) as [S' [NE' [Sub' [Rep' Small]]]].
      assert (Iz : In z l) by (apply Cover; exact Vz).
      apply in_split in Iz; destruct Iz as [l1 [l2 Eq]].
      eapply (IH (l1 ++ l2) S').
      * subst l; rewrite !app_length in *; simpl in *; lia.
      * exact NE'.
      * intros x H; apply Sub; apply Sub'; exact H.
      * exact Rep'.
      * intros u Vu.
        destruct (Small u Vu) as [Vu0 Nuz].
        specialize (Cover u Vu0). rewrite Eq in Cover.
        apply in_app_iff; apply in_app_iff in Cover.
        simpl in Cover; destruct Cover as [L | [Eq' | Rr]];
          [left; exact L |exfalso; apply Nuz; symmetry; exact Eq' |right; exact Rr].
    + apply (empty_active_impossible S NE Sub Rep); firstorder.
Qed.

Theorem serial_domain_finite_image_impossible :
  (exists x, J x) ->
  (exists l : list X, forall z, active M z -> In z l) -> False.
Proof.
  intros [a Ja] [l Cover].
  pose proof initial_representatives as Rep.
  destruct (Rep a Ja) as [t [Mt _]].
  eapply (finite_active_impossible (length l) l M).
  - lia.
  - exists t; exact Mt.
  - auto.
  - exact Rep.
  - exact Cover.
Qed.

(** Uniform finite height, with every original shortcut alternative retained. *)
Definition domination (S : X -> Prop) (u v : X) :=
  S u /\ S v /\ E u v /\
  forall x, S x -> E x u -> E x v.

Lemma domination_transitive (S : X -> Prop) x y z :
  domination S x y -> domination S y z -> domination S x z.
Proof.
  intros [Sx [Sy [Exy Hxy]]] [_ [Sz [Eyz Hyz]]].
  split; [exact Sx |]. split; [exact Sz |]. split.
  - apply Hyz; assumption.
  - intros t St Etx; apply Hyz; [exact St |apply Hxy; assumption].
Qed.
Lemma domination_path_transfer (S : X -> Prop) u v :
  star (domination S) u v ->
  forall x, S x -> E x u -> E x v.
Proof.
  intro Path; induction Path as [u |u t v Hdt Path IH];
    intros x Sx Exu.
  - exact Exu.
  - apply IH; [exact Sx |]. destruct Hdt as [_ [_ [_ Transfer]]].
    apply Transfer; assumption.
Qed.

Lemma top_domination_successor (S : X -> Prop) h :
  (forall x, S x -> M x) -> representatives S ->
  (forall x, S x -> height_le B (Datatypes.S h) x) ->
  forall y, S y -> long B (Datatypes.S h) y ->
  exists t, domination S y t.
Proof.
  intros Sub Rep Bound y Sy [z [Byz Lz]].
  assert (Jz : J z).
  { exact (proj2 (Domain y z (or_intror (or_introl Byz)))). }
  destruct (Rep z Jz) as [t [St Target]].
  exists t; split; [exact Sy |]. split; [exact St |]. split.
  - apply Target; [exact Sy |left; exact Byz].
  - intros x Sx Exy. apply Target; [exact Sx |].
    destruct Exy as [Bxy |Fxy].
    + exfalso; apply (Bound x Sx). exists y; split; [exact Bxy |].
      exists z; split; assumption.
    + destruct (H1 x y z Fxy Byz) as [[u [Axu L]] |[Pxz |Fxz]].
      * exfalso; exact (proj2 (Sub x Sx) u Axu).
      * destruct (plus_split B x z Pxz) as [Bxz |[u [Bxu Puz]]].
        -- left; exact Bxz.
        -- exfalso; apply (Bound x Sx). exists u; split; [exact Bxu |].
           eapply plus_long; [exact Puz |exact Lz].
      * right; exact Fxz.
Qed.

Lemma top_domination_wf (S : X -> Prop) h :
  (forall x, S x -> height_le B (Datatypes.S h) x) ->
  WF (cut (fun x => S x /\ long B (Datatypes.S h) x) (domination S)).
Proof.
  intro Bound.
  eapply (transitive_subunion_wf _ C D).
  - exact WC.
  - exact WD.
  - intros x y [[Sx Lx] [[_ [_ [Exy Hxy]]] [Sy Ly]]].
    destruct Exy as [Bxy |Fxy]; [|exact Fxy].
    exfalso; apply (Bound x Sx). exists y; split; assumption.
  - intros x y z [Ux [Txy Uy]] [Uy' [Tyz Uz]].
    split; [exact Ux |]. split; [|exact Uz].
    eapply domination_transitive; eauto.
Qed.

Lemma lower_representatives (S : X -> Prop) h :
  (exists x, S x) -> (forall x, S x -> M x) ->
  representatives S -> (forall x, S x -> height_le B (Datatypes.S h) x) ->
  let Lower := fun x => S x /\ height_le B h x in
  (exists x, Lower x) /\ representatives Lower.
Proof.
  intros NE Sub Rep Bound Lower.
  set (Top := fun x => S x /\ long B (Datatypes.S h) x).
  set (T := cut Top (domination S)).
  assert (WT : WF T).
  { apply top_domination_wf; exact Bound. }
  assert (Exit : forall u, S u ->
      exists v, Lower v /\ star (domination S) u v).
  { intro u; induction (WT u) as [u Au IH]; intro Su.
    destruct (classic (long B (Datatypes.S h) u)) as [Lu |Nu].
    - destruct (top_domination_successor S h Sub Rep Bound u Su Lu)
        as [v Huv].
      assert (Sv : S v) by (exact (proj1 (proj2 Huv))).
      destruct (classic (long B (Datatypes.S h) v)) as [Lv |Nv].
      + assert (Tuv : T u v).
        { unfold T, cut, Top; split; [split; assumption |].
          split; [exact Huv |split; assumption]. }
        destruct (IH v Tuv Sv) as [w [Lw Path]].
        exists w; split; [exact Lw |exact (star_cons Huv Path)].
      + exists v; split.
        * unfold Lower; split; assumption.
        * apply star_one; exact Huv.
    - exists u; split.
      + unfold Lower; split; assumption.
      + apply star_refl. }
  split.
  - destruct NE as [u Su]. destruct (Exit u Su) as [v [Lv _]].
    exists v; exact Lv.
  - intros z Jz. destruct (Rep z Jz) as [u [Su Urep]].
    destruct (Exit u Su) as [v [Lv Path]].
    exists v; split; [exact Lv |]. intros x [Sx Hx] Exz.
    eapply domination_path_transfer; [exact Path |exact Sx |].
    apply Urep; assumption.
Qed.

Lemma bounded_representatives_impossible :
  forall h (S : X -> Prop),
    (exists x, S x) -> (forall x, S x -> M x) ->
    representatives S -> (forall x, S x -> height_le B h x) -> False.
Proof.
  induction h as [|h IH]; intros S NE Sub Rep Bound.
  - apply (empty_active_impossible S NE Sub Rep).
    intros z [x [Sx Bxz]]. apply (Bound x Sx).
    exists z; split; [exact Bxz |exact I].
  - destruct (lower_representatives S h NE Sub Rep Bound) as [NE' Rep'].
    eapply (IH (fun x => S x /\ height_le B h x)).
    + exact NE'.
    + intros x [Sx Hx]; apply Sub; exact Sx.
    + exact Rep'.
    + intros x [Sx Hx]; exact Hx.
Qed.

Theorem serial_domain_bounded_height_impossible :
  (exists x, J x) ->
  (exists h, forall x, M x -> height_le B h x) -> False.
Proof.
  intros [a Ja] [h Bound].
  pose proof initial_representatives as Rep.
  destruct (Rep a Ja) as [t [Mt _]].
  eapply (bounded_representatives_impossible h M).
  - exists t; exact Mt.
  - auto.
  - exact Rep.
  - exact Bound.
Qed.

(** No-shortcut strengthening.  The pointwise conclusion actually holds at
    every A-minimal immortal point, not just the doubly minimal stratum. *)
Lemma strong_F_long
  (Hstrong : forall x y z, F x y -> B y z ->
     (exists u, A x u /\ star R u z) \/ plus B x z) :
  forall x y, normal A x -> F x y ->
    forall n, long B n y -> long B n x.
Proof.
  intros x y Nx Fxy n Ly; destruct n as [|n].
  - exact I.
  - destruct Ly as [z [Byz Lz]].
    destruct (Hstrong x y z Fxy Byz) as [[u [Axu Path]] |Pxz].
    + exfalso; exact (Nx u Axu).
    + eapply plus_long; [exact Pxz |exact Lz].
Qed.

Theorem serial_domain_pointwise_height_impossible
  (Hstrong : forall x y z, F x y -> B y z ->
     (exists u, A x u /\ star R u z) \/ plus B x z) :
  forall a, M a -> forall h, height_le B h a -> False.
Proof.
  intros a Ma h Ha.
  set (S := fun x => M x /\ height_le B h x).
  assert (Sub : forall x, S x -> M x) by (intros x [Mx Hx]; exact Mx).
  assert (Closure : forall x y, S x -> M y -> E x y -> S y).
  { intros x y [[Jx Nx] Hx] My Exy.
    split; [exact My |]. intro Ly; apply Hx.
    destruct Exy as [Bxy |Fxy].
    - apply (long_down B (Datatypes.S h) x).
      exists y; split; assumption.
    - eapply strong_F_long; eauto. }
  assert (Rep : representatives S).
  { intros z Jz.
    destruct (classic (exists x, S x /\ E x z)) as [[x [Sx Exz]] |None].
    - destruct (initial_representatives z Jz) as [t [Mt Target]].
      exists t; split.
      + eapply Closure; [exact Sx |exact Mt |apply Target; auto using Sub].
      + intros u Su Euz; apply Target; [apply Sub; exact Su |exact Euz].
    - exists a; split; [split; assumption |].
      intros x Sx Exz; exfalso; apply None; exists x; auto. }
  eapply (bounded_representatives_impossible h S).
  - exists a; split; assumption.
  - exact Sub.
  - exact Rep.
  - intros x [_ Hx]; exact Hx.
Qed.


(** Abstract ordinal-rank refinement.  No ordinal library is postulated:
    the order and the defining least-upper-bound property of the rank are
    explicit hypotheses.  The conclusion says that the least realized rank
    has a nonempty lower segment with no greatest member. *)
Section Ranks.
Context {K : Type}.
Variable ltK : K -> K -> Prop.
Variable rho : X -> K.
Let leK u v := u = v \/ ltK u v.
Hypotheses
  (LTirrefl : forall u, ~ ltK u u)
  (LTtrans : forall u v w, ltK u v -> ltK v w -> ltK u w)
  (LTtotal : forall u v, u = v \/ ltK u v \/ ltK v u)
  (RankStep : forall x y, B x y -> ltK (rho y) (rho x))
  (RankBound : forall x alpha,
     (forall y, B x y -> ltK (rho y) alpha) -> leK (rho x) alpha)
  (RankStrong : forall x y z, F x y -> B y z ->
     (exists u, A x u /\ star R u z) \/ plus B x z).

Lemma rank_le_antisym u v : leK u v -> leK v u -> u = v.
Proof.
  intros [Eq |Luv] [Eq' |Lvu]; try assumption; try congruence.
  exfalso; apply (LTirrefl u); eapply LTtrans; eauto.
Qed.
Lemma rank_star x y : star B x y -> leK (rho y) (rho x).
Proof.
  intro Path; induction Path as [x |x y z Bxy Path IH].
  - left; reflexivity.
  - right; destruct IH as [Eq |Lzy].
    + rewrite Eq; apply RankStep; exact Bxy.
    + eapply LTtrans; [exact Lzy |apply RankStep; exact Bxy].
Qed.
Lemma rank_plus x y : plus B x y -> ltK (rho y) (rho x).
Proof.
  intros [z [Bxz Path]]. destruct (rank_star z y Path) as [Eq |Lyz].
  - rewrite Eq; apply RankStep; exact Bxz.
  - eapply LTtrans; [exact Lyz |apply RankStep; exact Bxz].
Qed.
Lemma rank_F_nonincrease x y :
  normal A x -> F x y -> leK (rho y) (rho x).
Proof.
  intros Nx Fxy. apply RankBound. intros z Byz.
  destruct (RankStrong x y z Fxy Byz) as [[u [Axu Path]] |Pxz].
  - exfalso; exact (Nx u Axu).
  - apply rank_plus; exact Pxz.
Qed.

Variable alpha : K.
Hypotheses
  (RankRealized : exists x, M x /\ rho x = alpha)
  (RankMinimal : forall x, M x -> leK alpha (rho x)).
Let Smin := fun x => M x /\ rho x = alpha.

Lemma rank_min_representatives : representatives Smin.
Proof.
  intros z Jz.
  destruct (classic (exists x, Smin x /\ E x z))
    as [[x [[Mx Rx] Exz]] |None].
  - destruct (initial_representatives z Jz) as [t [Mt Target]].
    assert (Ext : E x t) by (apply Target; assumption).
    assert (Rt : rho t = alpha).
    { apply rank_le_antisym; [|apply RankMinimal; exact Mt].
      rewrite <- Rx. destruct Ext as [Bxt |Fxt].
      - right; apply RankStep; exact Bxt.
      - apply rank_F_nonincrease; [exact (proj2 Mx) |exact Fxt]. }
    exists t; split; [split; assumption |].
    intros u [Mu Ru] Euz; apply Target; assumption.
  - destruct RankRealized as [t [Mt Rt]]. exists t; split; [split; assumption |].
    intros x Sx Exz; exfalso; apply None; exists x; auto.
Qed.
Lemma least_rank_nonzero : exists beta, ltK beta alpha.
Proof.
  apply NNPP; intro None.
  eapply (empty_active_impossible Smin).
  - exact RankRealized.
  - intros x [Mx Rx]; exact Mx.
  - exact rank_min_representatives.
  - intros z [x [[Mx Rx] Bxz]].
    apply None; exists (rho z). rewrite <- Rx; apply RankStep; exact Bxz.
Qed.

Lemma least_rank_not_successor beta :
  (forall gamma, ltK gamma alpha <-> leK gamma beta) -> False.
Proof.
  intro Cut.
  assert (Lba : ltK beta alpha).
  { apply (proj2 (Cut beta)); left; reflexivity. }
  assert (Attained : forall x, Smin x ->
      exists z, B x z /\ rho z = beta).
  { intros x [Mx Rx]; apply NNPP; intro No.
    assert (Upper : leK (rho x) beta).
    { apply RankBound; intros z Bxz.
      assert (Lza : ltK (rho z) alpha).
      { rewrite <- Rx; apply RankStep; exact Bxz. }
      destruct (proj1 (Cut (rho z)) Lza) as [Eq |Lzb]; [|exact Lzb].
      exfalso; apply No; exists z; auto. }
    rewrite Rx in Upper. destruct Upper as [Eq |Lab].
    - rewrite Eq in Lba; exact (LTirrefl beta Lba).
    - apply (LTirrefl alpha); eapply LTtrans; eauto. }
  assert (SubF : forall x y, domination Smin x y -> F x y).
  { intros x y [[Mx Rx] [[My Ry] [Exy Transfer]]].
    destruct Exy as [Bxy |Fxy]; [|exact Fxy].
    pose proof (RankStep x y Bxy) as L.
    rewrite Rx, Ry in L; exfalso; exact (LTirrefl alpha L). }
  assert (WT : WF (domination Smin)).
  { eapply (transitive_subunion_wf _ C D).
    - exact WC.
    - exact WD.
    - exact SubF.
    - intros x y z Hxy Hyz; eapply domination_transitive; eauto. }
  eapply (wf_no_serial (domination Smin) Smin WT RankRealized).
  intros y Sy.
  destruct (Attained y Sy) as [z [Byz Rz]].
  assert (Jz : J z).
  { exact (proj2 (Domain y z (or_intror (or_introl Byz)))). }
  destruct (rank_min_representatives z Jz) as [t [St Target]].
  exists t; split; [exact St |].
  split; [exact Sy |]. split; [exact St |]. split.
  - apply Target; [exact Sy |left; exact Byz].
  - intros x Sx Exy. apply Target; [exact Sx |].
    destruct Sx as [Mx Rx]. destruct Sy as [My Ry].
    destruct Exy as [Bxy |Fxy].
    + pose proof (RankStep x y Bxy) as L.
      rewrite Rx, Ry in L; exfalso; exact (LTirrefl alpha L).
    + destruct (RankStrong x y z Fxy Byz) as [[u [Axu Path]] |Pxz].
      * exfalso; exact (proj2 Mx u Axu).
      * destruct (plus_split B x z Pxz) as [Bxz |[u [Bxu Puz]]].
        -- left; exact Bxz.
        -- pose proof (RankStep x u Bxu) as Lua.
           rewrite Rx in Lua.
           pose proof (rank_plus u z Puz) as Lbu.
           rewrite Rz in Lbu.
           destruct (proj1 (Cut (rho u)) Lua) as [Eq |Lub].
           ++ rewrite Eq in Lbu; exfalso; exact (LTirrefl beta Lbu).
           ++ exfalso; apply (LTirrefl beta); eapply LTtrans; eauto.
Qed.

Theorem least_rank_is_nonzero_limit :
  (exists beta, ltK beta alpha) /\
  forall beta, ltK beta alpha ->
    exists gamma, ltK beta gamma /\ ltK gamma alpha.
Proof.
  split; [exact least_rank_nonzero |].
  intros beta Lba; apply NNPP; intro No.
  apply (least_rank_not_successor beta).
  intro gamma; split.
  - intro Lga. destruct (LTtotal gamma beta) as [Eq |[Lgb |Lbg]].
    + left; exact Eq.
    + right; exact Lgb.
    + exfalso; apply No; exists gamma; auto.
  - intros [Eq |Lgb].
    + rewrite Eq; exact Lba.
    + eapply LTtrans; eauto.
Qed.
End Ranks.

End SerialDomain.

Section Restriction.
Context {X : Type}.
Variables A B C D : rel X.
Let R := R0 A B C D.
Let E := E0 B C D.
Let I := bad R.
Let a := cut I A.
Let b := cut I B.
Let c := cut I C.
Let d := cut I D.

Lemma cut_R_equiv x y : R0 a b c d x y <-> cut I R x y.
Proof. unfold a, b, c, d, R, R0, E0, F0, cup, cut; firstorder. Qed.
Lemma cut_E_equiv x y : E0 b c d x y <-> cut I E x y.
Proof. unfold b, c, d, E, E0, F0, cup, cut; firstorder. Qed.
Lemma cut_F_equiv x y : F0 c d x y <-> cut I (F0 C D) x y.
Proof. unfold c, d, F0, cup, cut; firstorder. Qed.
Lemma I_backward x y : R x y -> I y -> I x.
Proof. intros H K; eapply bad_step; eauto. Qed.
Lemma cut_R_path x y : star R x y -> I y -> I x /\ star (R0 a b c d) x y.
Proof.
  intros H K; destruct (star_cut I R I_backward x y H K) as [L M].
  split; [exact L |]. eapply star_mono; [|exact M].
  intros u v W; apply cut_R_equiv; exact W.
Qed.
Lemma cut_E_path x y : star E x y -> I y -> I x /\ star (E0 b c d) x y.
Proof.
  intros H K.
  assert (Back : forall u v, E u v -> I v -> I u).
  { intros u v L Iv; eapply I_backward; [right; exact L |exact Iv]. }
  destruct (star_cut I E Back x y H K) as [L M].
  split; [exact L |]. eapply star_mono; [|exact M].
  intros u v W; apply cut_E_equiv; exact W.
Qed.
Lemma cut_B_plus x y : plus B x y -> I y -> I x /\ plus b x y.
Proof.
  intros H K. eapply plus_cut; [|exact H |exact K].
  intros u v L Iv; eapply I_backward; [right; left; exact L |exact Iv].
Qed.
Lemma cut_C_plus x y : plus C x y -> I y -> I x /\ plus c x y.
Proof.
  intros H K. eapply plus_cut; [|exact H |exact K].
  intros u v L Iv; eapply I_backward; [right; right; left; exact L |exact Iv].
Qed.
Lemma P0_restrict : P0 A B C D -> P0 a b c d.
Proof.
  intros H x y z Exy [Iy [Ayz Iz]].
  apply cut_E_equiv in Exy; destruct Exy as [Ix [Exy Iy']].
  destruct (H x y z Exy Ayz) as [[u [Axu Puz]] | Exz].
  - destruct (cut_R_path u z Puz Iz) as [Iu L].
    left; exists u; split; [unfold a, cut; auto |exact L].
  - right; apply cut_E_equiv; unfold cut; auto.
Qed.
Lemma P1_restrict : P1 A B C D -> P1 a b c d.
Proof.
  intros H x y z Fxy [Iy [Byz Iz]].
  apply cut_F_equiv in Fxy; destruct Fxy as [Ix [Fxy Iy']].
  destruct (H x y z Fxy Byz) as [[u [Axu Puz]] | [Bxz | Fxz]].
  - destruct (cut_R_path u z Puz Iz) as [Iu L].
    left; exists u; split; [unfold a, cut; auto |exact L].
  - right; left; exact (proj2 (cut_B_plus x z Bxz Iz)).
  - right; right; apply cut_F_equiv; unfold cut; auto.
Qed.
Lemma Q2_restrict : Q2 B C D -> Q2 b c d.
Proof.
  intros H x y z [Ix [Dxy Iy]] [Iy' [Cyz Iz]].
  destruct (H x y z Dxy Cyz) as [[u [Bxu Puz]] | [Cxz | Dxz]].
  - destruct (cut_E_path u z Puz Iz) as [Iu L].
    left; exists u; split; [unfold b, cut; auto |exact L].
  - right; left; exact (proj2 (cut_C_plus x z Cxz Iz)).
  - right; right; unfold d, cut; auto.
Qed.

Definition minimal_immortal x :=
  I x /\ forall y, A x y -> ~ I y.

Theorem finite_escape_target_termination :
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1 A B C D -> Q2 B C D ->
  (exists l : list X, forall x z,
     minimal_immortal x -> B x z -> I z -> In z l) ->
  WF R.
Proof.
  intros WA WB WC WD H0 H1 H2 [l Cover].
  apply NNPP; intro NotWF.
  destruct (not_wf_has_bad R NotWF) as [x Ix].
  assert (Wcut : forall P : rel X, WF P -> WF (cut I P)).
  { intros P W; eapply wf_mono; [|exact W]; unfold cut; firstorder. }
  eapply (serial_domain_finite_image_impossible a b c d I).
  - apply Wcut; exact WA.
  - apply Wcut; exact WB.
  - apply Wcut; exact WC.
  - apply Wcut; exact WD.
  - apply P0_restrict; exact H0.
  - apply P1_restrict; exact H1.
  - apply Q2_restrict; exact H2.
  - intros u v H; apply cut_R_equiv in H; unfold cut in H; tauto.
  - intros u Iu; destruct (bad_successor R u Iu) as [v [Ruv Iv]].
    exists v; apply cut_R_equiv; unfold cut; auto.
  - exists x; exact Ix.
  - exists l; intros z [u [[Iu Nu] [Iu' [Buz Iz]]]].
    apply (Cover u z); auto.
    split; [exact Iu |]. intros v Auv Iv.
    apply (Nu v); unfold a, cut; auto.
Qed.

Theorem finite_termination :
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1 A B C D -> Q2 B C D ->
  (exists l : list X, forall x, In x l) -> WF R.
Proof.
  intros WA WB WC WD H0 H1 H2 [l All].
  apply finite_escape_target_termination.
  - exact WA.
  - exact WB.
  - exact WC.
  - exact WD.
  - exact H0.
  - exact H1.
  - exact H2.
  - exists l; intros; apply All.
Qed.

Lemma cut_well_founded (P : rel X) : WF P -> WF (cut I P).
Proof.
  intro W; eapply wf_mono; [|exact W]. unfold cut; firstorder.
Qed.
Lemma cut_domain : forall x y, R0 a b c d x y -> I x /\ I y.
Proof.
  intros x y H; apply cut_R_equiv in H; unfold cut in H; tauto.
Qed.
Lemma cut_serial : forall x, I x -> exists y, R0 a b c d x y.
Proof.
  intros x Ix; destruct (bad_successor R x Ix) as [y [Rxy Iy]].
  exists y; apply cut_R_equiv; unfold cut; auto.
Qed.
Lemma cut_minimal_equiv x : M a I x <-> minimal_immortal x.
Proof.
  unfold M, minimal_immortal, normal, a, cut; firstorder.
Qed.
Lemma P1_strong_restrict : P1_strong A B C D -> P1_strong a b c d.
Proof.
  intros H x y z Fxy [Iy [Byz Iz]].
  apply cut_F_equiv in Fxy; destruct Fxy as [Ix [Fxy Iy']].
  destruct (H x y z Fxy Byz) as [[u [Axu Puz]] |Bxz].
  - destruct (cut_R_path u z Puz Iz) as [Iu L].
    left; exists u; split; [unfold a, cut; auto |exact L].
  - right; exact (proj2 (cut_B_plus x z Bxz Iz)).
Qed.

(** Exact uniform-height statement: the bound is needed only on A-minimal
    immortal points, and only for B-paths staying in the immortal set. *)
Theorem bounded_immortal_height_termination :
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1 A B C D -> Q2 B C D ->
  (exists h, forall x, minimal_immortal x -> height_le b h x) -> WF R.
Proof.
  intros WA WB WC WD H0 H1 H2 [h Bound].
  apply NNPP; intro N.
  destruct (not_wf_has_bad R N) as [x Ix].
  eapply (serial_domain_bounded_height_impossible a b c d I).
  - apply cut_well_founded; exact WA.
  - apply cut_well_founded; exact WC.
  - apply cut_well_founded; exact WD.
  - apply P0_restrict; exact H0.
  - apply P1_restrict; exact H1.
  - apply Q2_restrict; exact H2.
  - exact cut_domain.
  - exact cut_serial.
  - exists x; exact Ix.
  - exists h; intros u Hu. apply Bound; apply cut_minimal_equiv; exact Hu.
Qed.

Corollary bounded_height_termination :
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1 A B C D -> Q2 B C D ->
  (exists h, forall x, height_le B h x) -> WF R.
Proof.
  intros WA WB WC WD H0 H1 H2 [h Bound].
  apply bounded_immortal_height_termination; try assumption.
  exists h; intros x Mx.
  eapply (height_mono b B); [unfold b, cut; firstorder |apply Bound].
Qed.

(** Strengthens the manuscript's pointwise assertion from I_B to I_A. *)
Theorem minimal_immortal_unbounded :
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1_strong A B C D -> Q2 B C D ->
  forall x, minimal_immortal x -> forall n, long b n x.
Proof.
  intros WA WB WC WD H0 Hs H2 x Mx n.
  destruct n as [|n]; [constructor |].
  apply NNPP; intro Hbound.
  eapply (serial_domain_pointwise_height_impossible a b c d I).
  - apply cut_well_founded; exact WA.
  - apply cut_well_founded; exact WC.
  - apply cut_well_founded; exact WD.
  - apply P0_restrict; exact H0.
  - apply P1_restrict; apply P1_strong_implies; exact Hs.
  - apply Q2_restrict; exact H2.
  - exact cut_domain.
  - exact cut_serial.
  - apply P1_strong_restrict; exact Hs.
  - apply cut_minimal_equiv; exact Mx.
  - exact Hbound.
Qed.

Theorem pointwise_minimal_height_termination :
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1_strong A B C D -> Q2 B C D ->
  (forall x, minimal_immortal x -> exists h, height_le b h x) -> WF R.
Proof.
  intros WA WB WC WD H0 Hs H2 Bound.
  apply NNPP; intro N.
  destruct (not_wf_has_bad R N) as [x Ix].
  destruct (wf_minimum A I WA (ex_intro _ x Ix)) as [u [Iu Nu]].
  assert (Mu : minimal_immortal u) by (split; assumption).
  destruct (Bound u Mu) as [h Hh]. apply Hh.
  eapply minimal_immortal_unbounded; eauto.
Qed.

Corollary pointwise_height_termination :
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1_strong A B C D -> Q2 B C D ->
  (forall x, exists h, height_le B h x) -> WF R.
Proof.
  intros WA WB WC WD H0 Hs H2 Bound.
  apply pointwise_minimal_height_termination; try assumption.
  intros x Mx; destruct (Bound x) as [h Hh]; exists h.
  eapply (height_mono b B); [unfold b, cut; firstorder |exact Hh].
Qed.

Corollary finitely_branching_termination :
  WF A -> WF B -> WF C -> WF D ->
  P0 A B C D -> P1_strong A B C D -> Q2 B C D ->
  finitely_branching B -> WF R.
Proof.
  intros WA WB WC WD H0 Hs H2 Branch.
  apply pointwise_height_termination; try assumption.
  apply finitely_branching_wf_height; assumption.
Qed.

End Restriction.

Lemma well_founded_has_no_infinite_chain {X} (P : rel X) :
  WF P -> forall f : nat -> X, (forall n, P (f n) (f (Datatypes.S n))) -> False.
Proof.
  intros W f Chain.
  assert (H : forall x, Acc (flip P) x ->
      forall g : nat -> X, g 0 = x ->
      (forall n, P (g n) (g (Datatypes.S n))) -> False).
  { intros x A; induction A as [x K IH]. intros g Eq Edges.
    assert (Step : P x (g 1)).
    { rewrite <- Eq; exact (Edges 0). }
    exact (IH (g 1) Step (fun n => g (Datatypes.S n)) eq_refl
      (fun n => Edges (Datatypes.S n))). }
  eapply H; [apply W |reflexivity |exact Chain].
Qed.

Theorem finite_acyclic_four_relations {X} (A B C D : rel X) :
  (exists l : list X, forall x, In x l) ->
  (forall x, ~ plus A x x) -> (forall x, ~ plus B x x) ->
  (forall x, ~ plus C x x) -> (forall x, ~ plus D x x) ->
  P0 A B C D -> P1 A B C D -> Q2 B C D ->
  WF (R0 A B C D).
Proof.
  intros Fin AA AB AC AD H0 H1 H2.
  apply (finite_termination A B C D).
  - apply finite_acyclic_wf; assumption.
  - apply finite_acyclic_wf; assumption.
  - apply finite_acyclic_wf; assumption.
  - apply finite_acyclic_wf; assumption.
  - exact H0.
  - exact H1.
  - exact H2.
  - exact Fin.
Qed.

