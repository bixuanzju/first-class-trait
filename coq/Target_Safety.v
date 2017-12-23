
Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import Infrastructure target_inf.




Lemma typing_weaken : forall G E F t T,
   (E ++ G) |= t ~: T ->
   uniq (E ++ F ++ G) ->
   (E ++ F ++ G) |= t ~: T.
Proof.
  introv Typ; inductions Typ; introv Ok; autos*.
  pick fresh x and apply typ_abs.
  rewrite_env (([(x, T1)] ++ E) ++ F ++ G).
  apply~ H0.
  solve_uniq.
Qed.

Lemma typing_weakening : forall (E F : ctx) e T,
    typing E e T ->
    uniq (F ++ E) ->
    typing (F ++ E) e T.
Proof.
  intros E F e T H J.
  rewrite_env (nil ++ F ++ E).
  apply~ typing_weaken.
Qed.


(** Typing is preserved by substitution. *)


Lemma typing_subst : forall (E F : ctx) e u S T (z : atom),
  typing (F ++ [(z,S)] ++ E) e T ->
  typing E u S ->
  typing (F ++ E) ([z ~> u] e) T.
Proof.
  intros.
  remember (F ++ [(z,S)] ++ E) as E'.
  generalize dependent F.
  induction H; intros F Eq; subst; simpl; autos*.

  case_if*.
  substs.
  assert (T = S).
  eapply binds_mid_eq; eauto.
  substs.
  apply~ typing_weakening.
  solve_uniq.

  pick fresh x and apply typ_abs.
  rewrite subst_exp_open_exp_wrt_exp_var; auto.
  rewrite_env (([(x, T1)] ++ F) ++ E).
  apply~ H1.
Qed.

Lemma prod_canonical : forall t T1 T2,
    value t ->
    nil |= t ~: a_prod T1 T2 ->
    exists t1 t2, value t1 /\ value t2 /\ t = trm_pair t1 t2.
Proof.
  introv Val Typ. lets Typ' : Typ. inductions Typ; inverts* Val.
  inverts H.
  inverts H.
  inverts H.
Qed.

Lemma unit_canonical : forall t,
    value t ->
    nil |= t ~: a_unit ->
    t = trm_unit.
Proof.
  introv Val Typ. lets Typ' : Typ. inductions Typ; inverts* Val.
  inverts H.
  inverts H.
  inverts H.
Qed.


Lemma rcd_canonical : forall t l T,
    value t ->
    nil |= t ~: a_rcd l T ->
    exists t', t = trm_rcd l t'.
Proof.
  introv Val Typ. lets Typ' : Typ. inductions Typ; inverts* Val.
  inverts H.
  inverts H.
  inverts H.
Qed.


(** Preservation (typing is preserved by reduction). *)

Theorem preservation : forall G t t' T,
  G |= t ~: T ->
  step t t' ->
  G |= t' ~: T.
Proof.

  introv H; gen t'.
  inductions H; try solve [introv J; inverts* J].

  - Case "typing_app".
    introv J. inverts* J.

    inverts* H.
    inverts* H6.

    inverts* H.
    inverts* H8.

    inverts* H.
    inverts* H9.
    inverts* H7.

    inverts* H.
    pick fresh x.
    rewrite* (@subst_exp_intro x).
    rewrite_env (nil ++ G).
    sapply* typing_subst.

  - Case "typing_capp".
    introv J. inverts J; try solve [inverts* H0].

    inverts H.
    inverts* H0.

    inverts H.
    inverts* H0.

    inverts H.
    inverts* H0.

    inverts H.
    inverts* H0.
    inverts* H6.
    inverts* H8.


  - Case "typing_proj".
    introv J.
    inverts* J.
    inverts* H.
Qed.




Theorem progress : forall t T,
  nil |= t ~: T ->
  value t \/ exists t', step t t'.
Proof.
  introv Typ. lets Typ': Typ. inductions Typ; try solve [left*].
  (* var case *)
  - invert H0.
  (* app case *)
  - right.
    destruct~ IHTyp1 as [Val1 | [t1' Red1]].
    destruct~ IHTyp2 as [Val2 | [t2' Red2]].
    inverts Typ1; inverts Val1.
    exists* (e ^^ e2).
    exists* (trm_capp c2 (trm_app e (trm_capp c1 e2))).
    inverts* H0.
    lets* (? & ? & ? & ? & ?) : prod_canonical H.
    substs*.


    inverts* H0.
    lets* : unit_canonical Typ2.
    substs.
    lets* : unit_canonical H.
    substs.
    exists* trm_unit.

    exists* (trm_app e1 t2').
    exists* (trm_app t1' e2).
  (* pair case *)
  - destruct~ IHTyp1 as [Val1 | [t1' Red1]].
    destruct~ IHTyp2 as [Val2 | [t2' Red2]].
    right*. right*.

  - Case "capp".

    destruct~ IHTyp as [Val | [t1' Red1]].
    inverts* H.
    lets H: prod_canonical Val Typ.
    destruct H as [t1 [t2 [Val1 [Val2 VPair]]]].
    right*.
    subst*.
    lets H: prod_canonical Val Typ.
    destruct H as [t1 [t2 [Val1 [Val2 VPair]]]].
    right*.
    subst*.

    lets (? & ?)  : rcd_canonical Val Typ.
    substs.
    inverts Val.
    right*.

    lets : unit_canonical Val Typ.
    substs.
    right*.


    lets H: prod_canonical Val Typ.
    destruct H as [t1 [t2 [Val1 [Val2 VPair]]]].
    substs.
    inverts Typ.
    lets (? & ?)  : rcd_canonical Val1 H3.
    lets (? & ?)  : rcd_canonical Val2 H5.
    substs.
    inverts Val.
    inverts H1.
    inverts H2.

    right*.

    right*.




  - Case "trm_rcd".
    destruct~ IHTyp as [Val | [t1' Red1]].
    right*.

  - Case "trm_projRcd".
    destruct~ IHTyp as [Val | [t1' Red1]].
    lets H: rcd_canonical Val Typ.
    destruct H as (v & ?).
    substs.
    right*.
    inverts Val.
    exists~ v.
    right*.

Qed.


Theorem preservation_multi_step : forall t t' T,
    nil |= t ~: T ->
    t ->* t' ->
    nil |= t' ~: T.
Proof.
  introv Typ Red.
  induction* Red.
  lets*: preservation Typ H.
Qed.


Theorem type_safety : forall t t' T,
    nil |= t ~: T ->
    t ->* t' ->
    value t' \/ exists t'', step t' t''.
Proof.
  introv Typ Red.
  induction Red.
  lets* : progress Typ.
  lets* Res : preservation Typ H.
Qed.
