
Require Import LibTactics.
Require Import Metalib.Metatheory.


Require Import
        Target_Safety
        target_inf
        Infrastructure
        Logical_Relation_Def
        Source_Property
        Target_Adequacy
        Normalize.


Lemma bind_capp : forall s c t,
    bind s (trm_capp c t) = trm_capp c (bind s t).
Proof.
  intros s; induction s; intros.
  reflexivity.
  simpls*.
Qed.


Lemma bind_app : forall s t1 t2,
    bind s (trm_app t1 t2) = trm_app (bind s t1) (bind s t2).
Proof.
  intros s; induction s; intros.
  reflexivity.
  simpls*.
Qed.


Lemma bind_pair : forall s t1 t2,
    bind s (trm_pair t1 t2) = trm_pair (bind s t1) (bind s t2).
Proof.
  intros s; induction s; intros.
  reflexivity.
  simpls*.
Qed.


Lemma bind_abs : forall s t,
    bind s (trm_abs t) = trm_abs (bind s t).
Proof.
  intros s; induction s; intros.
  reflexivity.
  simpls*.
Qed.

Lemma bind_rcd : forall s t l,
    bind s (trm_rcd l t) = trm_rcd l (bind s t).
Proof.
  intros s; induction s; intros.
  reflexivity.
  simpls*.
Qed.

Lemma bind_proj : forall s t l,
    bind s (trm_proj t l) = trm_proj (bind s t) l.
Proof.
  intros s; induction s; intros.
  reflexivity.
  simpls*.
Qed.



Lemma rel_v_relates_values : forall T1 T2 v1 v2,
  rel_v T1 T2 v1 v2 -> value v1 /\ value v2.
Proof.
  introv Rel; destruct* T1; destruct* T2; simpls*.
Qed.

Lemma rel_v_well_type : forall T1 T2 v1 v2,
  rel_v T1 T2 v1 v2 -> nil |= v1 ~: T1 /\ nil |= v2 ~: T2.
Proof.
  introv Rel; destruct* T1; destruct* T2; simpls*.
Qed.

Lemma rel_g_regular : forall G1 G2 g1 g2,
    rel_g G1 G2 g1 g2 ->
    uniq G1 /\ uniq G2.
Proof.
  introv Rel.
  induction~ Rel.
  splits*.
Qed.



Hint Extern 1 (value ?v) =>
  match goal with
  | H: rel_v _ _ v _ |- _ => apply (proj1 (rel_v_relates_values _ _ _ _ H))
  | H: rel_v _ _ _ v |- _ => apply (proj2 (rel_v_relates_values _ _ _ _ H))
  end.

Hint Extern 1 (uniq ?G) =>
  match goal with
  | H: rel_g G _ _ _ |- _ => apply (proj1 (rel_g_regular _ _ _ _ H))
  | H: rel_g _ G _ _ |- _ => apply (proj2 (rel_g_regular _ _ _ _ H))
  end.

Hint Extern 1 (lc_exp ?v) =>
  match goal with
  | H: rel_v _ _ v _ |- _ => apply (value_regular (proj1 (rel_v_relates_values _ _ _ _ H)))
  | H: rel_v _ _ _ v |- _ => apply (value_regular (proj2 (rel_v_relates_values _ _ _ _ H)))
  end.


Lemma bind_value : forall g v,
    fv_exp v [=] {} ->
    bind g v = v.
Proof.
  intros.
  induction g.
  reflexivity.
  simpl.
  rewrite* subst_exp_fresh_eq.
  fsetdec.
Qed.



Lemma rel_g_well_type_value : forall G1 G2 g1 g2,
    rel_g G1 G2 g1 g2 ->
    all_value g1 /\ all_value g2.
Proof.
  introv GG.
  induction GG; splits*; forwards * : rel_v_well_type.
Qed.

Lemma bind_subst_open : forall g t a,
    all_value g ->
    fv_exp a [=] {} ->
    bind g (t ^^ a) = (bind g t) ^^ a.
Proof.
  intro g.
  induction g; intros; autos.
  destruct a as [x T].
  simpls.
  inverts H.
  rewrite~ <- IHg.
  rewrite~ subst_exp_open_exp_wrt_exp.
  rewrite subst_exp_fresh_eq with (e2 := a0); auto.
  rewrite H0.
  apply notin_empty.
Qed.

Lemma bind_subst : forall g x a t,
    all_value ([(x , a)] ++ g) ->
    x \notin fv_exp t ->
    bind ([(x , a)] ++ g) (t ^ x) = (bind g t) ^^ a.
Proof.
  intros.
  inverts H.
  simpl.
  rewrite* <- bind_subst_open.
  rewrite* <- subst_exp_intro.
  sapply* value_no_fv.
Qed.


Lemma bind_close : forall G1 G2 g1 g2 t1 t2 T1 T2,
    G1 |= t1 ~: T1 ->
    G2 |= t2 ~: T2 ->
    rel_g G1 G2 g1 g2 ->
    nil |= bind g1 t1 ~: T1 /\ nil |= bind g2 t2 ~: T2.
Proof.
  introv Ty1 Ty2 GG.
  gen T1 T2 t1 t2.
  induction GG; introv Rel1 Rel2.
  simpls*.
  lets* [Val1 Val2]: rel_v_relates_values.
  lets* [Ty1' Ty2']: rel_v_well_type.
  asserts Ty1 : (G1 |= [x ~> v1] t1 ~: T0).
  rewrite_env (nil ++ G1).
  sapply* typing_subst.
  rewrite_env (nil ++ G1 ++ nil).
  sapply* typing_weaken.
  asserts Ty2: (G2 |= [x ~> v2] t2 ~: T3).
  rewrite_env (nil ++ G2).
  sapply* typing_subst.
  rewrite_env (nil ++ G2 ++ nil).
  sapply* typing_weaken.
  forwards * [? ?]: IHGG Ty1 Ty2.
Qed.

Lemma rel_e_well_type : forall T1 T2 t1 t2,
  rel_e T1 T2 t1 t2 -> nil |= t1 ~: T1 /\ nil |= t2 ~: T2.
Proof.
  intros.
  destructs H.
  auto.
Qed.


Lemma rel_v_proj1' : forall v v' T T1 T2,
    rel_v (a_prod T1 T2) T v v' <->
    value v /\ value v' /\ rel_e T1 T (trm_capp co_proj1 v) v' /\ rel_e T2 T (trm_capp co_proj2 v) v'.
Proof.
  intros; splits.


  - destruct T; intros H.
    + destructs H; lets* : prod_canonical H1.
      splits*.
      splits*.
      splits*.
    + destructs H; lets* : prod_canonical H1.
      splits*.
      splits*.
      splits*.
    + destructs H; lets* : prod_canonical H1.
      splits*.
      splits*.
      splits*.
    + destructs H; lets* : prod_canonical H1.
      splits*.
      splits*.
      splits*.
    + destructs H; lets* : prod_canonical H1.
      splits*.
      splits*.
      splits*.

  - destruct T; intros H.
    + destruct H as (Val & ? & Rel1 & Rel2).
      destructs Rel1.
      destructs Rel2.
      splits*.
      forwards * : pair_type Val.
    + destruct H as (Val & ? & Rel1 & Rel2).
      destructs Rel1.
      destructs Rel2.
      splits*.
      forwards * : pair_type Val.
    + destruct H as (Val & ? & Rel1 & Rel2).
      destructs Rel1.
      destructs Rel2.
      splits*.
      forwards * : pair_type Val.
    + destruct H as (Val & ? & Rel1 & Rel2).
      destructs Rel1.
      destructs Rel2.
      splits*.
      forwards * : pair_type Val.
    + destruct H as (Val & ? & Rel1 & Rel2).
      destructs Rel1.
      destructs Rel2.
      splits*.
      forwards * : pair_type Val.
Qed.


Ltac my_simplfier :=
  repeat match goal with
         | H : grel_e _ _ _ |- _ => destruct H as (? & ? & ? & ? & ? & ? & ?)
         | H : rel_e _ _ _ _ |- _ => destruct H as (? & ? & ?)
         | H : ?v ->* ?v', V1 : value ?v, V2 : value ?v' |- _ =>
           apply value_no_step in H; autos; substs
         | H1 : ?t ->* ?v1, H2 : ?t ->* ?v2, V1 : value ?v1, V2 : value ?v2 |- _ =>
           lets* : value_unique H1 H2; substs; clear H1
         | H : ?t2 ->* ?v2, V1 : value ?v, V2 : value ?v2
           |- rel_e _ _ ?v ?t2 => splits*; exists* v v2; splits*
         | H : ?t2 ->* ?v2, V1 : value ?v, V2 : value ?v2
           |- rel_e _ _ ?t2 ?v => splits*; exists* v2 v; splits*
         | H : ?t2 ->* ?v2, V1 : value ?v, V2 : value ?v2
           |- grel_e _ ?v ?t2 => exists* v v2; splits*
         | H : ?t2 ->* ?v2, V1 : value ?v, V2 : value ?v2
           |- grel_e _ ?t2 ?v => exists* v2 v; splits*
         | |- rel_v (a_prod _ _) _ _ _ =>  apply rel_v_proj1'; splits*
         | H : rel_v (a_prod _ _) _ _ _ |- _ =>
           apply rel_v_proj1' in H ; destructs H
         (* | H1 : ?G1 |= _ ~: _, H2 : ?G2 |= _ ~: _, H3 : rel_g ?G1 ?G2 _ _ |- _ => *)
         (*   lets [? ?] : bind_close H1 H2 H3 *)
         end.

Lemma rel_e_redr : forall t t' T T' d,
    rel_e T T' t d ->
    d ->* t' ->
    rel_e T T' t t'.
Proof.
  intros.
  my_simplfier.
  lets : preservation_multi_step H2 H0.
  lets (v & ? & ?): normalization H7.
  assert (d ->* v).
  sapply* star_trans.
  unfolds.
  splits*.
  exists x v; splits*.
  asserts_rewrite* (v = x0).
  apply value_unique with (t := d); autos.
Qed.

Lemma rel_e_redl : forall t t' T T' d,
    rel_e T T' d t' ->
    d ->* t ->
    rel_e T T' t t'.
Proof.
  intros.
  my_simplfier.
  lets : preservation_multi_step H1 H0.
  lets (v & ? & ?): normalization H7.
  assert (d ->* v).
  sapply* star_trans.
  splits*.
  exists v x0; splits*.
  asserts_rewrite* (v = x).
  apply value_unique with (t := d); autos.
Qed.


Lemma rel_e_convr : forall t t' T T' d,
    rel_e T T' t t' ->
    nil |= d ~: T' ->
    d ->* t' ->
    rel_e T T' t d.
Proof.
  intros.
  my_simplfier.
  assert (d ->* x0).
  sapply* star_trans.
  splits*.
  exists x x0; splits*.
Qed.


Lemma rel_e_convl : forall t t' T T' d,
    rel_e T T' t t' ->
    nil |= d ~: T ->
    d ->* t ->
    rel_e T T' d t'.
Proof.
  intros.
  my_simplfier.
  assert (d ->* x).
  sapply* star_trans.
  splits*.
  exists x x0; splits*.
Qed.

Lemma rel_e_grel : forall T T' t t',
    rel_e T T' t t' ->
    grel_e (rel_v T T') t t'.
Proof.
  introv H.
  destruct* H.
Qed.

Lemma rel_e_open_cl : forall T1 T2 t1 t2,
  (rel_e_open nil nil t1 t2 T1 T2) <-> (rel_e T1 T2 t1 t2).
Proof.
  intros.
  splits.
  intros.
  destructs H.
  specialize (H1 nil nil).
  simpls.
  apply~ H1.

  intros.
  lets : rel_e_well_type H.
  splits*.
  intros.
  inverts* H1.
Qed.

Lemma rel_e_in_rel_v : forall T1 T2 t1 t2,
    value t1 -> value t2 ->
    rel_e T1 T2 t1 t2 ->
    rel_v T1 T2 t1 t2.
Proof.
  intros.
  my_simplfier; auto.
Qed.

Lemma rel_v_in_rel_e : forall T1 T2 t1 t2,
  rel_v T1 T2 t1 t2 -> rel_e T1 T2 t1 t2.
Proof.
  intros.
  lets : rel_v_well_type H.
  splits*.
  exists* t1 t2.
Qed.


Lemma rel_v_proj2' : forall v v' T T1 T2,
    rel_v T (a_prod T1 T2) v v' <->
    value v /\ value v' /\ rel_e T T1 v (trm_capp co_proj1 v') /\ rel_e T T2 v (trm_capp co_proj2 v').
Proof.
  intros.
  splits; intros H.
  - gen v.
    induction T; intros.
    + destruct H as (? & ? & ? & ? & ? & ?).
      splits*; splits*.
    + destruct H as (? & ? & ? & ? & ? & ?).
      splits*; splits*.
    + destruct H as (? & ? & ? & ? & ? & ?).
      splits*; splits*.
    + destruct H as (? & ? & ? & ? & ? & ?).
      my_simplfier.
      forwards* (? & ? & ? & ?): IHT1.
      forwards* (? & ? & ? & ?): IHT2.
      my_simplfier.
      lets [? ?] : rel_v_well_type H30.
      lets [? ?] : rel_v_well_type H24.
      splits*; my_simplfier.
    + destruct H as (? & ? & ? & ? & ? & ?).
      splits*; splits*.


  - gen v.
    induction T; introv H; destruct H as (? & Val & Rel1 & Rel2).
    + my_simplfier.
      forwards * : pair_type Val.
      splits*; my_simplfier.
    + my_simplfier.
      forwards * : pair_type Val.
      splits*; my_simplfier.
    + my_simplfier.
      forwards * : pair_type Val.
      splits*; my_simplfier.
    + my_simplfier.

      lets [? ?]: rel_v_well_type H26.
      forwards * : pair_type Val.
      my_simplfier.
      apply IHT1.
      splits*; my_simplfier.


      lets [? ?]: rel_v_well_type H20.
      forwards * : pair_type Val.
      my_simplfier.
      apply IHT2.
      splits*; my_simplfier.

    + my_simplfier.
      forwards * : pair_type Val.
      splits*; my_simplfier.
Qed.


Lemma rel_v_proj1 : forall v v1 v2 T T1 T2,
    rel_v (a_prod T1 T2) T (trm_pair v1 v2) v <->
    rel_v T1 T v1 v /\ rel_v T2 T v2 v.
Proof.
  intros.
  splits; introv H.

  apply rel_v_proj1' in H.
  destruct H as (Val & ? & Rel1 & Rel2).
  inverts Val.
  apply rel_e_redl with (t := v1) in Rel1; autos.
  apply rel_e_redl with (t := v2) in Rel2; autos.
  apply rel_e_in_rel_v in Rel1; autos.
  apply rel_e_in_rel_v in Rel2; autos.

  destruct H as [Imp1 Imp2].
  lets [? ?]: rel_v_well_type Imp1.
  lets [? ?]: rel_v_well_type Imp2.
  my_simplfier.
  splits*.
  exists* v1 v.
  splits*.
  exists* v2 v.
Qed.


Lemma rel_v_proj2 : forall v v1 v2 T T1 T2,
    rel_v T (a_prod T1 T2) v (trm_pair v1 v2) <->
    rel_v T T1 v v1 /\ rel_v T T2 v v2.
Proof.
  intros.
  splits; intros H.
  apply rel_v_proj2' in H.
  destruct H as (? & Val & Rel1 & Rel2).
  inverts Val.
  apply rel_e_redr with (t' := v1) in Rel1; autos.
  apply rel_e_redr with (t' := v2) in Rel2; autos.
  apply rel_e_in_rel_v in Rel1; autos.
  apply rel_e_in_rel_v in Rel2; autos.

  gen v.
  induction T; introv H; destruct H as (Rel1 & Rel2);
    lets [? ?] : rel_v_well_type Rel1;
    lets [? ?] : rel_v_well_type Rel2;
    try solve [splits*; [exists* v v1 | exists* v v2]].

  assert (value (trm_pair v1 v2)) by auto.
  my_simplfier.
  apply IHT1.
  splits*.
Qed.

Lemma rel_v_unit : forall v v' T,
    value v -> value v' ->
    nil |= v' ~: T ->
    nil |= v ~: a_unit ->
    rel_v a_unit T v v'.
Proof.
  intros.
  gen v'.
  inductions T; introv ? Typ; try solve [simpls*].
  lets* (? & ? & ? & ? & ?) : prod_canonical Typ.
  substs.
  inverts Typ.
  sapply* rel_v_proj2.
Qed.

Lemma rel_v_unit2 : forall v v' T,
    value v -> value v' ->
    nil |= v ~: T ->
    nil |= v' ~: a_unit ->
    rel_v T a_unit v v'.
Proof.
  intros.
  gen v.
  inductions T; introv ? Typ; try solve [simpls*].
  lets* (? & ? & ? & ? & ?) : prod_canonical Typ.
  substs.
  inverts Typ.
  sapply* rel_v_proj1.
Qed.



Lemma rel_v_rcd : forall v v' T T' l,
    rel_v (a_rcd l T) (a_rcd l T') (trm_rcd l v) (trm_rcd l v') <->
    value v /\ value v' /\ rel_v T T' v v'.
Proof.
  intros. splits.


  - Case "->".
    introv H.
    destructs H.
    inverts H.
    inverts H0.
    inverts H1.
    inverts H2.
    case_if*.
    destruct H3 as (v1 & v2 & ? & ? & ? & ? & ?).
    assert (trm_proj (trm_rcd l v) l ->* v) by auto.
    assert (trm_proj (trm_rcd l v') l ->* v') by auto.
    my_simplfier.

    splits*.



  - Case "<-".
    introv H.
    destructs H.
    lets (? & ?): rel_v_well_type H1.
    simpl.
    splits*.
    case_if*.
    exists v v'.
    splits*.
Qed.



Lemma context_well_type : forall Γ Γ' E A A' e dir dir' C c,
    CTyp C Γ dir A Γ' dir' A' c ->
    has_type Γ E dir A e ->
    ∥ Γ' ∥ |= (appctx c e) ~: |A'|.
Proof.
  introv Typ. gen E e.
  induction Typ; intros; simpls*; lets* : elaboration_well_type_term.

  lets* : elaboration_well_type_term H.
  lets* : elaboration_well_type_term H.

  - Case "trm_abs1".
    lets : IHTyp H0.
    set (ee :=  appctx cc5 e).
    pick fresh y and apply typ_abs.
    apply typing_rename with (x := x).
    rewrite open_exp_wrt_exp_close_exp_wrt_exp.
    rewrite_env ((x, | A1 |) :: ∥ GG' ∥); auto.
    assert (x `notin` dom (∥ GG' ∥)). apply~ notin_trans.
    assert (x `notin` (fv_exp (close_exp_wrt_exp x (appctx cc5 e)))).
    rewrite fv_exp_close_exp_wrt_exp. solve_uniq. solve_notin.
    rewrite fv_exp_close_exp_wrt_exp.
    solve_notin.
  - Case "trm_abs2".
    lets : IHTyp H0.
    set (ee :=  appctx cc5 e).
    pick fresh y and apply typ_abs.
    apply typing_rename with (x := x).
    rewrite open_exp_wrt_exp_close_exp_wrt_exp.
    rewrite_env ((x, | A1 |) :: ∥ GG' ∥); auto.
    assert (x `notin` dom (∥ GG' ∥)). apply~ notin_trans.
    assert (x `notin` (fv_exp (close_exp_wrt_exp x (appctx cc5 e)))).
    rewrite fv_exp_close_exp_wrt_exp. solve_uniq. solve_notin.
    rewrite fv_exp_close_exp_wrt_exp.
    solve_notin.
Qed.
