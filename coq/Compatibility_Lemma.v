
Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        Infrastructure
        Target_Adequacy
        Logical_Relation_Def
        Logical_Relation_Infrastructure
        Target_Safety
        Normalize.


Lemma disjoint_rel_v : forall A1 A2 v1 v2,
    disjoint A1 A2 ->
    nil |= v1 ~: (|A1|) ->
    nil |= v2 ~: (|A2|) ->
    value v1 ->
    value v2 ->
    rel_v (|A1|) (|A2|) v1 v2.
Proof.
  introv Dis. gen v1 v2.
  induction Dis; introv Ty1 Ty2 Val1 Val2; try solve [simpls*].

  apply~ rel_v_unit.
  apply~ rel_v_unit2.

  simpls.
  splits*.
  introv Rel.
  lets [? ?] : rel_v_well_type Rel.
  assert (HH1 : nil |= (trm_app v1 a1) ~: | A2 |) by autos*.
  assert (HH2 : nil |= (trm_app v2 a2) ~: | B2 |) by autos*.
  lets (v3 & ? & Red1): normalization HH1.
  lets (v3' & ? & Red2): normalization HH2.
  lets* : preservation_multi_step Red1.
  lets* : preservation_multi_step Red2.
  exists* v3 v3'.

  lets* (v1' & v2' & ? & ? & ?) : prod_canonical Ty1.
  substs.
  inverts Ty1.
  apply rel_v_proj1. splits*.

  lets* (v1' & v2' & ? & ? & ?) : prod_canonical Ty2.
  substs.
  inverts Ty2.
  apply rel_v_proj2. splits*.


  (* recrds *)
  simpls.
  splits*.
  lets* (v1' & ?): rcd_canonical Val1 Ty1.
  lets* (v2' & ?): rcd_canonical Val2 Ty2.
  substs.
  case_if*.
  inverts Val1.
  inverts Val2.
  inverts Ty1.
  inverts Ty2.
  exists~ v1' v2'.
  splits*.
  simpls.
  splits*.
  case_if*.
Qed.


Lemma disjoint_rel_e_open : forall G1 G2 t1 t2 T1 T2,
    G1 |= t1 ~: | T1 | ->
    G2 |= t2 ~: | T2 | ->
    disjoint T1 T2 ->
    rel_e_open G1 G2 t1 t2 (| T1 |)  (| T2 |).
Proof.
  introv Ty1 Ty2 Dis.
  splits*.
  introv GG.
  lets (HH1 & HH2): bind_close  Ty1 Ty2 GG.
  lets (v1 & ? & ?): normalization HH1.
  lets (v2 & ? & ?): normalization HH2.
  lets* : preservation_multi_step H0.
  lets* : preservation_multi_step H2.
  splits*.
  exists~ v1 v2.
  splits*.
  apply~ disjoint_rel_v.
Qed.




Lemma compat_var : forall G1 G2 x A1 A2,
    uniq G1 -> uniq G2 -> binds x A1 G1 -> binds x A2 G2 ->
    rel_e_open G1 G2 (trm_var_f x) (trm_var_f x) A1 A2.
Proof.
  intros.
  unfolds.
  splits*.
  introv GG.
  (* gen A1 A2. *)
  induction GG.
  invert H1.

  simpls.
  lets [[? [? ?]]|[? ?]] : binds_cons_uniq_1 H H1; substs;
    lets [[? [? ?]]|[? ?]] : binds_cons_uniq_1 H0 H2; substs; tryfalse; case_if*.

  lets* [? ?]: rel_v_well_type H5.
  repeat rewrite* bind_value; try (sapply* value_no_fv).
  apply~ rel_v_in_rel_e.
Qed.


Lemma compat_unit1 : forall G1 G2 t T,
    G2 |= t ~: T -> uniq G1 -> rel_e_open G1 G2 trm_unit t a_unit T.
Proof.
  introv H ?.
  unfolds.
  splits*.
  introv GG.
  assert (HH : G1 |= trm_unit ~: a_unit) by auto.
  lets (? & HH1): bind_close HH H GG.
  lets (v & ? & H3): normalization HH1.
  lets : preservation_multi_step HH1 H3.
  rewrite* bind_value; try solve [simpl; fsetdec].
  splits*.
  exists trm_unit v.
  splits*.
  apply~ rel_v_unit.
Qed.


Lemma compat_unit2 : forall G1 G2 t T,
    G2 |= t ~: T -> uniq G1 -> rel_e_open G2 G1 t trm_unit T a_unit.
Proof.
  introv H ?.
  unfolds.
  splits*.
  introv GG.
  assert (HH : G1 |= trm_unit ~: a_unit) by auto.
  lets (HH1 & ?): bind_close H HH GG.
  lets (v & ? & H3): normalization HH1.
  lets : preservation_multi_step HH1 H3.
  (* rewrite* bind_value; try solve [simpl; fsetdec]. *)
  splits*.
  exists v trm_unit.
  splits*.
  rewrite* bind_value; try solve [simpl; fsetdec].
  apply~ rel_v_unit2.
Qed.


Lemma compat_int : forall G i,
    uniq G -> rel_e_open G G (trm_lit i) (trm_lit i) a_nat a_nat.
Proof.
  intros.
  unfolds.
  splits*.
  introv GG.
  repeat rewrite* bind_value; try solve [simpl; fsetdec].
  apply~ rel_v_in_rel_e.
  splits*.
Qed.

Lemma compat_app : forall G1 G2 t1 t2 t3 t4 T1 T2 T1' T2',
    rel_e_open G1 G2 t1 t2 (a_arrow T1 T1') (a_arrow T2 T2') ->
    rel_e_open G1 G2 t3 t4 T1 T2 ->
    rel_e_open G1 G2 (trm_app t1 t3) (trm_app t2 t4) T1' T2'.
Proof.
  introv Rel1 Rel2.
  destruct Rel1 as (HH1 & HH2 & Rel1).
  destruct Rel2 as (HH3 & HH4 & Rel2).
  splits*.
  introv GG.
  lets Rel1' : Rel1 GG.
  lets Rel2' : Rel2 GG.
  repeat rewrite bind_app.
  destruct Rel1' as (Rel1' & ? & ?).
  destruct Rel1' as (v1 & v1' & ? & ? & Red1 & Red1' & Rel1').
  destruct Rel2' as (Rel2' & ? & ?).
  destruct Rel2' as (v2 & v2' & ? & ? & Red2 & Red2' & Rel2').
  lets [? ?]: bind_close HH1 HH2 GG.
  lets [? ?]: bind_close HH3 HH4 GG.
  apply rel_e_convr with (t' := trm_app v1' v2'); auto_star.
  apply rel_e_convl with (t := trm_app v1 v2); auto_star.
  destruct Rel1' as (? & ? & ? & ? & Rel1').
  lets [? ?]: bind_close HH3 HH4 GG.
  lets* : preservation_multi_step Red2.
  lets* : preservation_multi_step Red2'.
  forwards * : Rel1' Rel2'.

  splits*.
  apply star_trans with (b := trm_app v1 (bind g1 t3)).
  apply~ multi_red_app2.
  apply~ multi_red_app.
  apply star_trans with (b := trm_app v1' (bind g2 t4)).
  apply~ multi_red_app2.
  apply~ multi_red_app.
Qed.


Lemma compat_pair1 : forall G1 G2 T1 T2 T3 t1 t2 t3,
    rel_e_open G1 G2  (trm_pair t1 t2) t3 (a_prod T1 T2) T3 <->
    rel_e_open G1 G2 t1 t3 T1 T3 /\
    rel_e_open G1 G2 t2 t3 T2 T3.
Proof.
  intros.
  splits.
  introv H.

  - Case "->".
    destruct H as (H & ? & ?).
    splits.

    inverts H.
    splits*.
    introv GG.
    lets : H1 GG.
    rewrite bind_pair in H.
    destruct H as (HH & Ty1 & Ty2).
    inverts Ty1.
    lets* (v1 & ? & ?): normalization H5.
    lets* (vv & ? & ?): normalization Ty2.
    lets* (v2 & ? & ?): normalization H9.
    destruct HH as (vv1 & ? & ? & ? & ? & ? & Imp).
    lets (? & ?) : rel_v_well_type Imp.
    lets* (v1' & v2' & ? & ? & ?) : prod_canonical H15.
    substs.
    assert (trm_pair (bind g1 t1) (bind g1 t2) ->* trm_pair v1 v2).
    sapply* multi_red_pair.
    lets* : value_unique H13 H19.
    inverts H20.
    apply rel_v_proj1 in Imp.
    destruct Imp.
    my_simplfier.
    splits*.
    exists v1 vv.
    splits*.

    inverts H.
    splits*.
    introv GG.
    lets : H1 GG.
    rewrite bind_pair in H.
    destruct H as (HH & Ty1 & Ty2).
    inverts Ty1.
    lets* (v1 & ? & ?): normalization H5.
    lets* (vv & ? & ?): normalization Ty2.
    lets* (v2 & ? & ?): normalization H9.
    destruct HH as (vv1 & ? & ? & ? & ? & ? & Imp).
    lets (? & ?) : rel_v_well_type Imp.
    lets* (v1' & v2' & ? & ? & ?) : prod_canonical H15.
    substs.
    assert (trm_pair (bind g1 t1) (bind g1 t2) ->* trm_pair v1 v2).
    sapply* multi_red_pair.
    lets* : value_unique H13 H19.
    inverts H20.
    apply rel_v_proj1 in Imp.
    destruct Imp.
    my_simplfier.
    splits*.
    exists v2 vv.
    splits*.

  - Case "<-".
    introv H.
    destruct H as (H1 & H2).
    destruct H1 as (? & ? & Imp1).
    destruct H2 as (? & ? & Imp2).
    splits*.
    introv GG.
    lets Imp1' : Imp1 GG.
    lets Imp2' : Imp2 GG.
    clear Imp1 Imp2.
    destruct Imp1' as (Imp1' & ? & ?).
    destruct Imp1' as (v1 & ? & ? & ? & ? & ? & Imp1').
    destruct Imp2' as (Imp2' & ? & ?).
    destruct Imp2' as (v2 & ? & ? & ? & ? & ? & Imp2').
    my_simplfier.

    rewrite bind_pair.
    splits*.
    exists (trm_pair v1 v2) x0.
    splits*.
    sapply* multi_red_pair.
    apply rel_v_proj1.
    splits~.
Qed.



Lemma compat_pair2 : forall G1 G2 T1 T2 T3 t1 t2 t3,
    rel_e_open G1 G2 t3 (trm_pair t1 t2) T3 (a_prod T1 T2) <->
    rel_e_open G1 G2 t3 t1 T3 T1 /\
    rel_e_open G1 G2 t3 t2 T3 T2.
Proof.
  intros.
  splits.
  introv H.

  - Case "->".
    destruct H as (? & HH & ?).
    splits.

    inverts HH.
    splits*.
    introv GG.
    lets : H0 GG.
    rewrite bind_pair in H1.
    destruct H1 as (HH & Ty1 & Ty2).
    inverts Ty2.
    lets* (v1 & ? & ?): normalization H6.
    lets* (vv & ? & ?): normalization Ty1.
    lets* (v2 & ? & ?): normalization H9.
    destruct HH as (? & vv1 & ? & ? & ? & ? & Imp).
    lets (? & ?) : rel_v_well_type Imp.
    lets* (v1' & v2' & ? & ? & ?) : prod_canonical H16.
    substs.
    assert (trm_pair (bind g2 t1) (bind g2 t2) ->* trm_pair v1 v2).
    sapply* multi_red_pair.
    lets* : value_unique H14 H19.
    inverts H20.
    apply rel_v_proj2 in Imp.
    destruct Imp.
    my_simplfier.
    splits*.
    exists vv v1.
    splits*.

    inverts HH.
    splits*.
    introv GG.
    lets : H0 GG.
    rewrite bind_pair in H1.
    destruct H1 as (HH & Ty1 & Ty2).
    inverts Ty2.
    lets* (v1 & ? & ?): normalization H6.
    lets* (vv & ? & ?): normalization Ty1.
    lets* (v2 & ? & ?): normalization H9.
    destruct HH as (? & vv1 & ? & ? & ? & ? & Imp).
    lets (? & ?) : rel_v_well_type Imp.
    lets* (v1' & v2' & ? & ? & ?) : prod_canonical H16.
    substs.
    assert (trm_pair (bind g2 t1) (bind g2 t2) ->* trm_pair v1 v2).
    sapply* multi_red_pair.
    lets* : value_unique H14 H19.
    inverts H20.
    apply rel_v_proj2 in Imp.
    destruct Imp.
    my_simplfier.
    splits*.
    exists vv v2.
    splits*.

  - Case "<-".
    introv H.
    destruct H as (H1 & H2).
    destruct H1 as (? & ? & Imp1).
    destruct H2 as (? & ? & Imp2).
    splits*.
    introv GG.
    lets Imp1' : Imp1 GG.
    lets Imp2' : Imp2 GG.
    clear Imp1 Imp2.
    destruct Imp1' as (Imp1' & ? & ?).
    destruct Imp1' as (? & v1 & ? & ? & ? & ? & Imp1').
    destruct Imp2' as (Imp2' & ? & ?).
    destruct Imp2' as (? & v2 & ? & ? & ? & ? & Imp2').
    my_simplfier.

    rewrite bind_pair.
    splits*.
    exists x0 (trm_pair v1 v2).
    splits*.
    sapply* multi_red_pair.
    apply rel_v_proj2.
    splits~.
Qed.



Lemma compat_pair : forall G1 G2 t1 t2 t3 t4 A1 A2 A1' A2',
    rel_e_open G1 G2 t1 t2 (|A1|) (|A2|) ->
    rel_e_open G1 G2 t3 t4 (|A1'|) (|A2'|) ->
    disjoint A1 A2' ->
    disjoint A1' A2 ->
    rel_e_open G1 G2 (trm_pair t1 t3) (trm_pair t2 t4) (a_prod (|A1|) (|A1'|)) (a_prod (|A2|) (|A2'|)).
Proof.
  introv Rel1 Rel2 Dis1 Dis2.
  destruct Rel1 as (HH1 & HH2 & Rel1).
  destruct Rel2 as (HH3 & HH4 & Rel2).
  splits*.
  introv GG.
  lets Rel1' : Rel1 GG.
  lets Rel2' : Rel2 GG.
  repeat rewrite bind_pair.
  destruct Rel1' as (Rel1' & ? & ?).
  destruct Rel1' as (v1 & v1' & ? & ? & Red1 & Red1' & Rel1').
  destruct Rel2' as (Rel2' & ? & ?).
  destruct Rel2' as (v2 & v2' & ? & ? & Red2 & Red2' & Rel2').
  lets [TT1 TT2]: bind_close HH1 HH2 GG.
  lets [TT3 TT4]: bind_close HH3 HH4 GG.

  apply rel_e_convr with (t' := trm_pair v1' v2'); auto_star.
  apply rel_e_convl with (t := trm_pair v1 v2); auto_star.
  lets : preservation_multi_step TT1 Red1.
  lets : preservation_multi_step TT2 Red1'.
  lets : preservation_multi_step TT3 Red2.
  lets : preservation_multi_step TT4 Red2'.
  apply rel_v_in_rel_e.
  apply rel_v_proj1; splits; apply rel_v_proj2; splits~.
  apply~ disjoint_rel_v.
  apply~ disjoint_rel_v.
  apply~ multi_red_pair.
  apply~ multi_red_pair.
Qed.


Lemma compat_co_proj1 : forall G1 G2 t1 t1' t2 T1 T2,
    rel_e_open G1 G2 (trm_capp co_proj1 (trm_pair t1 t1')) t2 T1 T2 ->
    rel_e_open G1 G2 t1 t2 T1 T2.
Proof with auto.
  introv H.
  destruct H as (Ty1 & Ty2 & Imp).
  inverts Ty1.
  inverts H4.
  inverts H2.

  splits*.
  introv GG.
  lets : Imp GG.
  repeat rewrite bind_capp in *.
  repeat rewrite bind_pair in *.

  lets (? & ?): bind_close H4 Ty2 GG.
  lets (? & ?): bind_close H6 Ty2 GG.
  lets (v1 & ? & ?): normalization H0.
  lets (v2 & ? & ?): normalization H1.
  lets (v3 & ? & ?): normalization H2.

  apply rel_e_redl with (t := v1) in H.
  apply rel_e_redr with (t' := v2) in H...
  apply rel_e_convl with (t := v1)...
  apply rel_e_convr with (t' := v2)...

  apply star_trans with (b := (trm_capp co_proj1 (trm_pair v1 v3)))...
  apply multi_red_capp.
  apply multi_red_pair...
Qed.

Lemma compat_co_proj2 : forall G1 G2 t1 t1' t2 T1 T2,
    rel_e_open G1 G2 (trm_capp co_proj2 (trm_pair t1' t1)) t2 T1 T2 ->
    rel_e_open G1 G2 t1 t2 T1 T2.
Proof with auto.
  introv H.
  destruct H as (Ty1 & Ty2 & Imp).
  inverts Ty1.
  inverts H4.
  inverts H2.

  splits*.
  introv GG.
  lets : Imp GG.
  repeat rewrite bind_capp in *.
  repeat rewrite bind_pair in *.

  lets (? & ?): bind_close H4 Ty2 GG.
  lets (? & ?): bind_close H6 Ty2 GG.
  lets (v1 & ? & ?): normalization H0.
  lets (v2 & ? & ?): normalization H1.
  lets (v3 & ? & ?): normalization H2.

  apply rel_e_redl with (t := v3) in H.
  apply rel_e_redr with (t' := v2) in H...
  apply rel_e_convl with (t := v3)...
  apply rel_e_convr with (t' := v2)...

  apply star_trans with (b := (trm_capp co_proj2 (trm_pair v1 v3)))...
  apply multi_red_capp.
  apply multi_red_pair...
Qed.



Lemma compat_abs : forall G1 G2 t1 t2 x T1 T2 T1' T2',
    x \notin dom G1 \u dom G2 \u fv_exp t1 \u fv_exp t2 ->
    rel_e_open ([(x, T1)] ++ G1) ([(x, T2)] ++ G2) (t1 ^ x) (t2 ^ x) T1' T2' ->
    rel_e_open G1 G2 (trm_abs t1) (trm_abs t2) (a_arrow T1 T1') (a_arrow T2 T2').
Proof.
  introv ? Rel.
  destruct Rel as (Ty1 & Ty2 & Rel).
  splits*.
  pick fresh y and apply typ_abs.
  sapply* typing_rename.
  pick fresh y and apply typ_abs.
  sapply* typing_rename.
  introv GG.
  lets Ty1': typing_to_etyping Ty1.
  lets Ty2': typing_to_etyping Ty2.
  apply etyping_abs in Ty1'; autos.
  apply etyping_abs in Ty2'; autos.
  apply etyping_to_typing in Ty1'; autos.
  apply etyping_to_typing in Ty2'; autos.
  lets* [? ?]: bind_close Ty1' Ty2' GG.
  repeat rewrite bind_abs in *.
  apply rel_v_in_rel_e.
  splits*.
  intros.

  assert (rel_g ([(x, T1)] ++ G1) ([(x, T2)] ++ G2) ([(x, a1)] ++ g1) ([(x, a2)] ++ g2)) by autos.
  lets [? ?]: rel_g_well_type_value H3.

  forwards* Imp : Rel.
  inverts H3 as. intros ? ? ? Typ.
  lets [? ?]: rel_v_well_type Typ.

  apply rel_e_convr with (t':= (bind g2 t2) ^^ a2); auto_star.
  apply rel_e_convl with (t := (bind g1 t1) ^^ a1); auto_star.
  rewrite* <- (@bind_subst g1 x).
  rewrite* <- (@bind_subst g2 x).
Qed.

Lemma compat_rcd : forall G1 G2 t1 t2 T1 T2 l,
    rel_e_open G1 G2 t1 t2 T1 T2 ->
    rel_e_open G1 G2 (trm_rcd l t1) (trm_rcd l t2) (a_rcd l T1) (a_rcd l T2).
Proof.
  introv H.
  destruct H as (? & ? & Imp).
  splits*.
  introv HH.
  apply Imp in HH.
  repeat rewrite bind_rcd.


  destruct HH as (HH & ? & ?).
  destruct HH as (v1 & v2 & ? & ? & ? & ? & ?).

  splits*.
  exists (trm_rcd l v1) (trm_rcd l v2).
  splits~; try apply~ multi_red_rcd.
  apply~ rel_v_rcd.
Qed.



Lemma compat_proj : forall G1 G2 t1 t2 T1 T2 l,
    rel_e_open G1 G2 t1 t2 (a_rcd l T1) (a_rcd l T2) ->
    rel_e_open G1 G2 (trm_proj t1 l) (trm_proj t2 l) T1 T2.
Proof.
  introv H.
  destruct H as (? & ? & Imp).
  splits*.
  introv HH.
  apply Imp in HH.
  repeat rewrite bind_proj.


  destruct HH as (HH & ? & ?).
  destruct HH as (v1 & v2 & ? & ? & ? & ? & HH).
  lets (HH1 & HH2) : rel_v_well_type HH.
  lets* (v1' & ?): rcd_canonical HH1.
  lets* (v2' & ?): rcd_canonical HH2.
  substs.
  inverts H3.
  inverts H4.
  inverts HH1.
  inverts HH2.

  splits*.
  exists v1' v2'.
  splits~.

  apply star_trans with (b := trm_proj (trm_rcd l v1') l); auto.
  apply~ multi_red_proj.

  apply star_trans with (b := trm_proj (trm_rcd l v2') l); auto.
  apply~ multi_red_proj.

  sapply rel_v_rcd; eauto.
Qed.
