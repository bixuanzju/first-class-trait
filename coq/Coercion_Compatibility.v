
Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        Target_Safety
        Logical_Relation_Def
        Logical_Relation_Infrastructure
        Infrastructure
        Compatibility_Lemma
        Normalize.




Lemma coercion_compatibility1 : forall c T1 T2 T0 G1 G2 t1 t2,
    c |= T1 ~> T2 ->
    rel_e_open G1 G2 t1 t2 T1 T0 ->
    rel_e_open G1 G2 (trm_capp c t1) t2 T2 T0.
Proof with auto.
  introv Co. gen T0 t1 t2 G1 G2.
  inductions Co; introv H.

  - (* co_id *)
    destruct H as [? [? Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & ? & ? & ?).
    rewrite bind_capp.
    splits*.
    exists* v1 v2.
    splits*.
    apply star_trans with (trm_capp co_id v1)...
    apply~ multi_red_capp.

  - Case "co_trans".

    set (HH := H).
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & ? & ? & ?).
    rewrite bind_capp.
    splits*.

    apply IHCo2 in HH.
    apply IHCo1 in HH.
    destruct HH as [Ty1' [Ty2' Rel']].
    lets TrmR : Rel' GG.
    repeat rewrite bind_capp in TrmR.
    apply rel_e_redl  with (t := trm_capp c1 (trm_capp c2 v1)) in TrmR.

    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1' & v2' & ? & ? & ? & ? & ?).
    my_simplfier.

    exists v1' v2'.
    splits*.

    apply star_trans with (trm_capp (co_trans c1 c2) v1).
    apply~ multi_red_capp.
    apply star_trans with (trm_capp c1 (trm_capp c2 v1))...

    repeat sapply~ multi_red_capp.



  - (* co_top *)
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & ? & ? & ?).

    rewrite bind_capp.
    splits*.
    exists* trm_unit v2.
    splits*.
    apply star_trans with (trm_capp co_top v1)...
    apply~ multi_red_capp.
    apply~ rel_v_unit.
    sapply* preservation_multi_step.

  - Case "co_topArr".
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & Red1 & Red2 & Relv).

    rewrite bind_capp.
    splits*.

    exists (trm_capp co_topArr v1) v2.
    splits*.
    apply~ multi_red_capp.
    lets (? & ?): rel_v_well_type Relv.


    (* case analysis on the structure of τ0 *)
    clear Rel Ty1 Ty2 GG Red1 Red2 H H0.
    gen v2.
    induction T0; intros; try solve [splits*].

    + splits*.
      intros a1 a2 RelA.
      change (rel_v a_unit T0_1 a1 a2) in RelA.
      lets (? & ?) : rel_v_well_type RelA.
      change (grel_e (rel_v a_unit T0_2) (trm_app (trm_capp co_topArr v1) a1) (trm_app v2 a2)).
      apply rel_e_grel.
      clear IHT0_1 IHT0_2.
      lets~ : unit_canonical H3.
      lets~ : unit_canonical H.
      substs.
      apply rel_e_convl with trm_unit; auto_star.
      apply rel_e_open_cl.
      apply compat_unit1; auto_star.


    + lets* (v21 & v22 & ? & ? & ?) : prod_canonical H4.
      substs.
      inverts H4.


      apply rel_v_proj2 in Relv.
      destruct Relv.

      apply rel_v_proj2.
      splits.

      apply IHT0_1...
      apply IHT0_2...


  - (*co_arr *)
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    forwards* TrmR: Rel.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & Red1 & Red2 & Imp).
    rewrite bind_capp.

    splits*.
    exists (trm_capp (co_arr c1 c2) v1) v2.
    splits*.
    apply star_trans with (trm_capp (co_arr c1 c2) v1)...
    apply~ multi_red_capp.
    lets (? & ?) : rel_v_well_type Imp.

    (* case analysis on the structure of T0 *)
    clear Rel Ty1 Ty2 Red1 Red2 H H0.
    gen v2.
    induction T0; intros; try solve [splits*].
    + simpl.
      splits*.
      intros a1 a2 RelA.
      lets (? & ?) : rel_v_relates_values RelA.
      clear IHT0_1 IHT0_2.
      lets [? ?] : rel_v_well_type RelA.

      apply rel_v_in_rel_e in RelA.
      apply rel_e_open_cl in RelA.
      apply IHCo1 in RelA. clear IHCo1.

      apply rel_v_in_rel_e in Imp.
      apply rel_e_open_cl in Imp.

      lets RelA' : compat_app Imp RelA.
      apply IHCo2 in RelA'. clear IHCo2.
      apply rel_e_open_cl in RelA'.
      apply rel_e_grel.
      apply rel_e_convl with (trm_capp c2 (trm_app v1 (trm_capp c1 a1)))...
      auto_star.


    + lets* (v21 & v22 & ? & ? & ?) : prod_canonical H4.
      substs.
      inverts H4.

      apply rel_v_proj2 in Imp.
      destruct Imp.

      apply rel_v_proj2.
      splits~.


  - (* co_pair *)
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & Red1 & Red2 & Relv).

    rewrite bind_capp.
    lets (? & ?) : rel_v_well_type Relv.
    apply rel_v_in_rel_e in Relv.
    apply rel_e_open_cl in Relv.
    lets Imp1 : IHCo1 Relv.
    lets Imp2 : IHCo2 Relv.

    apply rel_e_convl with (trm_pair (trm_capp c1 v1) (trm_capp c2 v1)); auto_star.
    apply rel_e_convr with v2; auto_star.
    apply rel_e_open_cl.
    apply compat_pair1.
    splits~.

    apply star_trans with (b := trm_capp (co_pair c1 c2) v1).
    apply~ multi_red_capp.
    apply star_trans with (b := trm_pair (trm_capp c1 v1) (trm_capp c2 v1)); autos.

  - Case "co_distArr".

    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    destruct TrmR as (TrmR & HH1 & HH2).
    destruct TrmR as (v1 & v2 & ? & ? & Red1 & Red2 & Relv).
    rewrite bind_capp.
    lets * : preservation_multi_step Red1.
    lets * : preservation_multi_step Red2.
    lets* (va & vb & ? & ? & ?) : prod_canonical H1.
    substs.

    splits*.
    exists (trm_capp co_distArr (trm_pair va vb)) v2.
    splits*.
    apply~ multi_red_capp.

    (* case analysis on the structure of τ0 *)
    clear Rel Ty1 Ty2 GG Red1 Red2 HH1 HH2.
    gen v2.
    induction T0; intros; try solve [splits*].
    + simpl.
      splits*.
      intros a1 a2 RelA.
      lets [? ?]: rel_v_relates_values RelA.
      lets [? ?]: rel_v_well_type RelA.
      clear IHT0_1 IHT0_2.
      change (grel_e (rel_v (a_prod T2 T3) T0_2) (trm_app (trm_capp co_distArr (trm_pair va vb)) a1) (trm_app v2 a2)).
      apply rel_e_grel.

      apply rel_v_proj1 in Relv.
      destruct Relv as (Relv1 & Relv2).
      apply rel_v_in_rel_e in Relv1.
      apply rel_e_open_cl in Relv1.
      apply rel_v_in_rel_e in Relv2.
      apply rel_e_open_cl in Relv2.
      apply rel_v_in_rel_e in RelA.
      apply rel_e_open_cl in RelA.

      lets : compat_app  Relv1 RelA.
      lets : compat_app  Relv2 RelA.

      apply rel_e_convl with (trm_pair (trm_app va a1) (trm_app vb a1)); auto_star.
      apply rel_e_open_cl.
      apply compat_pair1.
      splits~.

    + lets* (v21 & v22 & ? & ? & ?) : prod_canonical H2.
      substs.
      inverts H2.

      apply rel_v_proj2 in Relv.
      destruct Relv.

      apply rel_v_proj2.
      splits~.



  - (* co_proj1  *)
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & Red1 & Red2 & Relv).
    lets [B1 B2] : bind_close Ty1 Ty2 GG.
    lets Tyv1: preservation_multi_step B1 Red1.
    lets* (v1' & v2' & ? & ? & ?): prod_canonical Tyv1.
    substs.
    apply rel_v_proj1 in Relv.
    destructs Relv.

    rewrite bind_capp.
    splits*.
    exists v1' v2.
    splits*.
    apply star_trans with (b := trm_capp co_proj1 (trm_pair v1' v2')); auto.
    apply~ multi_red_capp.


  - (* co_proj2  *)
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & Red1 & Red2 & Relv).

    lets [B1 B2] : bind_close Ty1 Ty2 GG.
    lets Tyv1: preservation_multi_step B1 Red1.
    lets* (v1' & v2' & ? & ? & ?): prod_canonical Tyv1.
    substs.
    apply rel_v_proj1 in Relv.
    destructs Relv.


    rewrite bind_capp.
    splits*.
    exists v2' v2.
    splits*.
    apply star_trans with (b := trm_capp co_proj2 (trm_pair v1' v2')); auto.
    apply~ multi_red_capp.


  - Case "co_rcd".
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    clear Rel GG.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & Red1 & Red2 & Relv).
    lets (? & ?) : rel_v_well_type Relv.
    lets* (v1' & ?): rcd_canonical H3.
    substs.
    inverts H3.
    inverts H1.


    rewrite bind_capp.
    splits*.
    assert (Imp : nil |= trm_capp c v1' ~: T2) by auto_star.
    lets (vv & ? & ?): normalization Imp.

    exists (trm_rcd l vv) v2.
    splits*.
    apply star_trans with (b := trm_capp (co_rcd l c) (trm_rcd l v1')); auto.
    apply~ multi_red_capp.
    apply star_trans with (b := (trm_rcd l (trm_capp c v1'))); auto.
    apply~ multi_red_rcd.
    lets : preservation_multi_step Imp H3.

    sort.
    (* case analyze T0 *)
    clear Ty1 Ty2 Red1 Red2 H H0.
    gen v2.
    induction T0; intros; try solve [splits*].

    + SCase "T0 = a_prod".
      lets* (vv1 & vv2 & ? & ? & ?): prod_canonical H4.
      subst.
      apply rel_v_proj2 in Relv.
      destruct Relv.

      inverts H4.
      inverts H2.

      apply rel_v_proj2.
      splits~.

    + SCase "T0 = a_rcd".
      lets* (v2' & ?): rcd_canonical H4.
      substs.
      inverts H4.
      inverts H2.

      destruct (Nat.eq_dec l l0); try solve [splits*; case_if~].
      substs.

      apply rel_e_in_rel_v...
      apply rel_e_open_cl.


      apply rel_v_rcd in Relv.
      destruct Relv as (? & ? & Relv).
      apply rel_v_in_rel_e in Relv.
      apply rel_e_open_cl in Relv.
      apply IHCo in Relv.
      apply rel_e_open_cl in Relv.
      apply rel_e_redl with (t := vv) in Relv...
      apply rel_e_open_cl in Relv.

      apply~ compat_rcd.



  - Case "co_topRcd".
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    clear Rel GG.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & Red1 & Red2 & Relv).
    lets (? & ?) : rel_v_relates_values Relv.
    lets (? & ?) : rel_v_well_type Relv.
    lets : unit_canonical H3 H5.
    substs.

    rewrite bind_capp.
    splits*.
    exists (trm_rcd l trm_unit) v2.
    splits*.
    apply star_trans with (b := trm_capp (co_topRcd l) trm_unit); auto.
    apply~ multi_red_capp.

    sort.
    (* case analyze T0 *)
    clear Ty1 Ty2 Red1 Red2 H H0.
    gen v2.
    induction T0; intros; try solve [splits*].

    + SCase "T0 = a_prod".

      lets* (vv1 & vv2 & ? & ? & ?): prod_canonical H6.
      subst.
      apply rel_v_proj2 in Relv.
      destruct Relv.
      inverts H6.
      inverts H4.

      apply rel_v_proj2.
      splits~.


    + SCase "T0 = a_rcd".
      lets* (v2' & ?): rcd_canonical H6.
      substs.
      inverts H4.
      inverts H6.

      destruct (Nat.eq_dec l l0); try solve [splits*; case_if~].

      substs.
      splits*.
      case_if*.
      exists~ trm_unit v2'.
      splits*.
      apply~ rel_v_unit.



  - Case "co_crcd2".
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    clear Rel.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & Red1 & Red2 & Relv).
    lets (? & ?) : rel_v_relates_values Relv.
    lets (? & ?) : rel_v_well_type Relv.
    lets (vv1 & vv2 & ? & ? & ?): prod_canonical H3 H5.
    substs.
    inverts H5.
    lets (vv1' & ?): rcd_canonical H7 H13.
    lets (vv2' & ?): rcd_canonical H8 H15.
    substs.
    inverts H7.
    inverts H8.
    apply rel_v_proj1 in Relv.
    destruct Relv as (Relv1 & Relv2).
    inverts H13.
    inverts H15.

    rewrite bind_capp.
    splits*.
    exists (trm_rcd l (trm_pair vv1' vv2')) v2.
    splits*.
    apply star_trans with (b := trm_capp (co_distRcd l) (trm_pair (trm_rcd l vv1') (trm_rcd l vv2'))); auto.
    apply~ multi_red_capp.


    sort.
    (* case analyze T0 *)
    clear Ty1 Ty2 Red1 Red2 H H0.
    gen v2.
    induction T0; intros; try solve [splits*].

    + SCase "T0 = a_prod".

      lets* (vv1 & vv2 & ? & ? & ?): prod_canonical H6.
      subst.
      apply rel_v_proj2 in Relv1.
      destruct Relv1.
      apply rel_v_proj2 in Relv2.
      destruct Relv2.
      inverts H3.
      inverts H6.
      inverts H4.
      inverts H16.
      inverts H17.


      apply rel_v_proj2.
      splits~.


    + SCase "T0 = a_rcd".

      lets* (v2' & ?): rcd_canonical H6.
      substs.
      inverts H4.
      inverts H6.

      destruct (Nat.eq_dec l l0); try solve [splits*; case_if~].

      substs.
      apply rel_v_rcd in Relv1.
      destruct Relv1 as (? & ? & Relv1).
      apply rel_v_rcd in Relv2.
      destruct Relv2 as (? & ? & Relv2).

      apply rel_v_rcd.
      splits*.
      apply rel_v_proj1.
      splits*.

Qed.








Lemma coercion_compatibility2 : forall c T1 T2 T0 G1 G2 t1 t2,
    c |= T1 ~> T2 ->
    rel_e_open G1 G2 t1 t2 T0 T1 ->
    rel_e_open G1 G2 t1 (trm_capp c t2)  T0 T2.
Proof with auto.
  introv Co. gen T0 t1 t2 G1 G2.
  inductions Co; introv H.

  - (* co_id *)
    destruct H as [? [? Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & ? & ? & ?).
    rewrite bind_capp.
    splits*.
    exists* v1 v2.
    splits*.
    apply star_trans with (trm_capp co_id v2); autos.
    apply~ multi_red_capp.


  - Case "co_trans".

    set (HH := H).
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & ? & ? & ?).
    rewrite bind_capp.
    splits*.

    apply IHCo2 in HH.
    apply IHCo1 in HH.
    destruct HH as [Ty1' [Ty2' Rel']].
    lets TrmR : Rel' GG.
    repeat rewrite bind_capp in TrmR.
    apply rel_e_redr  with (t' := trm_capp c1 (trm_capp c2 v2)) in TrmR.

    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1' & v2' & ? & ? & ? & ? & ?).
    my_simplfier.

    exists v1' v2'.
    splits*.

    apply star_trans with (trm_capp (co_trans c1 c2) v2).
    apply~ multi_red_capp.
    apply star_trans with (trm_capp c1 (trm_capp c2 v2)); auto.

    repeat sapply~ multi_red_capp.

  - (* co_top *)
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & ? & ? & ?).

    rewrite bind_capp.
    splits*.
    exists* v1 trm_unit.
    splits*.
    apply star_trans with (trm_capp co_top v2); autos.
    apply~ multi_red_capp.
    apply~ rel_v_unit2.
    forwards * [? ?]:  bind_close Ty1 Ty2.
    sapply* preservation_multi_step.


  - Case "co_topArr".
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & Red1 & Red2 & Relv).

    rewrite bind_capp.
    splits*.

    exists v1 (trm_capp co_topArr v2).
    splits*.
    apply~ multi_red_capp.
    lets (? & ?): rel_v_well_type Relv.


    (* case analysis on the structure of τ0 *)
    clear Rel Ty1 Ty2 GG Red1 Red2 H H0.
    gen v1.
    induction T0; intros; try solve [splits*].

    + splits*.
      intros a1 a2 RelA.
      change (rel_v T0_1 a_unit a1 a2) in RelA.
      lets (? & ?) : rel_v_well_type RelA.
      change (grel_e (rel_v T0_2 a_unit)  (trm_app v1 a1) (trm_app (trm_capp co_topArr v2) a2)).
      apply rel_e_grel.
      clear IHT0_1 IHT0_2.

      lets~ : unit_canonical H4.
      lets~ : unit_canonical H0.

      substs.

      apply rel_e_convr with trm_unit; auto_star.
      apply rel_e_open_cl.
      apply compat_unit2; auto_star.

    + lets* (v21 & v22 & ? & ? & ?) : prod_canonical H3.
      substs.
      inverts H3.

      apply rel_v_proj1 in Relv.
      destruct Relv.

      apply rel_v_proj1.
      splits~.



  - (*co_arr *)
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    forwards* TrmR: Rel.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & Red1 & Red2 & Imp).
    rewrite bind_capp.


    splits*.
    exists v1 (trm_capp (co_arr c1 c2) v2).
    splits*.
    apply star_trans with (trm_capp (co_arr c1 c2) v2)...
    apply~ multi_red_capp.
    lets (? & ?) : rel_v_well_type Imp.


    (* case analysis on the structure of T0 *)
    clear Rel Ty1 Ty2 Red1 Red2 H H0.
    gen v1.
    induction T0; intros; try solve [splits*].

    + simpl.
      splits*.
      intros a1 a2 RelA.
      lets (? & ?) : rel_v_relates_values RelA.
      clear IHT0_1 IHT0_2.
      lets [? ?] : rel_v_well_type RelA.

      apply rel_v_in_rel_e in RelA.
      apply rel_e_open_cl in RelA.
      apply IHCo1 in RelA. clear IHCo1.

      apply rel_v_in_rel_e in Imp.
      apply rel_e_open_cl in Imp.

      lets RelA' : compat_app Imp RelA.
      apply IHCo2 in RelA'. clear IHCo2.
      apply rel_e_open_cl in RelA'.
      apply rel_e_grel.
      apply rel_e_convr with (trm_capp c2 (trm_app v2 (trm_capp c1 a2)))...
      auto_star.

    + lets* (v21 & v22 & ? & ? & ?) : prod_canonical H3.
      substs.
      inverts H1.
      inverts H3.

      apply rel_v_proj1 in Imp.
      destruct Imp.

      apply rel_v_proj1.
      splits~.



  - (* co_pair *)
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & Red1 & Red2 & Relv).

    rewrite bind_capp.
    apply rel_v_in_rel_e in Relv.
    apply rel_e_open_cl in Relv.
    lets Imp1 : IHCo1 Relv.
    lets Imp2 : IHCo2 Relv.
    apply rel_e_open_cl in Imp1.
    apply rel_e_open_cl in Imp2.
    destruct Imp1 as (Imp1 & ? & ?).
    destruct Imp1 as (vv & v2' & ? & ? & ? & ? & Relv1).
    destruct Imp2 as (Imp2 & ? & ?).
    destruct Imp2 as (vv' & v2'' & ? & ? & ? & ? & Relv2).
    my_simplfier.

    splits*.
    exists v1 (trm_pair v2' v2'').
    splits*.
    apply star_trans with (b := trm_capp (co_pair c1 c2) v2).
    apply~ multi_red_capp.
    apply star_trans with (b := trm_pair (trm_capp c1 v2) (trm_capp c2 v2)); autos.
    apply~ multi_red_pair.
    apply~ rel_v_proj2.


  - Case "co_distArr".

    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    destruct TrmR as (TrmR & HH1 & HH2).
    destruct TrmR as (v1 & v2 & ? & ? & Red1 & Red2 & Relv).
    rewrite bind_capp.
    lets * : preservation_multi_step Red1.
    lets * : preservation_multi_step Red2.
    lets* (va & vb & ? & ? & ?) : prod_canonical H2.
    substs.

    splits*.
    exists v1 (trm_capp co_distArr (trm_pair va vb)).
    splits*.
    apply~ multi_red_capp.

    (* case analysis on the structure of τ0 *)
    clear Rel Ty1 Ty2 GG Red1 Red2 HH1 HH2.
    gen v1.
    induction T0; intros; try solve [splits*].

    + simpl.
      splits*.
      intros a1 a2 RelA.
      lets [? ?]: rel_v_relates_values RelA.
      lets [? ?]: rel_v_well_type RelA.
      clear IHT0_1 IHT0_2.
      apply rel_e_grel.

      apply rel_v_proj2 in Relv.
      destruct Relv as (Relv1 & Relv2).
      apply rel_v_in_rel_e in Relv1.
      apply rel_e_open_cl in Relv1.
      apply rel_v_in_rel_e in Relv2.
      apply rel_e_open_cl in Relv2.
      apply rel_v_in_rel_e in RelA.
      apply rel_e_open_cl in RelA.

      lets : compat_app  Relv1 RelA.
      lets : compat_app  Relv2 RelA.

      apply rel_e_convr with (trm_pair (trm_app va a2) (trm_app vb a2)); auto_star.
      apply rel_e_open_cl.
      apply compat_pair2.
      splits~.


    + lets* (v21 & v22 & ? & ? & ?) : prod_canonical H1.
      substs.

      apply rel_v_proj1 in Relv.
      destruct Relv.
      inverts H1.
      inverts H2.

      apply rel_v_proj1.
      splits*.


  - (* co_proj1  *)
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & Red1 & Red2 & Relv).

    lets [B1 B2] : bind_close Ty1 Ty2 GG.
    lets Tyv2: preservation_multi_step B2 Red2.
    lets* (v1' & v2' & ? & ? & ?): prod_canonical Tyv2.
    substs.
    apply rel_v_proj2 in Relv.
    destructs Relv.

    rewrite bind_capp.
    splits*.
    exists* v1 v1'.
    splits*.
    apply star_trans with (b := trm_capp co_proj1 (trm_pair v1' v2')); auto.
    apply~ multi_red_capp.


  - (* co_proj2  *)
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & Red1 & Red2 & Relv).

    lets [B1 B2] : bind_close Ty1 Ty2 GG.
    lets Tyv2: preservation_multi_step B2 Red2.
    lets* (v1' & v2' & ? & ? & ?): prod_canonical Tyv2.
    substs.
    apply rel_v_proj2 in Relv.
    destructs Relv.


    rewrite bind_capp.
    splits*.
    exists v1 v2'.
    splits*.
    apply star_trans with (b := trm_capp co_proj2 (trm_pair v1' v2')); auto.
    apply~ multi_red_capp.


  - Case "co_rcd".
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & Red1 & Red2 & Relv).
    lets (? & ?) : rel_v_well_type Relv.
    lets~ (v1' & ?): rcd_canonical H4.
    substs.
    inverts H4.
    inverts H2.


    rewrite bind_capp.
    splits*.
    assert (Imp : nil |= trm_capp c v1' ~: T2) by auto_star.
    lets (vv & ? & ?): normalization Imp.


    exists v1 (trm_rcd l vv).
    splits*.
    apply star_trans with (b := trm_capp (co_rcd l c) (trm_rcd l v1')); auto.
    apply~ multi_red_capp.
    apply star_trans with (b := (trm_rcd l (trm_capp c v1'))); auto.
    apply~ multi_red_rcd.
    lets* : preservation_multi_step Imp H4.


    sort.
    (* case analyze T0 *)
    clear Rel Ty1 Ty2 Red1 Red2 H H0.
    gen v1.
    induction T0; intros; try solve [splits*].

    + SCase "T0 = a_prod".

      lets* (vv1 & vv2 & ? & ? & ?): prod_canonical H3.
      subst.
      apply rel_v_proj1 in Relv.
      destruct Relv.
      inverts H3.
      inverts H1.

      apply rel_v_proj1.
      splits*.

    + SCase "T0 = a_rcd".
      lets* (v2' & ?): rcd_canonical H3.
      substs.
      inverts H3.
      inverts H1.

      destruct (Nat.eq_dec l l0); try solve [splits*; case_if~].
      substs.

      apply rel_e_in_rel_v...
      apply rel_e_open_cl.


      apply rel_v_rcd in Relv.
      destruct Relv as (? & ? & Relv).
      apply rel_v_in_rel_e in Relv.
      apply rel_e_open_cl in Relv.
      apply IHCo in Relv.
      apply rel_e_open_cl in Relv.
      apply rel_e_redr with (t' := vv) in Relv...
      apply rel_e_open_cl in Relv.

      apply~ compat_rcd.



  - Case "co_topRcd".
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & Red1 & Red2 & Relv).
    lets (? & ?) : rel_v_relates_values Relv.
    lets (? & ?) : rel_v_well_type Relv.
    lets : unit_canonical H4 H6.
    substs.

    rewrite bind_capp.
    splits*.
    exists v1 (trm_rcd l trm_unit).
    splits*.
    apply star_trans with (b := trm_capp (co_topRcd l) trm_unit); auto.
    apply~ multi_red_capp.

    sort.
    (* case analyze T0 *)
    (* case analyze T0 *)
    clear Rel Ty1 Ty2 Red1 Red2 H H0.
    gen v1.
    induction T0; intros; try solve [splits*].

    + SCase "T0 = a_prod".

      lets* (vv1 & vv2 & ? & ? & ?): prod_canonical H5.
      subst.
      apply rel_v_proj1 in Relv.
      destruct Relv.
      inverts H5.
      inverts H3.

      apply rel_v_proj1.
      splits*.


    + SCase "T0 = a_rcd".
      lets* (v2' & ?): rcd_canonical H5.
      substs.
      inverts H3.
      inverts H5.

      destruct (Nat.eq_dec l l0); try solve [splits*; case_if~].
      substs.
      splits*.
      case_if*.
      exists~ v2' trm_unit.
      splits*.
      apply~ rel_v_unit2.


  - Case "co_crcd2".
    destruct H as [Ty1 [Ty2 Rel]].
    splits*.
    intros g1 g2 GG.
    lets TrmR : Rel GG.
    clear Rel.
    destruct TrmR as (TrmR & ? & ?).
    destruct TrmR as (v1 & v2 & ? & ? & Red1 & Red2 & Relv).
    lets (? & ?) : rel_v_relates_values Relv.
    lets (? & ?) : rel_v_well_type Relv.
    lets (vv1 & vv2 & ? & ? & ?): prod_canonical H4 H6.
    substs.
    inverts H6.
    lets (vv1' & ?): rcd_canonical H7 H13.
    lets (vv2' & ?): rcd_canonical H8 H15.
    substs.
    inverts H7.
    inverts H8.
    apply rel_v_proj2 in Relv.
    destruct Relv as (Relv1 & Relv2).
    inverts H13.
    inverts H15.

    rewrite bind_capp.
    splits*.
    exists v1 (trm_rcd l (trm_pair vv1' vv2')).
    splits*.
    apply star_trans with (b := trm_capp (co_distRcd l) (trm_pair (trm_rcd l vv1') (trm_rcd l vv2'))); auto.
    apply~ multi_red_capp.


    sort.
    (* case analyze T0 *)
    clear Ty1 Ty2 Red1 Red2 H H0 H2.
    gen v1.
    induction T0; intros; try solve [splits*].

    + SCase "T0 = a_prod".
      lets* (vv1 & vv2 & ? & ? & ?): prod_canonical H5.
      subst.
      apply rel_v_proj1 in Relv1.
      destruct Relv1.
      apply rel_v_proj1 in Relv2.
      destruct Relv2.
      inverts H5.

      apply rel_v_proj1.
      splits~.


    + SCase "T0 = a_rcd".

      lets* (v2' & ?): rcd_canonical H5.
      substs.
      inverts H3.
      inverts H5.

      destruct (Nat.eq_dec l l0); try solve [splits*; case_if~].

      substs.
      apply rel_v_rcd in Relv1.
      destruct Relv1 as (? & ? & Relv1).
      apply rel_v_rcd in Relv2.
      destruct Relv2 as (? & ? & Relv2).

      apply rel_v_rcd.
      splits*.
      apply rel_v_proj2.
      splits~.


Qed.
