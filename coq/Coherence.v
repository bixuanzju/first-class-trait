
Require Import LibTactics.
Require Import Metalib.Metatheory.


Require Import
        Logical_Relation_Def
        Logical_Relation_Infrastructure
        Target_Safety
        Coercion_Compatibility
        Infrastructure
        Source_Property
        Compatibility_Lemma
        target_inf
        Normalize.



Definition ctx_equiv Γ E1 E2 A := forall e1 e2 dir dir' C c,
    has_type Γ E1 dir A e1 ->
    has_type Γ E2 dir A e2 ->
    CTyp C Γ dir A nil dir' styp_nat c ->
    kleene_equiv (appctx c e1) (appctx c e2).


Theorem coherence_log : forall Γ E A d t1 t2,
    has_type Γ E d A t1 ->
    has_type Γ E d A t2 ->
    rel_e_open (∥ Γ ∥) (∥ Γ ∥) t1 t2 (| A |) (| A |).
Proof.
  introv Ty1. gen t2.
  inductions Ty1; introv Ty2; simpls.
  - (* t_top *)
    inverts Ty2.
    apply~ compat_unit1.
  - (* t_int *)
    inverts Ty2.
    apply~ compat_int.
  - (* t_var *)
    inverts Ty2.
    apply~ compat_var.
  - inverts Ty2 as.
    introv Ty1 Ty2.
    lets H: inference_unique Ty1_1 Ty1.
    inverts H.
    forwards * : IHTy1_1.
    forwards * : IHTy1_2.
    apply~ compat_app.

  - (* t_merge *)
    inverts Ty2 as Ty1' Ty'2 ?.
    unfolds.
    forwards * H0 : elaboration_well_type_term Ty1_1.
    forwards * H1 : elaboration_well_type_term Ty1_2.
    forwards * H2 : elaboration_well_type_term Ty1'.
    forwards * H3 : elaboration_well_type_term Ty'2.
    splits*.
    intros g1 g2 GG'.
    repeat rewrite bind_pair.

    forwards * Imp1 : IHTy1_1.
    forwards * Imp2 : IHTy1_2.
    destruct Imp1 as (? & ? & Imp1).
    destruct Imp2 as (? & ? & Imp2).
    lets HH: Imp1 GG'. clear Imp1.
    lets HH': Imp2 GG'. clear Imp2.

    apply rel_e_open_cl.
    apply rel_e_open_cl in HH.
    apply rel_e_open_cl in HH'.
    apply~ compat_pair.

    apply~ disjoint_commute.

  - Case "t_rcd".
    inverts* Ty2.
    forwards * : IHTy1.
    destruct H as (? & ? & Imp).

    splits*.
    introv HH.
    apply Imp in HH.
    repeat rewrite bind_rcd.

    apply rel_e_open_cl.
    apply rel_e_open_cl in HH.
    apply~ compat_rcd.

  - Case "t_proj".
    inverts* Ty2.
    forwards * : IHTy1.
    destruct H as (? & ? & Imp).

    splits*.
    introv HH.
    apply Imp in HH.
    repeat rewrite bind_proj.

    apply rel_e_open_cl.
    apply rel_e_open_cl in HH.
    apply~ compat_proj.


  - inverts* Ty2.
  - inverts Ty2 as.
    intros L0 HH.
    pick fresh x.
    forwards* : H0 x (e0 ^ x). apply~ HH.
    sapply* compat_abs.
    introv Tm. inverts Tm.
  - (* t_sub *)
    inverts Ty2.
    inverts Ty1.
    forwards * : IHTy1.
    forwards * : inference_unique Ty1 H0. substs.
    forwards * : subtyping_well_type_coercion H.
    forwards * : subtyping_well_type_coercion H1.
    sapply* coercion_compatibility1.
    sapply* coercion_compatibility2.
Qed.


Theorem congruence : forall Γ Γ' E1 E2 A A' e1 e2 dir dir' C c,
    CTyp C Γ dir A Γ' dir' A' c ->
    has_type Γ E1 dir A e1 ->
    has_type Γ E2 dir A e2 ->
    rel_e_open (∥ Γ ∥) (∥ Γ ∥) e1 e2 (| A |) (| A |) ->
    rel_e_open (∥ Γ' ∥) (∥ Γ' ∥) (appctx c e1) (appctx c e2) (| A' |) (| A' |).
Proof.
  introv Typ.
  gen E1 E2 e1 e2.
  induction Typ; introv Typ1 Typ2 HH; simpls*.


  - Case "appL1".
    lets* : IHTyp Typ1 Typ2 HH.
    lets* : coherence_log H H.
    sapply* compat_app.
  - Case "appL2".
    lets* : IHTyp Typ1 Typ2 HH.
    lets* : coherence_log H H.
    sapply* compat_app.
  - Case "appR1".
    lets* : IHTyp Typ1 Typ2 HH.
    lets* : coherence_log H H.
    sapply* compat_app.
  - Case "appR2".
    lets* : IHTyp Typ1 Typ2 HH.
    lets* : coherence_log H H.
    sapply* compat_app.
  - Case "pairL1".
    lets* : IHTyp Typ1 Typ2 HH.
    lets* : coherence_log H H.
    sapply* compat_pair.
    apply~ disjoint_commute.
  - Case "pairL2".
    lets* : IHTyp Typ1 Typ2 HH.
    lets* : coherence_log H H.
    sapply* compat_pair.
    apply~ disjoint_commute.
  - Case "pairR1".
    lets* : IHTyp Typ1 Typ2 HH.
    lets* : coherence_log H H.
    sapply* compat_pair.
    apply~ disjoint_commute.
  - Case "pairR2".
    lets* : IHTyp Typ1 Typ2 HH.
    lets* : coherence_log H H.
    sapply* compat_pair.
    apply~ disjoint_commute.
  - Case "rcd1".
    lets* : IHTyp Typ1 Typ2 HH.
    apply~ compat_rcd.
  - Case "rcd2".
    lets* : IHTyp Typ1 Typ2 HH.
    apply~ compat_rcd.
  - Case "proj1".
    lets* : IHTyp Typ1 Typ2 HH.
    apply~ compat_proj.
  - Case "proj2".
    lets* : IHTyp Typ1 Typ2 HH.
    apply~ compat_proj.
  - Case "lam1".

    lets* : IHTyp Typ1 Typ2 HH.
    apply compat_abs with (x := x).
    repeat rewrite fv_exp_close_exp_wrt_exp.
    solve_notin.
    rewrite_env ((x, | A1 |) :: ∥ GG' ∥).
    repeat rewrite~ open_exp_wrt_exp_close_exp_wrt_exp.
  - Case "lam2".
    lets* : IHTyp Typ1 Typ2 HH.
    apply compat_abs with (x := x).
    repeat rewrite fv_exp_close_exp_wrt_exp.
    solve_notin.
    rewrite_env ((x, | A1 |) :: ∥ GG' ∥).
    repeat rewrite~ open_exp_wrt_exp_close_exp_wrt_exp.
Qed.


Theorem coherence_ctx : forall Γ Γ' E A A' e e' dir dir' C c,
    CTyp C Γ dir A Γ' dir' A' c ->
    has_type Γ E dir A e ->
    has_type Γ E dir A e' ->
    rel_e_open (∥ Γ' ∥) (∥ Γ' ∥) (appctx c e) (appctx c e') (| A' |) (| A' |).
Proof.

  intros.
  lets : coherence_log H0 H1.
  lets~ : congruence H H0 H1 H2.
Qed.


Theorem coherence_thm : forall Γ E A,
    ctx_equiv Γ E E A.
Proof.
  intros.
  unfolds.
  introv Ty1 Ty2 CTy.
  lets H : coherence_ctx CTy Ty1 Ty2.
  unfolds.
  simpls.
  destruct H as (? & ? & TT).
  pose (HH := TT nil nil rel_g_empty).
  simpls.
  destruct HH as (HH & ? & ?).
  destruct HH as (v1 & v2 & ? & ? & ? & ? & Rel).
  destruct Rel as (? & ? & ? & ? & Imp).
  inverts Imp.
  exists* n.
Qed.
