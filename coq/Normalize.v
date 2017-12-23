
Require Import
        target_inf
        Infrastructure
        LibTactics
        Target_Adequacy
        Target_Safety.



(**

Adapted from

https://softwarefoundations.cis.upenn.edu/draft/plf-current/Norm.html

 *)



Close Scope nat_scope.

Definition halts t  :=
  exists t',  value t' /\ t ->* t'.


Lemma value_halts : forall v, value v -> halts v.
Proof.
  introv H.
  unfolds.
  exists~ v.
Qed.



Fixpoint R T t : Prop :=
  nil |= t ~: T /\ halts t /\
  (match T with
   | a_nat => True
   | a_unit => True
   | a_arrow T1 T2 => forall s, R T1 s -> R T2 (trm_app t s)
   | a_prod T1 T2 => R T1 (trm_capp co_proj1 t) /\ R T2 (trm_capp co_proj2 t)
   | a_rcd l T' => R T' (trm_proj t l)
   end).


Lemma R_lc : forall T t,
    R T t -> lc_exp t.
Proof.
  introv H.
  destruct* T;
    unfold R in H; inverts* H.
Qed.




Lemma R_halts : forall T t, R T t -> halts t.
Proof.
  introv H.
  destruct T; unfold R in H; inverts H; inverts H1; assumption.
Qed.


Lemma R_typable_empty : forall T t, R T t -> nil |= t ~: T.
Proof.
  intros. destruct T; unfold R in H; inversion H; inversion H1; assumption.
Qed.


Lemma step_preserves_halting : forall t t', (step t t') -> (halts t <-> halts t').
Proof.
  introv ST.
  unfolds.
  split.

  - Case "->".
    intros [t'' [V STM]].
    inverts STM.
    false.
    apply value_irred in V.
    unfold irred in V.
    specialize (V t').
    apply~ V.

    lets~ : step_unique ST H.
    substs.
    exists~ t''.

  - Case "<-".
    intros [t'0 [STM V]].
    exists~ t'0; splits; eauto.
Qed.


Lemma step_preserves_R : forall T t t', (step t t') -> R T t -> R T t'.
Proof with try apply R_lc; eauto.
  induction T; intros t t' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
    destruct Rt as [typable_empty_t [halts_t RRt]].

  - Case "a_nat".
    splits~.
    sapply preservation...
    forwards * : step_preserves_halting E.

  - Case "a_unit".
    splits~.
    sapply preservation...
    forwards * : step_preserves_halting E.

  - Case "a_arrow".
    splits~.
    sapply preservation...
    forwards * : step_preserves_halting E.
    intros.
    eapply IHT2.
    apply step_app1...
    sapply R_lc...
    apply RRt...

  - Case "a_prod".
    destruct RRt.
    splits~.
    sapply preservation...
    forwards * : step_preserves_halting E.
    eapply IHT1...
    eapply IHT2...

  - Case "a_rcd".
    splits~.
    sapply preservation...
    forwards * : step_preserves_halting E.
    eapply IHT...
Qed.


Lemma multistep_preserves_R : forall T t t',
  (t ->* t') -> R T t -> R T t'.
Proof.
  intros T t t' STM; induction STM; intros.
  assumption.
  apply IHSTM. eapply step_preserves_R. apply H. assumption.
Qed.


Lemma step_preserves_R' : forall T t t',
  nil |= t ~: T -> (step t t') -> R T t' -> R T t.
Proof with try apply R_lc; eauto.
  induction T; intros t t' Typ E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt; destruct Rt as [typable_empty_t [halts_t RRt]].

  - Case "a_nat".
    splits~.
    forwards * : step_preserves_halting E.

  - Case "a_unit".
    splits~.
    forwards * : step_preserves_halting E.

  - Case "a_arrow".
    splits~.
    forwards * : step_preserves_halting E.
    intros.
    lets : R_typable_empty H.
    eapply IHT2...

  - Case "a_prod".
    destruct RRt.
    splits~.
    forwards * : step_preserves_halting E.
    eapply IHT1...
    eapply IHT2...

  - Case "a_rcd".
    splits~.
    forwards * : step_preserves_halting E.
    eapply IHT...
Qed.


Lemma multistep_preserves_R' : forall T t t',
  nil |= t ~: T -> (t ->* t') -> R T t' -> R T t.
Proof.
  intros T t t' HT STM.
  induction STM; intros.
  assumption.
  eapply step_preserves_R'. assumption. apply H. apply IHSTM.
  eapply preservation; eauto. auto.
Qed.




Fixpoint msubst (ss:env) (t:exp) {struct ss} : exp :=
  match ss with
  | nil => t
  | ((x,s)::ss') => msubst ss' ([x ~> s]t)
  end.



Inductive instantiation : ctx -> env -> Prop :=
| V_nil :
    instantiation nil nil
| V_cons : forall x T v Γ γ,
    x # Γ -> x # γ ->
    value v -> R T v ->
    instantiation Γ γ ->
    instantiation ((x,T)::Γ) ((x,v)::γ).


Definition vacuous_substitution := subst_exp_fresh_eq.


Definition closed (t:exp) :=
  forall x,  x `notin` fv_exp t.


Lemma subst_closed: forall t,
    closed t ->
    forall x t', [x ~> t']t = t.
Proof.
  intros.
  apply vacuous_substitution.
  apply H.
Qed.



Lemma msubst_closed: forall t, closed t -> forall ss, msubst ss t = t.
Proof.
  induction ss.
    reflexivity.
    destruct a. simpl. rewrite subst_closed; assumption.
Qed.


Fixpoint closed_env (env:env) {struct env} :=
  match env with
  | nil => True
  | (x,t)::env' => lc_exp t /\ closed t /\ closed_env env'
  end.



Lemma msubst_var: forall ss x, closed_env ss ->
   msubst ss (trm_var_f x) =
   match get x ss with
   | Some t => t
   | None => trm_var_f x
  end.
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
     simpl. repeat case_if.
      apply msubst_closed. inverts H as (? & ?); auto.
      apply IHss. inverts H as (? & ?); auto.
Qed.

Lemma msubst_abs: forall ss t,
    msubst ss (trm_abs t) =
    trm_abs (msubst ss t).
Proof.
  induction ss; intros.
  simpl.
  reflexivity.
  destruct a.
  simpl.
  rewrite~ IHss.
Qed.

Lemma msubst_app : forall ss t1 t2,
    msubst ss (trm_app t1 t2) = trm_app (msubst ss t1) (msubst ss t2).
Proof.
 induction ss; intros.
   reflexivity.
   destruct a.
    simpl. rewrite <- IHss. auto.
Qed.


Lemma msubst_pair : forall ss t1 t2,
    msubst ss (trm_pair t1 t2) = trm_pair (msubst ss t1) (msubst ss t2).
Proof.
 induction ss; intros.
   reflexivity.
   destruct a.
    simpl. rewrite <- IHss. auto.
Qed.

Lemma msubst_rcd : forall ss l t,
    msubst ss (trm_rcd l t) = trm_rcd l (msubst ss t).
Proof.
 induction ss; intros.
   reflexivity.
   destruct a.
    simpl. rewrite <- IHss. auto.
Qed.


Lemma msubst_proj : forall ss l t,
    msubst ss (trm_proj t l) = trm_proj (msubst ss t) l.
Proof.
 induction ss; intros.
   reflexivity.
   destruct a.
    simpl. rewrite <- IHss. auto.
Qed.


Lemma msubst_capp : forall ss c t,
    msubst ss (trm_capp c t) = trm_capp c (msubst ss t).
Proof.
 induction ss; intros.
   reflexivity.
   destruct a.
    simpl. rewrite <- IHss. auto.
Qed.


Lemma msubst_unit : forall ss,
    msubst ss trm_unit = trm_unit.
Proof.
 induction ss; intros.
   reflexivity.
   destruct a.
    simpl. rewrite IHss. auto.
Qed.


Lemma msubst_lit : forall ss i,
    msubst ss (trm_lit i) = trm_lit i.
Proof.
 induction ss; intros.
   reflexivity.
   destruct a.
    simpl. rewrite IHss. auto.
Qed.



Lemma instantiation_domains_match: forall {Γ} {γ},
    instantiation Γ γ ->
    forall {x} {T},
      binds x T Γ -> exists t, binds x t γ.
Proof.
  intros Γ γ V. induction V; intros x0 T0 C.
  inverts C.
  analyze_binds C.
  exists~ v.
  lets (v' & ?): IHV BindsTac.
  exists~ v'.
Qed.


Corollary typable_empty_closed : forall t T,
    nil |= t ~: T ->
    closed t.
Proof.
  intros. unfold closed. intros x H1.
  lets : value_no_fv H.
  solve_uniq.
Qed.


Lemma instantiation_env_closed : forall Γ γ,
  instantiation Γ γ -> closed_env γ.
Proof.
  intros Γ γ V; induction V; intros.
    econstructor.
    unfold closed_env. fold closed_env.
    splits~. eapply typable_empty_closed. eapply R_typable_empty. eauto.
Qed.

Lemma instantiation_R : forall Γ γ,
    instantiation Γ γ ->
    forall x t T,
      binds x T Γ ->
      binds x t γ ->
      R T t.
Proof.
  intros Γ γ V. induction V; intros x' t' T' G E.
  inverts G.
  analyze_binds G.
  analyze_binds E.
  lets* : binds_dom_contradiction BindsTac H0.
  analyze_binds  E.
  lets* : binds_dom_contradiction BindsTac H.

  forwards * : IHV BindsTac BindsTac0.

Qed.


Lemma msubst_preserves_typing : forall Γ γ,
    instantiation Γ γ ->
    forall t S, Γ |= t ~: S ->
           nil |= (msubst γ t) ~: S.
Proof.
  introv Ins.
  induction~ Ins; intros.
  simpls.
  apply IHIns.
  rewrite_env (nil ++ Γ).
  eapply typing_subst; simpl_env in *; eauto.
  lets : R_typable_empty H2.
  rewrite_env (Γ ++ nil).
  apply typing_weakening; eauto.
  lets (? & ?) : typing_regular H3.
  solve_uniq.
Qed.


Lemma uniq_gamma : forall Γ γ,
    instantiation Γ γ ->
    uniq Γ ->
    uniq γ.
Proof.
  introv H.
  induction~ H; introv Uniq.
  solve_uniq.
Qed.


Lemma binds_get : forall (A : Type) x (t : A) (T : list (atom * A)),
    uniq T -> binds x t T -> get x T = Some t.
Proof.
  intros A x t T.
  gen x t.
  induction T; introv H Bind.
  invert Bind.
  destruct a as (x0, t0).
  simpls.
  apply binds_cons_uniq_1 in Bind; auto.
  destruct Bind.
  destructs H0; substs.
  case_if~.
  destruct H0.
  case_if.
  apply~ IHT.
  solve_uniq.
Qed.



Lemma msubst_subst_open : forall g t a,
    closed_env g ->
    closed a ->
    msubst g (t ^^ a) = (msubst g t) ^^ a.
Proof.
  intro g.
  induction g; intros; autos.
  destruct a as [x T].
  simpls.
  inverts H as (? & ?).
  rewrite~ <- IHg.
  rewrite~ subst_exp_open_exp_wrt_exp.
  rewrite subst_exp_fresh_eq with (e2 := a0); auto.
Qed.



Lemma msubst_open : forall x v γ t,
    closed_env ((x ~ v) ++ γ) ->
    x \notin fv_exp t ->
    msubst ((x ~ v) ++ γ) (t ^ x) = (msubst γ t) ^^ v.
Proof.
  intros.
  inverts H as (? & ?).
  simpl.
  rewrite* <- msubst_subst_open.
  rewrite* <- subst_exp_intro.

Qed.


Lemma R_capp : forall c t T1 T2,
    c |= T1 ~> T2 ->
    R T1 t ->
    R T2 (trm_capp c t).
Proof with auto.
  introv H.
  gen t.
  induction H; intros.

  - Case "co_id".
    lets WT : R_typable_empty H.
    lets VA : R_halts H.
    destruct VA as (v & ? & Red).
    apply multistep_preserves_R with (t' := v) in H...
    apply multistep_preserves_R' with v; auto_star.
    apply star_trans with (trm_capp co_id v)...
    apply~ multi_red_capp.

  - Case "co_trans".
    lets : IHcotyp2 H1.
    lets : IHcotyp1 H2.
    lets WT : R_typable_empty H1.
    lets VA : R_halts H1.
    destruct VA as (v & ? & Red).
    apply multistep_preserves_R' with (trm_capp c1 (trm_capp c2 v)); auto_star.
    apply star_trans with (trm_capp (co_trans c1 c2) v)...
    apply~ multi_red_capp.
    apply multistep_preserves_R with (t' := trm_capp c1 (trm_capp c2 v)) in H3...
    apply~ multi_red_capp.
    apply~ multi_red_capp.

  - Case "co_top".
    lets WT : R_typable_empty H.
    lets VA : R_halts H.
    destruct VA as (v & ? & Red).
    apply multistep_preserves_R' with (trm_unit); auto_star.
    apply star_trans with (trm_capp co_top v)...
    apply~ multi_red_capp.
    splits~.
    apply~ value_halts.

  - Case "co_topArr".
    lets WT : R_typable_empty H.
    lets (v & ? & Red) : R_halts H.
    lets : preservation_multi_step WT Red.
    lets~ : unit_canonical H1.
    substs.

    unfold R.
    splits*.
    unfolds.
    exists (trm_capp co_topArr trm_unit).
    splits~.
    apply~ multi_red_capp.


    intros.
    splits*.
    destructs H2.
    destruct H3 as (v' & ? & ?).
    lets : preservation_multi_step H2 H5.
    lets~ : unit_canonical H6.
    substs.
    unfolds.
    exists trm_unit.
    splits~.
    apply star_trans with (trm_app (trm_capp co_topArr trm_unit) trm_unit); auto.
    apply star_trans with (trm_app (trm_capp co_topArr trm_unit) s); auto.
    apply~ multi_red_app2.
    apply~ multi_red_capp.
    apply~ multi_red_app.


  - Case "co_arr".
    lets : R_typable_empty H1.
    destructs H1.
    destruct H3 as (v & ? & ?).

    unfold R.
    fold R.
    splits*.
    unfolds.
    exists (trm_capp (co_arr c1 c2) v).
    splits~.
    apply~ multi_red_capp.
    introv W.
    lets : R_typable_empty W.
    lets (v' & ? & ?): R_halts W.
    apply IHcotyp1 in W.
    apply H4 in W.
    apply IHcotyp2 in W.

    apply multistep_preserves_R with (t' := trm_capp c2 (trm_app v (trm_capp c1 s))) in W.
    apply multistep_preserves_R with (t' := trm_capp c2 (trm_app v (trm_capp c1 v'))) in W.

    apply multistep_preserves_R' with (t' := trm_capp c2 (trm_app v (trm_capp c1 v'))); auto_star.

    apply star_trans with (trm_app (trm_capp (co_arr c1 c2) v) s).
    apply~ multi_red_app2.
    apply~ multi_red_capp.
    apply star_trans with (trm_app (trm_capp (co_arr c1 c2) v) v').
    apply~ multi_red_app.
    apply~ star_one.

    apply~ multi_red_capp.
    apply~ multi_red_app.
    apply~ multi_red_capp.

    apply~ multi_red_capp.
    apply~ multi_red_app2.


  - Case "co_pair".
    lets : R_typable_empty H1.
    lets : R_halts H1.
    destruct H3 as (v & ? & ?).
    apply multistep_preserves_R with (t' := v) in H1; auto.
    lets WT1 : IHcotyp1 H1.
    lets WT2 : IHcotyp2 H1.
    lets VA : R_halts WT1.
    lets VB : R_halts WT2.
    destruct VA as (v1 & ? & ?).
    destruct VB as (v2 & ? & ?).
    apply multistep_preserves_R with (t' := v1) in WT1; auto.
    apply multistep_preserves_R with (t' := v2) in WT2; auto.
    lets : R_typable_empty WT1.
    lets : R_typable_empty WT2.

    unfold R.
    fold R.
    splits*.
    unfolds.
    exists (trm_pair v1 v2).
    splits~.
    apply star_trans with (trm_capp (co_pair c1 c2) v).
    apply~ multi_red_capp.
    apply star_trans with (trm_pair (trm_capp c1 v) (trm_capp c2 v)).
    apply~ star_one.
    apply~ multi_red_pair.

    apply multistep_preserves_R' with (t' := trm_capp co_proj1 (trm_pair v1 v2)); auto_star.
    apply~ multi_red_capp.
    apply star_trans with (trm_capp (co_pair c1 c2) v).
    apply~ multi_red_capp.
    apply star_trans with (trm_pair (trm_capp c1 v) (trm_capp c2 v)).
    apply~ star_one.
    apply~ multi_red_pair.
    apply multistep_preserves_R' with (v1); auto_star.

    apply multistep_preserves_R' with (t' := trm_capp co_proj2 (trm_pair v1 v2)); auto_star.
    apply~ multi_red_capp.
    apply star_trans with (trm_capp (co_pair c1 c2) v).
    apply~ multi_red_capp.
    apply star_trans with (trm_pair (trm_capp c1 v) (trm_capp c2 v)).
    apply~ star_one.
    apply~ multi_red_pair.
    apply multistep_preserves_R' with (v2); auto_star.

  - Case "co_distArr".

    lets : R_typable_empty H.
    lets (v & ? & ?) : R_halts H.
    lets : preservation_multi_step H0 H2.
    lets~ (v1 & v2 & ? & ? & ?): prod_canonical H3.
    substs.
    inverts H3.
    inverts H1.

    unfold R in *.
    fold R in *.
    destructs H.
    destructs H3.


    splits*.
    unfolds.
    exists (trm_capp co_distArr (trm_pair v1 v2)).
    splits*.
    apply~ multi_red_capp.
    introv W.
    lets : R_typable_empty W.
    lets (v' & ? & ?): R_halts W.
    apply multistep_preserves_R with (t' := v') in W; auto.
    lets WT1 : H14 W.
    lets WT2 : H11 W.
    apply multistep_preserves_R with (t' := trm_app v1 v') in WT1; auto.
    apply multistep_preserves_R with (t' := trm_app v2 v') in WT2; auto.
    lets (vv1 & ? & ?) : R_halts WT1.
    lets (vv2 & ? & ?) : R_halts WT2.
    apply multistep_preserves_R with (t' := vv1) in WT1; auto.
    apply multistep_preserves_R with (t' := vv2) in WT2; auto.

    assert ( trm_app (trm_capp co_distArr t) s ->* trm_pair vv1 vv2).
    {

    apply star_trans with (trm_app (trm_capp co_distArr (trm_pair v1 v2)) s).
    apply~ multi_red_app2.
    apply~ multi_red_capp.
    apply star_trans with (trm_app (trm_capp co_distArr (trm_pair v1 v2)) v').
    apply~ multi_red_app.
    apply star_trans with (trm_pair (trm_app v1 v') (trm_app v2 v')); auto.
    apply~ multi_red_pair.

    }

    splits*.
    unfolds.

    exists (trm_pair vv1 vv2).
    splits~.

    apply multistep_preserves_R' with (t' := vv1); auto_star.
    apply star_trans with (trm_capp co_proj1 (trm_pair vv1 vv2)); auto.
    apply~ multi_red_capp.

    apply multistep_preserves_R' with (t' := vv2); auto_star.
    apply star_trans with (trm_capp co_proj2 (trm_pair vv1 vv2)); auto.
    apply~ multi_red_capp.

    apply star_trans with (trm_app (trm_capp co_proj2 (trm_pair v1 v2)) v'); auto.
    apply~ multi_red_app2.
    apply~ multi_red_capp.

    apply star_trans with (trm_app (trm_capp co_proj1 (trm_pair v1 v2)) v'); auto.
    apply~ multi_red_app2.
    apply~ multi_red_capp.


  - Case "co_proj1".
    unfold R in H.
    fold R in H.
    destructs~ H.

  - Case "co_proj2".
    unfold R in H.
    fold R in H.
    destructs~ H.

  - Case "co_rcd".
    unfold R in H0.
    fold R in H0.
    destructs H0.
    unfolds in H1.
    destruct H1 as (v & ? & ?).
    lets : preservation_multi_step H0 H3.
    lets* : rcd_canonical H4.
    destruct H5 as (v' & ?).
    substs.
    inverts H4.
    inverts H1.
    apply multistep_preserves_R with (t' := trm_proj (trm_rcd l v') l)in H2.
    apply multistep_preserves_R with (t' := v')in H2; auto_star.
    lets : IHcotyp H2.
    lets : R_halts H1.
    unfolds in H4.
    destruct H4 as (v'' & ? & ?).
    apply multistep_preserves_R with (t' := v'')in H1; auto_star.


    unfold R.
    fold R.
    splits*.
    unfolds.
    exists (trm_rcd l v'').
    splits*.
    apply star_trans with (b := trm_capp (co_rcd l c) (trm_rcd l v')).
    apply~ multi_red_capp.
    apply star_trans with (b := (trm_rcd l (trm_capp c v'))); auto_star.
    apply~ multi_red_rcd.

    apply multistep_preserves_R' with (t' := v''); auto_star.
    apply star_trans with (b := trm_proj (trm_rcd l v'') l); auto_star.
    apply~ multi_red_proj.
    apply star_trans with (b := trm_capp (co_rcd l c) (trm_rcd l v')).
    apply~ multi_red_capp.
    apply star_trans with (b := (trm_rcd l (trm_capp c v'))); auto_star.
    apply~ multi_red_rcd.

    apply~ multi_red_proj.


  - Case "co_topRcd".
    lets : R_typable_empty H.
    lets : R_halts H.
    unfold halts in *.
    destruct H1 as (v & ? & ?).
    lets : preservation_multi_step H0 H2.
    lets~ : unit_canonical H3.
    substs.
    splits*.
    exists (trm_rcd l trm_unit).
    splits~.
    apply star_trans with (b := trm_capp (co_topRcd l) trm_unit); auto_star.
    apply~ multi_red_capp.

    unfold halts in *.
    exists trm_unit.
    splits~.
    apply star_trans with (b := trm_proj (trm_capp (co_topRcd l) trm_unit) l); auto_star.
    apply~ multi_red_proj.
    apply~ multi_red_capp.

  - Case "co_distRcd".
    lets : R_typable_empty H.
    lets : R_halts H.
    unfold halts in *.
    destruct H1 as (v & ? & ?).
    lets : preservation_multi_step  H0 H2.
    lets* (v1 & v2 & ? & ? & ?) : prod_canonical H3.
    substs.
    inverts H3.
    lets~ (v1' & ?): rcd_canonical H10.
    lets~ (v2' & ?): rcd_canonical H12.
    substs.
    inverts H10.
    inverts H12.
    inverts H5.
    inverts H4.

    unfold R in *.
    fold R in *.
    destructs H.
    destructs H4.

    apply multistep_preserves_R with (t' := v1') in H13; auto_star.
    apply multistep_preserves_R with (t' := v2') in H11; auto_star.


    splits*.

    unfolds.
    exists (trm_rcd l (trm_pair v1' v2')).
    splits~.
    apply star_trans with (b := trm_capp (co_distRcd l) (trm_pair (trm_rcd l v1') (trm_rcd l v2'))); auto.
    apply~ multi_red_capp.
    unfolds.
    exists (trm_pair v1' v2').
    splits~.
    apply star_trans with (b := trm_proj (trm_capp (co_distRcd l) (trm_pair (trm_rcd l v1') (trm_rcd l v2'))) l); auto.
    apply~ multi_red_proj.
    apply~ multi_red_capp.
    apply star_trans with (b := trm_proj (trm_rcd l (trm_pair v1' v2')) l); auto.

    apply multistep_preserves_R' with (t' := v1'); auto_star.
    apply star_trans with (b := trm_capp co_proj1 (trm_pair v1' v2')); auto_star.
    apply~ multi_red_capp.
    apply star_trans with (b := trm_proj (trm_rcd l (trm_pair v1' v2')) l); auto.
    apply~ multi_red_proj.
    apply star_trans with (b := trm_capp (co_distRcd l) (trm_pair (trm_rcd l v1') (trm_rcd l v2'))); auto.
    apply~ multi_red_capp.

    apply multistep_preserves_R' with (t' := v2'); auto_star.
    apply star_trans with (b := trm_capp co_proj2 (trm_pair v1' v2')); auto_star.
    apply~ multi_red_capp.
    apply star_trans with (b := trm_proj (trm_rcd l (trm_pair v1' v2')) l); auto.
    apply~ multi_red_proj.
    apply star_trans with (b := trm_capp (co_distRcd l) (trm_pair (trm_rcd l v1') (trm_rcd l v2'))); auto.
    apply~ multi_red_capp.

    apply star_trans with (b := trm_proj (trm_capp co_proj2 (trm_pair (trm_rcd l v1') (trm_rcd l v2'))) l); auto.
    apply~ multi_red_proj.
    apply~ multi_red_capp.
    apply star_trans with (b := trm_proj (trm_rcd l v2') l); auto.

    apply star_trans with (b := trm_proj (trm_capp co_proj1 (trm_pair (trm_rcd l v1') (trm_rcd l v2'))) l); auto.
    apply~ multi_red_proj.
    apply~ multi_red_capp.
    apply star_trans with (b := trm_proj (trm_rcd l v1') l); auto.


Qed.

Lemma msubst_R : forall Γ γ t T,
    Γ |= t ~: T ->
    instantiation Γ γ ->
    R T (msubst γ t).
Proof.
  introv Typ.
  gen γ.
  induction Typ; intros.


  - Case "trm_unit".
    rewrite msubst_unit.
    splits~.
    apply~ value_halts.

  - Case "trm_lit".
    rewrite msubst_lit.
    splits~.
    apply~ value_halts.

  - Case "trm_var".
    destruct (instantiation_domains_match H1 H0) as [t P].
    eapply instantiation_R; eauto.
    rewrite msubst_var.
    lets : binds_get P.
    sapply uniq_gamma; eauto.
    rewrite H2. auto. eapply instantiation_env_closed; eauto.

  - Case "trm_arrow".
    rewrite msubst_abs.
    assert (WT : nil |= trm_abs (msubst γ e) ~: a_arrow T1 T2).
    {
      assert (G |= trm_abs e ~: a_arrow T1 T2).
      auto_star.
      lets : msubst_preserves_typing H1 H2.
      rewrite~ msubst_abs in H3.
    }

    unfold R. fold R. splits~.
    apply~ value_halts.

    intros.
    destruct (R_halts _ _ H2) as [v [Q P]].
    pose proof (multistep_preserves_R _ _ _ P H2).
    pick fresh x.
    assert (Ins : instantiation ((x ~ T1) ++ G) ((x ~ v) ++ γ)).
    sapply~ V_cons.
    lets* : H0 x ((x ~ v) ++ γ) Ins.
    rewrite~ msubst_open in H4.

    apply multistep_preserves_R' with (msubst γ e ^^ v).
    lets* : R_typable_empty H2.
    apply star_trans with (b := trm_app (trm_abs (msubst γ e)) v).
    apply~ multi_red_app.
    apply~ star_step.
    auto.
    simpls.
    splits~.
    unfold closed.
    lets : R_typable_empty H3.
    lets : value_no_fv H5.
    intros.
    rewrite H6.
    solve_notin.
    sapply instantiation_env_closed; eauto.


  - Case "trm_app".
    rewrite msubst_app.
    forwards* P1 : IHTyp1.
    forwards* P2 : IHTyp2.
    apply P1 in P2; auto.

  - Case "trm_prod".
    rewrite msubst_pair.
    forwards* P1 : IHTyp1.
    forwards* P2 : IHTyp2.
    unfold R.
    fold R.
    lets : R_typable_empty P1.
    lets : R_typable_empty P2.
    lets : R_halts P1.
    lets : R_halts P2.
    unfold halts in *.
    destruct H2 as (v1 & ? & ?).
    destruct H3 as (v2 & ? & ?).
    lets : preservation_multi_step  H0 H4.
    lets : preservation_multi_step  H1 H5.

    splits~.
    exists~ (trm_pair v1 v2).
    splits~.
    apply~ multi_red_pair.

    apply multistep_preserves_R' with (trm_capp co_proj1 (trm_pair v1 v2)).
    auto_star.
    apply~ multi_red_capp.
    apply~ multi_red_pair.
    apply multistep_preserves_R' with v1.
    auto_star.
    apply~ star_one.
    apply multistep_preserves_R with (msubst γ e1); auto.

    apply multistep_preserves_R' with (trm_capp co_proj2 (trm_pair v1 v2)).
    auto_star.
    apply~ multi_red_capp.
    apply~ multi_red_pair.
    apply multistep_preserves_R' with v2.
    auto_star.
    apply~ star_one.
    apply multistep_preserves_R with (msubst γ e2); auto.

  - Case "trm_capp".
    rewrite msubst_capp.
    lets : IHTyp H0.
    eapply R_capp; eauto.

  - Case "trm_rcd".
    lets : IHTyp H.
    lets : R_typable_empty H0.
    lets : R_halts H0.
    unfold halts in *.
    destruct H2 as (v & ? & ?).
    lets : preservation_multi_step  H1 H3.

    rewrite msubst_rcd.
    unfold R.
    fold R.
    splits~.

    exists (trm_rcd l v).
    splits~.
    apply~ multi_red_rcd.

    apply multistep_preserves_R' with (trm_proj (trm_rcd l v) l).
    auto_star.
    apply~ multi_red_proj.
    apply~ multi_red_rcd.
    apply multistep_preserves_R' with v.
    auto_star.
    apply~ star_one.
    apply multistep_preserves_R with (msubst γ e); auto.

  - Case "trm_proj".
    rewrite msubst_proj.
    lets Imp : IHTyp H.
    lets : R_typable_empty Imp.
    lets : R_halts Imp.
    unfold halts in *.
    destruct H1 as (v & ? & ?).
    lets : preservation_multi_step  H0 H2.
    lets* : rcd_canonical H3.
    destruct H4 as (v' & ?).
    substs.
    inverts H3.
    inverts H1.
    destruct Imp as (? & ? & Imp).

    apply multistep_preserves_R with (t' := trm_proj (trm_rcd l v') l) in Imp.
    apply multistep_preserves_R with (t' := v') in Imp; auto_star.

    apply multistep_preserves_R' with (trm_proj (trm_rcd l v') l); auto_star.
    apply~ multi_red_proj.
    apply multistep_preserves_R' with v'; auto_star.
    apply~ multi_red_proj.

Qed.






Theorem normalization : forall t T,
    nil |= t ~: T ->
    halts t.
Proof.
  intros.
  replace t with (msubst nil t) by reflexivity.
  apply (@R_halts T).
  apply (msubst_R nil); eauto.
  eapply V_nil.
Qed.
