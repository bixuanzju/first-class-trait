
Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import target_inf.

Definition relation := exp -> exp -> Prop.



Section Star.

  Variable R : relation.

  Inductive star: relation :=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

  Lemma star_one:
    forall a b, R a b -> star a b.
  Proof.
    eauto using star.
  Qed.

  Lemma star_trans:
    forall a b, star a b -> forall c, star b c -> star a c.
  Proof.
    induction 1; eauto using star.
  Qed.


  Hypothesis R_functional:
    forall a b c, R a b -> R a c -> b = c.

  Lemma star_star_inv:
    forall a b, star a b -> forall c, star a c -> star b c \/ star c b.
  Proof.
    induction 1; intros.
    - auto.
    - inversion H1; subst.
      + right. eauto using star.
      + assert (b = b0) by (eapply R_functional; eauto). subst b0.
        apply IHstar; auto.
  Qed.

  Definition irred a : Prop := forall b, ~(R a b).

  Lemma finseq_unique:
    forall a b b',
      star a b -> irred b ->
      star a b' -> irred b' ->
      b = b'.
  Proof.
    intros. destruct (star_star_inv _ _ H _ H1).
    - inversion H3; subst. auto. elim (H0 _ H4).
    - inversion H3; subst. auto. elim (H2 _ H4).
  Qed.


End Star.

Hint Constructors star.

Hint Resolve star_trans star_one.



Lemma value_irred : forall v,
    value v -> irred step v.
Proof.
  intros.
  induction H; unfolds; try solve [intros b C; inverts C].

  intros b C.
  inverts C.
  unfolds in IHvalue1.
  tryfalse*.
  unfolds in IHvalue2.
  tryfalse*.

  intros b C.
  inverts C.
  unfolds in IHvalue.
  tryfalse*.
  intros b C.
  inverts C.
  unfolds in IHvalue.
  tryfalse*.

  unfolds in IHvalue.
  intros b C.
  inverts C.
  tryfalse*.

  unfolds in IHvalue.
  intros b C.
  inverts C.
  tryfalse*.
Qed.


Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0).
Notation "t ^^ u"       := (open_exp_wrt_exp t u) (at level 67).
Notation "e ^ x"        := (open_exp_wrt_exp e (trm_var_f x)).


Notation "c |= T1 ~> T2" := (cotyp c T1 T2) (at level 69).
Notation "E |= t ~: T" := (typing E t T) (at level 69).

(* Notation "t  t'" := (step t t') (at level 68). *)

Notation "R 'star'" := (star R) (at level 69).

Notation "t ->* t'" := (step star t t') (at level 68).

Notation "'|' A '|'" := (ptyp2styp A) (at level 60).

Notation "'∥' Γ '∥'" := (map ptyp2styp Γ) (at level 60).

Notation "A ≺: B ⇝ co " := (sub A B co) (at level 45).

Notation "Γ ⊢ E ⇒ A ⇝ t" := (has_type Γ E Inf A t) (at level 45).

Notation "Γ ⊢ E ⇐ A ⇝ t" := (has_type Γ E Chk A t) (at level 45).


(** [x # E] to be read x fresh from E captures the fact that
    x is unbound in E . *)

Notation "x '#' E" := (x \notin (dom E)) (at level 67) : env_scope.

Definition env := list (atom * exp).


Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  let E := gather_atoms_with (fun x : ctx => dom x) in
  let E := gather_atoms_with (fun x : sctx => dom x) in
  let F := gather_atoms_with (fun x : sctx => dom (∥ x ∥)) in
  let G := gather_atoms_with (fun x : env => dom x) in
  constr:(A `union` B `union` C `union` D `union` E `union` F `union` G).


(* ********************************************************************** *)
(** ** Regularity of relations *)

(** A typing relation holds only if the environment has no
   duplicated keys and the pre-term is locally-closed. *)

Lemma typing_regular : forall E e T,
  typing E e T -> uniq E /\ lc_exp e.
Proof.
  split; induction* H.
  pick fresh y. forwards~ : (H0 y).
  solve_uniq.
Qed.

(** The value predicate only holds on locally-closed terms. *)

Lemma value_regular : forall e,
  value e -> lc_exp e.
Proof.
  induction 1; autos*.
Qed.


(** A reduction relation only holds on pairs of locally-closed terms. *)

Lemma red_regular : forall e e',
  step e e' -> lc_exp e /\ lc_exp e'.
Proof.
  induction 1; autos* value_regular.
  splits~.
  splits~.
  splits~.
  splits~.
  apply lc_body_exp_wrt_exp; autos* value_regular.
  apply lc_body_trm_abs_1; auto.
Qed.

(** Automation for reasoning on well-formedness. *)

Hint Extern 1 (uniq ?E) =>
  match goal with
  | H: typing E _ _ |- _ => apply (proj1 (typing_regular _ _ _ H))
  end.

Hint Extern 1 (lc_exp ?t) =>
  match goal with
  | H: typing _ t _ |- _ => apply (proj2 (typing_regular _ _ _ H))
  | H: step t _ |- _ => apply (proj1 (red_regular _ _ H))
  | H: step _ t |- _ => apply (proj2 (red_regular _ _ H))
  | H: value t |- _ => apply (value_regular _ H)
  end.


(** Other properties *)

Lemma pair_type : forall v T1 T2,
    value v ->
    nil |= trm_capp co_proj1 v ~: T1 ->
    nil |= trm_capp co_proj2 v ~: T2 ->
    nil |= v ~: (a_prod T1 T2).
Proof.
  introv Val Ty1 Ty2.

  destruct* Val.

  inverts Ty1;
  inverts H2;
  inverts H4.

  inverts Ty1;
  inverts H2;
  inverts H4.

  inverts Ty1;
  inverts H3;
  inverts H5.

  inverts Ty1.
  inverts H2.
  inverts H4.
  inverts Ty2.
  inverts H2.
  inverts~ H5.

  inverts Ty1.
  inverts H2.
  inverts H4.


  inverts Ty1.
  inverts H4.
  inverts H2.
  inverts H5.

  inverts Ty1.
  inverts H4.
  inverts H2.
  inverts H5.


  inverts Ty1.
  inverts H4.
  inverts H2.
  inverts H5.
Qed.


Lemma fv_in_dom : forall G e T,
    typing G e T -> fv_exp e [<=] dom G.
Proof.
  intros G e T H.
  induction H; simpl; try fsetdec.
  - Case "typing_var".
    apply binds_In in H0.
    fsetdec.
  - Case "typing_abs".
    pick fresh x.
    assert (Fx : fv_exp (e ^ x) [<=] dom ([(x,T1)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_exp e [<=] fv_exp (e ^ x)) by
        eapply fv_exp_open_exp_wrt_exp_lower.
    fsetdec.
Qed.


Lemma value_no_fv : forall v T,
    nil |= v ~: T ->
    fv_exp v [=] {}.
Proof.
  introv Typ.
  forwards * : fv_in_dom Typ.
  fsetdec.
Qed.


Lemma value_no_step' : forall v1 v2,
    value v1 ->
    step v1 v2 ->
    v2 = v1.
Proof.
  introv V Sp.
  induction Sp; inverts V; try rewrite* IHSp.
Qed.

Lemma value_no_step : forall v1 v2,
    value v1 ->
    v1 ->* v2 ->
    v2 = v1.
Proof.
  introv ? Red.
  induction* Red.
  lets : value_irred H.
  pose (H1 b).
  tryfalse.
Qed.



Lemma notin_trans : forall G x,
    x `notin` dom G ->
    x `notin` dom (∥ G ∥).
Proof.
  intros.
  induction G; solve_notin.
Qed.





Lemma multi_red_capp : forall c t t',
    t ->* t' -> (trm_capp c t) ->* (trm_capp c t').
Proof.
  intros.
  induction* H.
Qed.





Lemma multi_red_app : forall v t t',
    value v -> t ->* t' -> (trm_app v t) ->* (trm_app v t').
Proof.
  introv ? Red.
  induction* Red.
Qed.




Lemma multi_red_app2 : forall t1 t2 t1',
    lc_exp t2 -> t1 ->* t1' -> (trm_app t1 t2) ->* (trm_app t1' t2).
Proof.
  introv ? Red.
  induction* Red.
Qed.



Lemma multi_red_pair1 : forall t1 t2 t1',
    lc_exp t2 ->
    t1 ->* t1' ->
    (trm_pair t1 t2) ->* (trm_pair t1' t2).
Proof.
  introv ? Red.
  induction* Red.
Qed.


Lemma multi_red_pair2 : forall v1 t2 t2',
    value v1 ->
    t2 ->* t2' ->
    (trm_pair v1 t2) ->* (trm_pair v1 t2').
Proof.
  introv ? Red.
  induction* Red.
Qed.

Lemma multi_red_pair : forall t1 t2 v1 v2,
    value v1 -> lc_exp t2 ->
    t1 ->* v1 -> t2 ->* v2 ->
    (trm_pair t1 t2) ->* (trm_pair v1 v2).
Proof.
  intros.
  apply star_trans with (b := trm_pair v1 t2).
  sapply* multi_red_pair1.
  sapply* multi_red_pair2.
Qed.


Lemma multi_red_rcd : forall t t' l,
    t ->* t' ->
    trm_rcd l t ->* trm_rcd l t'.
Proof.
  intros.
  induction* H.
Qed.


Lemma multi_red_proj : forall t t' l,
    t ->* t' ->
    trm_proj t l ->* trm_proj t' l.
Proof.
  intros.
  induction* H.
Qed.



Ltac sweet :=
  match goal with
  | H : value ?t, H1 : step ?t ?e |- _ =>
    forwards * :  (value_irred _ H e)
  end.


Lemma step_unique: forall (t t1 t2 : exp),
  step t t1 -> step t t2 -> t1 = t2.
Proof.
  introv Red1.
  gen t2.
  induction Red1; introv Red2.


  (* capp *)
  inverts* Red2; sweet.
  inverts* Red2; sweet.
  inverts* Red2; sweet.
  inverts* Red2. inverts H3. inverts H4. inverts H3.
  inverts* Red2; [inverts* H5; sweet | sweet].
  inverts* Red2; sweet.
  inverts* Red2;  assert (value (trm_capp co_distArr (trm_pair v1 v2))) by auto; sweet.
  inverts* Red2; assert (value (trm_pair v1 v2)) by auto; sweet.
  inverts* Red2; assert (value (trm_pair v1 v2)) by auto; sweet.
  inverts* Red2.
  forwards * : value_irred (trm_rcd l v); apply H0 in H3; tryfalse.

  inverts* Red2.
  forwards * : value_irred (trm_unit); apply H in H2; tryfalse.

  inverts* Red2.
  forwards * : value_irred (trm_pair (trm_rcd l v1) (trm_rcd l v2)); apply H1 in H4; tryfalse.


  (* trm_proj *)
  inverts* Red2.
  forwards * : value_irred (trm_rcd l v); apply H0 in H3; tryfalse.


  (* abs *)
  inverts* Red2; assert (value (trm_abs e)) by auto; sweet.

  (* app1 *)
  inverts* Red2; try sweet.
  forwards * : value_irred (trm_capp co_topArr trm_unit); apply H0 in Red1; tryfalse.
  forwards * : value_irred (trm_capp (co_arr c1 c2) v1); apply H0 in Red1; tryfalse.
  forwards * : value_irred (trm_capp co_distArr (trm_pair v1 v2)); apply H0 in Red1; tryfalse.
  forwards * : value_irred (trm_abs e); apply H0 in Red1; tryfalse.
  erewrite IHRed1; eauto.

  (* app2 *)
  inverts* Red2; try sweet.
  inverts Red1.
  erewrite IHRed1; eauto.
  inverts* Red2; [forwards * : IHRed1; substs* | sweet].
  inverts* Red2; [sweet | forwards * : IHRed1; substs*].

  inverts* Red2; try sweet.
  forwards * : value_irred (trm_pair t2 v2); apply H in Red1; tryfalse.
  forwards * : value_irred (trm_pair v1 t2); apply H in Red1; tryfalse.
  forwards * : value_irred (trm_rcd l0 v); apply H in Red1; tryfalse.
  forwards * : value_irred (trm_unit); apply H in Red1; tryfalse.
  forwards * : value_irred (trm_pair (trm_rcd l0 v1) (trm_rcd l0 v2)); apply H in Red1; tryfalse.

  erewrite IHRed1; eauto.


  inverts* Red2.
  erewrite IHRed1; eauto.

  inverts* Red2; try sweet.
  forwards * : value_irred (trm_rcd l t2); apply H in Red1; tryfalse.


  erewrite IHRed1; eauto.

Qed.




Lemma value_unique: forall t v1 v2,
  value v1 -> value v2 -> t ->* v1 -> t ->* v2 -> v1 = v2.
Proof.
  introv Val1 Val2 ? ?.
  lets : value_irred Val1.
  lets : value_irred Val2.
  forwards * : finseq_unique step_unique H H0.
Qed.


Lemma and_false1 : forall A1 A2,
    styp_and A1 A2 = A1 -> False.
Proof.
  intros A1.
  induction A1; intros; inverts* H.
Qed.

Lemma and_false2 : forall A2 A1,
    styp_and A1 A2 = A2 -> False.
Proof.
  intros A2.
  induction A2; intros; inverts* H.
Qed.
