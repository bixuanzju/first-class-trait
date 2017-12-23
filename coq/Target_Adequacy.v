
Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import 
  target_inf
  Infrastructure
  Target_Safety.

(***************************************************************************)
(** * Definitions with the exists-fresh quantification *)

(** Terms are locally-closed pre-terms *)

Inductive eterm : exp -> Prop :=
| eterm_var : forall x,
    eterm (trm_var_f x)
| eterm_abs : forall x t1,
    x \notin fv_exp t1 ->
    eterm (t1 ^ x) ->
    eterm (trm_abs t1)
| eterm_app : forall t1 t2,
    eterm t1 ->
    eterm t2 ->
    eterm (trm_app t1 t2)
| eterm_unit : eterm (trm_unit)
| eterm_lit : forall n, eterm (trm_lit n)
| eterm_pair : forall t1 t2,
    eterm t1 ->
    eterm t2 ->
    eterm (trm_pair t1 t2)
| eterm_rcd : forall l t,
    eterm t ->
    eterm (trm_rcd l t)
| eterm_proj : forall l t,
    eterm t ->
    eterm (trm_proj t l)
| eterm_capp : forall c t,
    eterm t ->
    eterm (trm_capp c t).


(** Typing relation *)

Reserved Notation "E |== t ~: T" (at level 69).

Inductive etyping : ctx -> exp -> typ -> Prop :=
| etyping_var : forall E x T,
    uniq E ->
    binds x T E ->
    E |== (trm_var_f x) ~: T
| etyping_abs : forall x E U T t1,
    x \notin dom E \u fv_exp t1 ->
    ([(x , U)] ++ E) |== (t1 ^ x) ~: T ->
    E |== (trm_abs t1) ~: (a_arrow U T)
| etyping_app : forall S T E t1 t2,
    E |== t1 ~: (a_arrow S T) ->
    E |== t2 ~: S ->
    E |== (trm_app t1 t2) ~: T
| etyping_unit : forall E,
    uniq E ->
    E |== trm_unit ~: a_unit
| etyping_lit : forall E n,
    uniq E ->
    E |== (trm_lit n) ~: a_nat
| etyping_pair : forall S T E t1 t2,
    E |== t1 ~: T ->
    E |== t2 ~: S ->
    E |== (trm_pair t1 t2) ~: (a_prod T S)
| etyping_capp : forall E t T T' c,
    E |== t ~: T ->
    c |= T ~> T' ->
    E |== (trm_capp c t) ~: T'

| etyping_proj : forall E t l T,
    E |== t ~: a_rcd l T ->
    E |== (trm_proj t l) ~: T

| etyping_rcd : forall E t l T,
    E |== t ~: T ->
    E |== (trm_rcd l t) ~: (a_rcd l T)

where "E |== t ~: T" := (etyping E t T).

(** Definition of values (only abstractions are values) *)

(* Inductive evalue : trm -> Prop := *)
(*   | evalue_abs : forall t1,  *)
(*       eterm (trm_abs t1) -> evalue (trm_abs t1). *)

(** Reduction relation - one step in call-by-value *)

(* Inductive ered : trm -> trm -> Prop := *)
(*   | ered_beta : forall t1 t2, *)
(*       eterm (trm_abs t1) -> *)
(*       evalue t2 -> *)
(*       ered (trm_app (trm_abs t1) t2) (t1 ^^ t2) *)
(*   | ered_app_1 : forall t1 t1' t2, *)
(*       eterm t2 -> *)
(*       ered t1 t1' -> *)
(*       ered (trm_app t1 t2) (trm_app t1' t2) *)
(*   | ered_app_2 : forall t1 t2 t2', *)
(*       evalue t1 -> *)
(*       ered t2 t2' -> *)
(*       ered (trm_app t1 t2) (trm_app t1 t2'). *)

(* Notation "t -->> t'" := (ered t t') (at level 68). *)

(** Goal is to prove preservation and progress *)

(* Definition epreservation := forall E t t' T, *)
(*   E |== t ~: T -> *)
(*   t -->> t' -> *)
(*   E |== t' ~: T. *)

(* Definition eprogress := forall t T,  *)
(*   empty |== t ~: T -> *)
(*      evalue t  *)
(*   \/ exists t', t -->> t'. *)



(***************************************************************************)
(** * Detailed Proofs of Renaming Lemmas (without high automation)  *)


(* ********************************************************************** *)
(** ** Proving the renaming lemma for [term]. *)

Lemma term_rename : forall x y t,
  lc_exp (t ^ x) ->
  x \notin fv_exp t ->
  y \notin fv_exp t ->
  lc_exp (t ^ y).
Proof.
  introv Wx Frx Fry.
  (* introduce a renaming *)
  rewrite (@subst_exp_intro x).
  (* apply substitution result *)
  apply~ subst_exp_lc_exp.
  (* use the fact that x is fresh *)
  assumption.
Qed.

(* ********************************************************************** *)
(** ** Proving the renaming lemma for [typing]. *)

Lemma typing_rename : forall x y E t U T,
  ([(x, U)] ++ E) |= (t ^ x) ~: T ->
  x \notin dom E \u fv_exp t ->
  y \notin dom E \u fv_exp t ->
  ([(y, U)] ++ E) |= (t ^ y) ~: T.
Proof.
  introv Typx Frx Fry.
  destruct (x == y); subst*.
  (* assert that E is ok *)
  lets K: (proj1 (typing_regular _ _ _ Typx)).
  (* introduce substitution *)
  rewrite~ (@subst_exp_intro x).
  (* apply substitution lemma *)
  rewrite_env (nil ++ [(y, U)] ++ E).
  apply typing_subst with (S := U).
  (* apply weakening lemma *)
  simpl_env.
  apply~ typing_weaken.
  apply~ typ_var.
  solve_uniq.
Qed.


(***************************************************************************)
(** * Proofs of equivalence.  *)



Hint Constructors eterm.

Lemma term_to_eterm : forall t,
  lc_exp t -> eterm t.
Proof.
  induction 1; eauto.
  pick_fresh x. apply~ (@eterm_abs x).
Qed.

Lemma eterm_to_term : forall t,
  eterm t -> lc_exp t.
Proof.
  induction 1; eauto.
  sapply* lc_trm_abs_exists.
Qed.

(* ********************************************************************** *)
(** ** Proving the equivalence of [value] and [evalue] *)

(* Hint Constructors value evalue. *)

(* Lemma value_to_evalue : forall t, *)
(*   value t -> evalue t. *)
(* Proof. *)
(*   lets: term_to_eterm. induction 1; jauto. *)
(* Qed. *)

(* Lemma evalue_to_value : forall t, *)
(*   evalue t -> value t. *)
(* Proof. *)
(*   lets: eterm_to_term. induction 1; jauto. *)
(* Qed. *)

(* ********************************************************************** *)
(** ** Proving the equivalence of [red] and [ered] *)

(* Hint Constructors red ered. *)

(* Lemma red_to_ered : forall t t', *)
(*   red t t' -> ered t t'. *)
(* Proof. *)
(*   lets: term_to_eterm. lets: value_to_evalue. induction 1; jauto. *)
(* Qed. *)

(* Lemma ered_to_red : forall t t', *)
(*   ered t t' -> red t t'. *)
(* Proof. *)
(*   lets: eterm_to_term. lets: evalue_to_value. induction 1; jauto. *)
(* Qed. *)

(* ********************************************************************** *)
(** ** Proving the equivalence of [typing] and [etyping] *)

Hint Constructors etyping.

Lemma typing_to_etyping : forall E t T,
  E |= t ~: T  ->  E |== t ~: T.
Proof.
  induction 1; eauto.
  pick_fresh x. apply~ (@etyping_abs x).
Qed.

Lemma etyping_to_typing : forall E t T,
  E |== t ~: T  ->  E |= t ~: T.
Proof.
  induction 1; eauto.
  pick fresh y and apply typ_abs.
  apply~ typing_rename; auto.
Qed.

(* ********************************************************************** *)
