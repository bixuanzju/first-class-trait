
Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        Infrastructure.


Lemma disjoint_commute : forall A B,
    disjoint A B -> disjoint B A.
Proof.
  introv H.
  induction* H.
Qed.

Lemma disjoint_and : forall A B C,
    disjoint A (styp_and B C) <->
    disjoint A B /\ disjoint A C.
Proof.
  intros.
  splits.
  introv H.
  inductions H; auto_star.
  forwards * (? & ?): IHdisjoint1 B C.
  forwards * (? & ?): IHdisjoint2 B C.


  introv H.
  destruct* H.
Qed.



Lemma subtyping_well_type_coercion : forall A1 A2 c,
    A1 ≺: A2 ⇝ c ->
    c |= | A1 | ~> | A2 |.
Proof.
  introv Sub.
  induction Sub; simpls*.
Qed.

Lemma elaboration_well_type_term : forall Γ E A d t,
    has_type Γ E d A t ->
    ∥ Γ ∥ |= t ~: | A |.
Proof.
  introv Typ.
  induction Typ; simpls*.

  lets* : subtyping_well_type_coercion H.
Qed.


Lemma inference_unique : forall Γ E A1 A2 t1 t2,
    Γ ⊢ E ⇒ A1 ⇝ t1 ->
    Γ ⊢ E ⇒ A2 ⇝ t2 ->
    A1 = A2.
Proof.
  introv Ty1.
  gen_eq Dir : Inf.
  gen A2 t2.
  induction Ty1; introv Eq Ty2; try (inverts* Eq); try (inverts* Ty2).
  - (* t_var *)
    forwards * : binds_unique H0 H4.
  - (* t_app *)
    forwards * : IHTy1_1 H2.
    inverts* H.
  - (* t_and *)
    forwards * : IHTy1_1 H2.
    substs.
    forwards * : IHTy1_2 H4.
    substs*.
  - Case "t_rcd".
    forwards * : IHTy1 H1.
    substs*.
  - Case "t_proj".
    forwards * : IHTy1 H1.
    inverts~ H.
Qed.
