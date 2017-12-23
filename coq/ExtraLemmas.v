
Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        Coherence
        Infrastructure
        Coercion_Compatibility
        Logical_Relation_Def
        Logical_Relation_Infrastructure
        Source_Property
        Normalize
        Compatibility_Lemma.




Lemma merge_is_neutral_log : forall G E1 E2 t1 t2 A dir1 dir2,
    has_type G E1 dir1 A t1 ->
    has_type G (e_merge E1 E2) dir2 A t2 ->
    rel_e_open (∥ G ∥) (∥ G ∥) t1 t2 (| A |) (| A |).
Proof with eauto.
  introv H1 H2.
  destruct dir1; destruct dir2.

  - Case "=> and =>".
    inverts H2.
    lets : inference_unique H1 H3.
    forwards* : and_false1 H.

  - Case "=> and <=".
    inverts H2.
    inverts H.
    lets : inference_unique H1 H4.
    substs.
    lets Imp1 : coherence_log H1 H4.
    lets Imp2 : coherence_log H6 H6.
    lets Co : subtyping_well_type_coercion H0.
    lets : elaboration_well_type_term H1.
    lets : elaboration_well_type_term H4.
    lets : elaboration_well_type_term H6.
    simpls.
    sapply coercion_compatibility2...
    apply compat_pair2; splits~.
    apply disjoint_rel_e_open...


  - Case "<= and =>".
    inverts H2.
    inverts H1.
    lets : inference_unique H3 H.
    substs.
    lets Imp1 : coherence_log H H3.
    lets Imp2 : coherence_log H5 H5.
    lets Co : subtyping_well_type_coercion H0.
    simpls.

    sapply coercion_compatibility1...
    apply compat_pair2; splits...
    lets : elaboration_well_type_term H3.
    lets : elaboration_well_type_term H5.
    lets : elaboration_well_type_term H.
    apply disjoint_rel_e_open...


  - Case "<= and <=".
    inverts H2.
    inverts H.
    inverts H1.
    inverts H4.

    lets : inference_unique H4 H.
    substs.
    lets Imp1 : coherence_log H H4.
    lets Imp2 : coherence_log H6 H6.
    lets Co1 : subtyping_well_type_coercion H0.
    lets Co2 : subtyping_well_type_coercion H2.
    lets : elaboration_well_type_term H4.
    lets : elaboration_well_type_term H6.
    lets : elaboration_well_type_term H.
    simpls.
    sapply coercion_compatibility2...
    sapply coercion_compatibility1...
    apply compat_pair2; splits~.
    apply disjoint_rel_e_open...

Qed.


Lemma merge_is_neutral_ctx : forall G G' E1 E2 t1 t2 A A' dir dir' C c,
    CTyp C G dir A G' dir' A' c ->
    has_type G E1 dir A t1 ->
    has_type G (e_merge E1 E2) dir A t2 ->
    rel_e_open (∥ G' ∥) (∥ G' ∥) (appctx c t1) (appctx c t2) (| A' |) (| A' |).
Proof.
  introv CC Typ1 Typ2.
  lets* : merge_is_neutral_log Typ1 Typ2.
  sapply* congruence.
Qed.



Lemma merge_commutativity_log: forall G E1 E2 A t1 t2 dir,
    has_type G (e_merge E1 E2) dir A t1 ->
    has_type G (e_merge E2 E1) dir A t2 ->
    rel_e_open (∥ G ∥) (∥ G ∥) t1 t2 (| A |) (| A |).
Proof with eauto.
  introv H1 H2.
  destruct dir.


  - Case "=> and =>".
    inverts H1.
    inverts H2.
    lets : inference_unique H3 H9.
    substs.
    simpls.
    lets Imp1 : coherence_log H3 H9.
    lets Imp2 : coherence_log H5 H8.
    lets : elaboration_well_type_term H3.
    lets : elaboration_well_type_term H5.
    lets : elaboration_well_type_term H8.
    lets : elaboration_well_type_term H9.
    apply compat_pair1; splits~;
    apply compat_pair2; splits~.
    apply disjoint_rel_e_open...
    apply disjoint_rel_e_open...


  - Case "<= and <=" .
    inverts H1.
    inverts H2.
    inverts H.
    inverts H1.
    lets : inference_unique H5 H9.
    lets : inference_unique H7 H4.
    substs.
    lets Co1 : subtyping_well_type_coercion H0.
    lets Co2 : subtyping_well_type_coercion H3.
    lets : elaboration_well_type_term H5.
    lets : elaboration_well_type_term H7.
    lets : elaboration_well_type_term H4.
    lets : elaboration_well_type_term H9.
    simpls.
    lets Imp1 : coherence_log H5 H9.
    lets Imp2 : coherence_log H7 H4.


    eapply coercion_compatibility1...
    eapply coercion_compatibility2...

    apply compat_pair1; splits~.
    apply compat_pair2; splits~;
    apply disjoint_rel_e_open...
    apply compat_pair2; splits~;
    apply disjoint_rel_e_open...

Qed.


Lemma merge_commutativity_ctx : forall G G' E1 E2 t1 t2 A A' dir dir' C c,
    CTyp C G dir A G' dir' A' c ->
    has_type G (e_merge E1 E2) dir A t1 ->
    has_type G (e_merge E2 E1) dir A t2 ->
    rel_e_open (∥ G' ∥) (∥ G' ∥) (appctx c t1) (appctx c t2) (| A' |) (| A' |).
Proof.
  introv CC Typ1 Typ2.
  lets* : merge_commutativity_log Typ1 Typ2.
  sapply* congruence.
Qed.



Lemma merge_is_associate_log : forall G E1 E2 E3 t1 t2 A dir,
    has_type G (e_merge (e_merge E1 E2) E3) dir A t1 ->
    has_type G (e_merge E1 (e_merge E2 E3)) dir A t2 ->
    rel_e_open (∥ G ∥) (∥ G ∥) t1 t2 (| A |) (| A |).
Proof with eauto.
  introv H1 H2.
  destruct dir.


  - Case "=> and =>".

    inverts H1.
    inverts H2.
    inverts H3.
    inverts H9.
    lets : inference_unique H5 H10.
    forwards* : and_false2 H.

  - Case "<= and <=".

    inverts H1.
    inverts H2.
    inverts H.
    inverts H1.
    inverts H5.
    inverts H9.

    lets : inference_unique H5 H11.
    lets : inference_unique H7 H13.
    lets : inference_unique H2 H4.
    substs.


    lets Imp1 : coherence_log H2 H4.
    lets Imp2 : coherence_log H7 H13.
    lets Imp3 : coherence_log H11 H5.


    apply disjoint_and in H10.
    destruct H10.

    apply disjoint_commute in H8.
    apply disjoint_and in H8.
    destruct H8.



    lets Co1 : subtyping_well_type_coercion H0.
    lets Co2 : subtyping_well_type_coercion H3.
    simpls.


    lets : elaboration_well_type_term H7.
    lets : elaboration_well_type_term H4.
    lets : elaboration_well_type_term H2.
    lets : elaboration_well_type_term H11.
    lets : elaboration_well_type_term H5.
    lets : elaboration_well_type_term H13.

    sapply coercion_compatibility1...
    sapply coercion_compatibility2...

    apply compat_pair1; splits~.
    apply compat_pair1; splits~;
    apply compat_pair2; splits~.

    apply compat_pair2; splits~.
    apply disjoint_rel_e_open...
    apply disjoint_rel_e_open...
    apply disjoint_rel_e_open...
    apply disjoint_commute...


    apply compat_pair2; splits~.
    apply disjoint_rel_e_open...


    apply compat_pair2; splits~.
    apply disjoint_rel_e_open...

    apply compat_pair2; splits~.
    apply disjoint_rel_e_open...
Qed.



Lemma merge_is_associate_ctx : forall G G' E1 E2 E3 t1 t2 A A' dir dir' C c,
    CTyp C G dir A G' dir' A' c ->
    has_type G (e_merge (e_merge E1 E2) E3) dir A t1 ->
    has_type G (e_merge E1 (e_merge E2 E3)) dir A t2 ->
    rel_e_open (∥ G' ∥) (∥ G' ∥) (appctx c t1) (appctx c t2) (| A' |) (| A' |).
Proof.
  introv CC Typ1 Typ2.
  lets* : merge_is_associate_log Typ1 Typ2.
  sapply* congruence.
Qed.


Lemma merge_is_associate : forall Γ E1 E2 E3 A,
    ctx_equiv Γ (e_merge (e_merge E1 E2) E3) (e_merge E1 (e_merge E2 E3)) A.
Proof.
  intros.
  unfolds.
  introv Ty1 Ty2 CTy.
  lets H : merge_is_associate_ctx CTy Ty1 Ty2.
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




Corollary merge_is_neutral : forall Γ E1 E2 A,
    ctx_equiv Γ E1 (e_merge E1 E2) A.
Proof.
  intros.
  unfolds.
  introv Ty1 Ty2 CTy.
  lets H : merge_is_neutral_ctx CTy Ty1 Ty2.
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


Corollary merge_commutativity : forall Γ E1 E2 A,
    ctx_equiv Γ (e_merge E1 E2) (e_merge E2 E1) A.
Proof.
  intros.
  unfolds.
  introv Ty1 Ty2 CTy.
  lets H : merge_commutativity_ctx CTy Ty1 Ty2.
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









Lemma intersection_commutativity: forall G E A B t1 t2 dir1 dir2,
    has_type G E dir1 (styp_and A B) t1 ->
    has_type G E dir2 (styp_and B A) t2 ->
    rel_e_open (∥ G ∥) (∥ G ∥) t1 t2 (a_prod (| A |) (| B |)) (a_prod (| B |) (| A |)).
Proof.
  introv H1 H2.

  destruct dir1; destruct dir2.

  - Case "=> and =>".

    lets : inference_unique H1 H2.
    inverts H.

    lets : coherence_log H1 H2.
    simpls*.

  - Case "=> and <=".
    inverts H2.
    lets : inference_unique H1 H.
    substs.
    lets : coherence_log H1 H.
    lets Co : subtyping_well_type_coercion H0.
    simpls.
    lets* : coercion_compatibility2 Co H2.

  - Case "<= and =>".
    inverts H1.
    lets : inference_unique H2 H.
    substs.
    lets : coherence_log H H2.
    lets Co : subtyping_well_type_coercion H0.
    simpls.
    lets* : coercion_compatibility1 Co H1.

  - Case "<= and <=".
    inverts H1.
    inverts H2.
    lets : inference_unique H H1.
    substs.
    lets : coherence_log H H1.
    lets Co1 : subtyping_well_type_coercion H0.
    lets Co2 : subtyping_well_type_coercion H3.
    lets* : coercion_compatibility1 Co1 H2.
    lets* : coercion_compatibility2 Co2 H4.
Qed.
