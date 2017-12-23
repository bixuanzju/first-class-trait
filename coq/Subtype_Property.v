
Require Import Metalib.Metatheory.

Require Import LibTactics.

Require Import syntax_ott.

Require Import List. Import ListNotations.




Fixpoint sizeTyp (s : styp) : nat :=
  match s with
  | styp_nat => 0
  | styp_top => 0
  | styp_arrow t1 t2 => S (sizeTyp t1 + sizeTyp t2)
  | styp_and t1 t2 => S (sizeTyp t1 + sizeTyp t2)
  | styp_rcd _ t => S (sizeTyp t)
  end.


Definition size_elem (s : st) : nat :=
  match s with
  | st_ty A => sizeTyp A
  | st_la _ => 0
  end.


Definition sizefs (fs : ls) := fold_right (fun l acc => l + acc) 0 (map size_elem fs).


Definition applyfs (fs : ls) (A : styp) :=
  fold_right (fun el acc =>
                match el with
                | st_ty A => styp_arrow A acc
                | st_la l => styp_rcd l acc
                end) A fs.


(** Lemma 25 *)
Lemma arrowTop : forall fs,
    sub styp_top (applyfs fs styp_top) (calTop fs).
Proof.
  intros.
  induction fs; simpls~.
  destruct a.

  apply S_trans with (A2 := styp_arrow A styp_top); auto.
  apply S_trans with (A2 := styp_arrow styp_top styp_top); auto.
  eapply S_trans; eauto.

  apply S_trans with (A2 := styp_rcd l styp_top); auto.
Qed.


(** Lemma 26 *)
Lemma arrowAnd : forall fs A B,
    sub (styp_and (applyfs fs A) (applyfs fs B))
        (applyfs fs (styp_and A B)) (calAnd fs).
Proof.
  intros fs.
  induction fs; intros; simpls~.
  destruct* a.
Qed.


Lemma applyArrow_append : forall fs B1 B2,
    applyfs (fs ++ [st_ty B1]) B2 = applyfs fs (styp_arrow B1 B2).
Proof.
  intros.
  unfolds.
  rewrite fold_right_app.
  reflexivity.
Qed.

Lemma applyLabel_append : forall fs l A,
    applyfs (fs ++ [st_la l]) A = applyfs fs (styp_rcd l A).
Proof.
  intros.
  unfolds.
  rewrite fold_right_app.
  reflexivity.
Qed.



(** *Soundness *)

Theorem ASub2sub : forall fs A B c,
    ASub fs A B c -> sub A (applyfs fs B) c.
Proof.
  introv H.
  induction* H; simpls*.

  - Case "rcd".
    rewrite applyLabel_append in IHASub; auto.


  - Case "top".
    eapply S_trans; eauto.
    apply arrowTop.


  - Case "and2".

    lets R : S_and IHASub1 IHASub2.
    eapply S_trans; eauto.
    apply arrowAnd.


  - Case "arrNat".
    unfold applyfs in IHASub.
    rewrite fold_right_app in IHASub.
    simpls*.

Qed.




(** *Porting Pierce's proofs *)


(** [Rel A] denotes a set of reflexive supertypes of [A] *)
Inductive Rel : styp -> styp -> Prop :=
| R_top : Rel styp_top styp_top
| R_rcd : forall l A B,
    Rel A B ->
    Rel (styp_rcd l A) (styp_rcd l B)
| R_and : forall A B C,
    Rel A C \/ Rel B C \/ C = styp_and A B ->
    Rel (styp_and A B) C
| R_arrow : forall A B B',
    Rel B B' ->
    Rel (styp_arrow A B) (styp_arrow A B')
| R_nat : Rel styp_nat styp_nat.

Hint Constructors Rel.

Notation "A ∈R B" := (Rel B A)  (at level 1).

Notation "A ⊆R B" := (forall C, Rel A C -> Rel B C )  (at level 1).


(** [Rel] is reflexive (Lemma 14) *)
Lemma setRefl : forall A, A ∈R A.
Proof.
  intros.
  induction* A.
Qed.


Lemma setAnd : forall A B C,
    (styp_and A B) ∈R C -> A ∈R C /\ B ∈R C.
Proof.
  intros A B C.
  gen A B.
  induction C; introv H.
  inverts H.
  inverts H.
  inverts H.
  branches.
  forwards * : IHC1.
  forwards * : IHC2.
  inverts H.
  splits.
  constructor.
  branch 1.
  apply setRefl.
  constructor.
  branch 2.
  apply setRefl.
  inverts H.
  inverts H.
Qed.


(** [Rel] is transitive *)
Lemma setTrans : forall A B C,
    A ∈R B ->
    B ∈R C ->
    A ∈R C.
Proof.
  intros A B C.
  gen A C.
  induction B; introv AsubB BsubC; try inverts* AsubB.

  - Case "styp_and".
    lets (? & ?): setAnd BsubC.
    branches.
    forwards * : IHB1.
    forwards * : IHB2.
    substs*.

  - Case "styp_arrow".
    gen B1 B2 B'.
    induction C; intros.

    + inverts BsubC.
    + inverts BsubC.
    + inverts BsubC.
      branches.
      SCase "B1 -> B2 ∈R C1".
        constructor.
        branch 1.
        sapply IHC1; eauto.
      SCase "B1 -> B2 ∈R C2".
        constructor.
        branch 2.
        sapply IHC2; eauto.
      SCase "Impossible case".
        inverts H.
    + inverts BsubC.
      constructor*.
    + inverts BsubC.

  - Case "styp_rcd".
    gen B B0.
    induction C; intros; try solve [inverts* BsubC].
    + inverts BsubC.
      branches.
      auto_star.
      auto_star.
      inverts H.
Qed.


(** Lemma 15

Pierce's proof of this lemma is very vague, which is not that obvious. We need
[setTrans] to make progress.

 *)
Lemma setSubset : forall A B,
    A ∈R B ->
    A ⊆R B.
Proof.
  introv H.
  induction* H.

  - Case "R_rcd".
    intros D HH.
    inverts* HH.

  - Case "R_and".
    branches.
    intros D HH.
    constructor.
    branch 1.
    sapply setTrans; eauto.
    constructor.
    branch 2.
    sapply setTrans; eauto.
    substs~.

  - Case "R_arrow".
    intros C HH.
    inverts HH.
    constructor.
    sapply setTrans; eauto.

Qed.


(** Lemma 16 *)
Lemma setList : forall fs A B,
    (applyfs fs A) ∈R (applyfs fs (styp_and A B)) /\
    (applyfs fs B) ∈R (applyfs fs (styp_and A B)).
Proof.
  intros fs.
  induction fs; intros; simpls.

  splits.
  constructor; branch 1; apply setRefl.
  constructor; branch 2; apply setRefl.

  destruct a;
  specializes IHfs A B.
Qed.


Require Import Omega.

Lemma sizefs_cons1 : forall s fs,
    sizefs (s :: fs) = size_elem s + sizefs fs.
Proof.
  intros.
  simpls~.
Qed.

Lemma sizefs_cons2 : forall s fs,
    sizefs (fs ++ [s]) = sizefs fs + size_elem s.
Proof.
  intros.
  induction fs.
  unfolds.
  simpls~.

  simpls.
  rewrite sizefs_cons1.
  rewrite IHfs.
  rewrite sizefs_cons1.
  omega.
Qed.


Lemma sizefs_nil : sizefs [] = 0.
Proof.
  unfolds.
  simpls~.
Qed.



Hint Rewrite sizefs_cons1 sizefs_cons2 sizefs_nil : base.

Tactic Notation "my_autorewrite" "in" "*" :=
  autorewrite_in_star_patch
    ltac:(fun tt => autorewrite with base).


Lemma set2Sub_aux : forall k fs A B,
    sizeTyp A + sizeTyp B + sizefs fs <= k ->
    (applyfs fs B) ∈R A ->
    exists c, ASub fs A B c.
Proof with my_autorewrite in * ; simpls; try omega.
  intros k.
  induction k; intros.

  - Case "k = 0".
    inverts H as HSize.
    destruct B...
    + SCase "B = styp_top".
      exists~ (co_trans (calTop fs) co_top).
    + SCase "B = styp_nat".
      destruct A...
      * SSCase "A = styp_top".
        destruct fs.
        inverts H0.
        destruct s;
        inverts H0.
      * SSCase "A = styp_nat".
        destruct fs.
        exists~ co_id.
        destruct s;
        inverts H0.

  - Case "k = S n".
    destruct B; simpls.
    + SCase "B = styp_top".
      exists~ (co_trans (calTop fs) co_top).
    + SCase "B = styp_nat".
      destruct A; simpls.
      * SSCase "A = styp_top".
        destruct fs.
        simpls; inverts H0.
        destruct s; inverts H0.
      * SSCase "A = styp_nat".
        destruct fs.
        exists~ co_id.
        destruct s; inverts H0.
      * SSCase "A = styp_and".
        inverts H0 as HH.
        destruct HH as [HH1 | [HH2 | HH3]].
        apply IHk in HH1...
        destruct HH1 as (c & ?).
        exists~ (co_trans c co_proj1).
        apply IHk in HH2...
        destruct HH2 as (c & ?).
        exists~ (co_trans c co_proj2).
        destruct fs. inverts HH3.
        destruct s; inverts HH3.
      * SSCase "A = styp_arrow".
        destruct fs; try solve [inverts H0].
        destruct s; simpls; try solve [inverts H0].
        inverts H0 as H0.
        lets HH : setRefl A.
        change A with (applyfs [] A) in HH.
        apply IHk in HH...
        destruct HH as (c1 & ?).
        apply IHk in H0...
        destruct H0 as (c2 & ?).
        exists~ (co_arr c1 c2).

      * SSCase "A = styp_rcd".
        destruct fs; try solve [ inverts H0 ].
        destruct s; inverts H0.
        apply IHk in H2...
        destruct H2 as (c & ?).
        exists~ (co_rcd l0 c).

    + SCase "B = styp_and".
      lets (HH1 & HH2): setList fs B1 B2.
      lets H1 : setTrans HH1 H0.
      lets H2 : setTrans HH2 H0.
      apply IHk in H1...
      destruct H1 as (c1 & ?).
      apply IHk in H2...
      destruct H2 as (c2 & ?).
      exists~ (co_trans (calAnd fs) (co_pair c1 c2)).

    + SCase "B = styp_arrow".
      rewrite <- applyArrow_append in H0.
      apply IHk in H0...
      destruct H0 as (c & ?).
      exists~ c.

    + SCase "B = styp_rcd".
      rewrite <- applyLabel_append in H0.
      apply IHk in H0...
      destruct H0 as (c & ?).
      exists~ c.

Qed.



(** Proposition 17 *)
Lemma set2Sub : forall fs A B,
    (applyfs fs B) ∈R A ->
    exists c, ASub fs A B c.
Proof.
  intros.
  apply set2Sub_aux with (sizeTyp A + sizeTyp B + sizefs fs); auto.
Qed.



Inductive Phi : ls -> ls -> Prop :=
| phi_empty : Phi [] []
| phi_cons1 : forall A B c fs1 fs2,
    ASub [] A B c ->
    Phi fs1 fs2 ->
    Phi (st_ty A :: fs1) (st_ty B :: fs2)
| phi_cons2 : forall l fs1 fs2,
    Phi fs1 fs2 ->
    Phi (st_la l :: fs1) (st_la l :: fs2).

Hint Constructors Phi.


Lemma phi_append1 : forall fs1 fs2 A B c,
    Phi fs1 fs2 ->
    ASub [] A B c ->
    Phi (fs1 ++ [st_ty A]) (fs2 ++ [st_ty B]).
Proof.
  introv phi.
  gen A B c.
  induction phi; intros; simpls*.
Qed.


Lemma phi_append2 : forall fs1 fs2 l,
    Phi fs1 fs2 ->
    Phi (fs1 ++ [st_la l]) (fs2 ++ [st_la l]).
Proof.
  introv phi.
  induction phi; intros; simpls*.
Qed.




(** Pierce's proof is wrong: should do complete induction also on [sizefs fs3],
otherwise the induction hypothesis is not applicable *)

Lemma ASub_trans_wrt_Phi_aux : forall k A B C fs1 fs2 fs3 c1 c2,
    sizeTyp A + sizefs fs1 + sizeTyp B + sizefs fs2 + sizeTyp C + sizefs fs3 <= k ->
    ASub fs1 A B c1 ->
    Phi fs3 fs1 ->
    ASub fs2 B C c2 ->
    exists c, ASub (fs3 ++ fs2) A C c.
Proof with my_autorewrite in *; simpls; try omega.
  intros k.
  induction k; introv Sum AsubB phi BsubC.

  - Case "k = 0".
    inverts Sum.
    destruct C...
    + SCase "C = styp_top".
      exists~ (co_trans (calTop (fs3 ++ fs2)) co_top).
    + SCase "C = styp_nat".
      destruct B...
      * SSCase "B = styp_top".
        inverts BsubC.
      * SSCase "B = styp_nat".
        inverts BsubC.
        destruct A...
        ** SSSCase "A = styp_top".
           inverts AsubB.
        ** SSSCase "A = styp_nat".
           inverts AsubB.
           inverts phi.
           exists~ co_id.

  - Case "k = S n".
    destruct C...
    + SCase "C = styp_top".
      exists~ (co_trans (calTop (fs3 ++ fs2)) co_top).
    + SCase "C = styp_nat".
      destruct B...
      * SSCase "B = styp_top".
        inverts BsubC.
      * SSCase "B = styp_nat".
        inverts BsubC.
        destruct A...
        ** SSSCase "A = styp_top".
           inverts AsubB.
        ** SSSCase "A = styp_nat".
           inverts AsubB.
           inverts phi.
           exists~ co_id.
        ** SSSCase "A = styp_and".
           inverts AsubB as HH.
           assert (HH1 : ASub nil styp_nat styp_nat co_id) by auto.
           forwards (cc & H) : >> IHk HH phi HH1...
           exists~ (co_trans cc co_proj1).

           assert (HH1 : ASub nil styp_nat styp_nat co_id) by auto.
           forwards (cc & H) : >> IHk HH phi HH1...
           exists~ (co_trans cc co_proj2).
        ** SSSCase "A = styp_arrow".
           inverts AsubB as HH1 HH2.
           inverts phi as HH phi.
           assert (HH' : ASub nil styp_nat styp_nat co_id) by auto.

           forwards (cc1 & ?) : >> IHk HH2 phi HH'...
           forwards (cc2 & ?) : >> IHk HH phi_empty HH1...
           exists~ (co_arr cc2 cc1).
        ** SSSCase "A = styp_rcd".
           inverts AsubB as HH.
           inverts phi as phi.
           assert (HH' : ASub nil styp_nat styp_nat co_id) by auto.
           forwards (cc & ?) : >> IHk HH phi HH'...
           exists~ (co_rcd l cc).


      * SSCase "B = styp_and".
        inverts AsubB as HH1 HH2.
        inverts BsubC as HH.
        forwards (cc & ?) : IHk HH1 phi HH...
        exists~ cc.
        forwards (cc & ?) : IHk HH2 phi HH...
        exists~ cc.

      * SSCase "B = styp_arrow".
        destruct fs2.
        inverts BsubC.
        inverts BsubC as HH1 HH2.
        inverts AsubB.
        assert (phi2 : Phi (fs3 ++ [st_ty A0]) (fs1 ++ [st_ty B1])) by (sapply phi_append1; eauto).
        forwards (cc & ?) : IHk H4 phi2 HH2...
        rewrite <- app_assoc in H.
        exists~ cc.

      * SSCase "B = styp_rcd".
        destruct fs2.
        inverts BsubC.
        inverts BsubC as HH1.
        inverts AsubB as HH2.
        assert (phi2 : Phi (fs3 ++ [st_la l]) (fs1 ++ [st_la l])) by (sapply phi_append2; eauto).
        forwards (cc & ?) : IHk HH2 phi2 HH1...
        rewrite <- app_assoc in H.
        exists~ cc.


    + SCase "C = styp_and".
      inverts BsubC as HH1 HH2.
      forwards (cc1 & ?) : IHk AsubB phi HH1...
      forwards (cc2 & ?) : IHk AsubB phi HH2...
      exists~ (co_trans (calAnd (fs3 ++ fs2)) (co_pair cc1 cc2)).
    + SCase "C = styp_arrow".
      inverts BsubC.
      forwards (cc & ?) : IHk AsubB phi H4...
      rewrite app_assoc in H.
      exists~ cc.

    + SCase "C = styp_rcd".
      inverts BsubC.
      forwards (cc & ?) : IHk AsubB phi H4...
      rewrite app_assoc in H.
      exists~ cc.
Qed.



Lemma ASub_trans_wrt_Phi : forall A B C fs1 fs2 fs3 c1 c2,
    ASub fs1 A B c1 ->
    Phi fs3 fs1 ->
    ASub fs2 B C c2 ->
    exists c, ASub (fs3 ++ fs2) A C c.
Proof.
  intros.
  eapply ASub_trans_wrt_Phi_aux
    with (k := sizeTyp A + sizefs fs1 + sizeTyp B + sizefs fs2 + sizeTyp C + sizefs fs3); eauto.
Qed.


(** [ASub] is transitive *)
Lemma ASub_trans : forall A B C c1 c2,
    ASub nil A B c1 -> ASub nil B C c2 -> exists c, ASub nil A C c.
Proof.
  introv H1 H2.
  forwards * : ASub_trans_wrt_Phi H1 phi_empty H2.
Qed.


(** [ASub] is reflexive *)
Lemma ASub_refl : forall A,
    exists c, ASub nil A A c.
Proof.
  intros.
  apply set2Sub.
  apply setRefl.
Qed.


Lemma arrSub : forall fs A1 A2 B1 B2 c1 c2,
    ASub fs B1 B2 c2 ->
    ASub nil A2 A1 c1 ->
    exists c, ASub ([st_ty A2] ++ fs) (styp_arrow A1 B1) B2 c.
Proof.
  introv H.
  gen A1 A2 c1.
  induction H; intros.

  - Case "A-nat".
    exists (co_arr c1 co_id).
    constructor~.

  - Case "A-rcdNat".
    forwards HH : IHASub H0.
    destruct HH as (cc & HH).
    inverts HH.
    exists~ (co_arr c1 (co_rcd l c2)).
    constructor~.

  - Case "A-rcd".
    forwards HH : IHASub H0.
    destruct HH as (cc & HH).
    exists~ cc.

  - Case "A-top".
    exists~ (co_trans (calTop ([st_ty A2] ++ fs)) co_top).

  - Case "A-and".
    forwards * (cc1 & HH1): IHASub1 H1.
    forwards * (cc2 & HH2): IHASub2 H1.

  - Case "A-arr".
    forwards * (cc & HH): IHASub H0.

  - Case "A-andNat1".

    forwards * (cc & HH): IHASub A0 A3 c1.
    inverts HH.
    exists (co_arr c0 (co_trans c2 co_proj1)).
    constructor~.

  - Case "A-andNat2".

    forwards * (cc & HH): IHASub A0 A3 c1.
    inverts HH.
    exists (co_arr c0 (co_trans c2 co_proj2)).
    constructor~.


  - Case "A-arrNat".

    forwards * (cc & HH): IHASub2 A1 A c1.
    exists (co_arr c0 cc).
    constructor~.

Qed.


Lemma rcdSub : forall fs A B c1 l,
    ASub fs A B c1 ->
    exists c2, ASub ([st_la l] ++ fs) (styp_rcd l A) B c2.
Proof.
  introv H.
  induction* H; simpls; try solve [destruct IHASub as (c' & IHASub); auto_star].

  - Case "A-nat".
    exists~ (co_rcd l co_id).


  - Case "A-and".
    destruct IHASub1 as (cc1 & IHASub1).
    destruct IHASub2 as (cc2 & IHASub2); auto_star.

  - Case "A-nat".
    destruct IHASub1 as (cc1 & IHASub1).
    destruct IHASub2 as (cc2 & IHASub2); auto_star.
Qed.



(** *Completeness *)

Theorem sub2ASub : forall A B c,
    sub A B c -> exists c', ASub nil A B c'.
Proof.
  introv H.
  induction* H.

  - Case "refl".
    apply ASub_refl.

  - Case "trans".
    destruct IHsub1 as (c1' & IHsub1).
    destruct IHsub2 as (c2' & IHsub2).
    eapply ASub_trans; eauto.

  - Case "arrow".
    destruct IHsub1 as (c1' & IHsub1).
    destruct IHsub2 as (c2' & IHsub2).

    (** Note: Pierce's proof is wrong in this case, we need [arrSub] *)
    lets* (cc & HH): arrSub IHsub2 IHsub1.

  - Case "and".
    destruct IHsub1 as (c1' & IHsub1).
    destruct IHsub2 as (c2' & IHsub2).
    exists* (co_trans (calAnd nil)(co_pair c1' c2')).

  - Case "and1".
    apply~ set2Sub.
    constructor; branch 1; apply setRefl.

  - Case "and2".
    apply~ set2Sub.
    constructor; branch 2; apply setRefl.

  - Case "arrAnd".
    set (T := styp_and (styp_arrow A1 A2) (styp_arrow A1 A3)).
    assert ((styp_arrow A1 A2) ∈R (styp_arrow A1 A2)) by apply setRefl.
    assert ((styp_arrow A1 A3) ∈R (styp_arrow A1 A3)) by apply setRefl.
    assert ((styp_arrow A1 A2) ∈R T). constructor; branch~ 1.
    assert ((styp_arrow A1 A3) ∈R T). constructor; branch~ 2.
    change (styp_arrow A1 A2) with (applyfs ([st_ty A1]) A2) in H1.
    change (styp_arrow A1 A3) with (applyfs ([st_ty A1]) A3) in H2.
    apply set2Sub in H1.
    apply set2Sub in H2.
    destruct H1 as [c1 H1].
    destruct H2 as [c2 H2].
    lets : A_and H1 H2.
    exists~ (co_trans (calAnd [st_ty A1]) (co_pair c1 c2)).

  - Case "recd1".
    destruct IHsub as (cc & ?).

    lets * (cc' & ?): rcdSub l H0.

  - Case "recd2".
    set (T := styp_and (styp_rcd l A) (styp_rcd l B)).
    assert ((styp_rcd l A) ∈R (styp_rcd l A)) by apply setRefl.
    assert ((styp_rcd l B) ∈R (styp_rcd l B)) by apply setRefl.
    assert ((styp_rcd l A) ∈R T). constructor; branch~ 1.
    assert ((styp_rcd l B) ∈R T). constructor; branch~ 2.
    change (styp_rcd l A) with (applyfs ([st_la l]) A) in H1.
    change (styp_rcd l B) with (applyfs ([st_la l]) B) in H2.
    apply set2Sub in H1.
    apply set2Sub in H2.
    destruct H1 as [c1 H1].
    destruct H2 as [c2 H2].
    lets : A_and H1 H2.
    exists~ (co_trans (calAnd [st_la l]) (co_pair c1 c2)).

Qed.
