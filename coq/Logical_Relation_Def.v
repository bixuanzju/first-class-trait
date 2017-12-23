
Require Import Metalib.Metatheory.
Require Import Infrastructure target_inf.



Inductive rel_nat : exp -> exp -> Prop :=
| RelInt : forall n, rel_nat (trm_lit n) (trm_lit n).



Definition grel_e (rel : exp -> exp -> Prop) (t1 t2 : exp) : Prop :=
  exists v1 v2, value v1 /\ value v2 /\ t1 ->* v1 /\ t2 ->* v2 /\ rel v1 v2.


(**

Ideally should define on a tuple, but Coq fails to determine termination of the following


Fixpoint rel_v T T' v v' : Prop :=
  match (T, T') with
  | (typ_int, typ_int) => rel_nat v v'
  | (typ_prod T1 T2, _) => rel_v T1 T' (trm_proj1 v) v' /\ rel_v T2 T' (trm_proj2 v) v'
  | (_, typ_prod T1' T2') => rel_v T T1' v (trm_proj1 v') /\ rel_v T T2' v (trm_proj2 v')
  | _ => True
  end.

 *)

Fixpoint rel_v T  :=
  fix rel_v' T' (v v' : exp) : Prop := value v /\ value v' /\ nil |= v ~: T /\ nil |= v' ~: T' /\
    match T with
    | a_nat =>
      match T' with
      | a_nat => rel_nat v v'
      | a_prod T1 T2 => grel_e (rel_v' T1) v (trm_capp co_proj1 v') /\ grel_e (rel_v' T2) v (trm_capp co_proj2 v')
      | _ => True
      end
    | a_arrow T1 T2 =>
      match T' with
      | a_arrow T1' T2' => forall a1 a2, rel_v T1 T1' a1 a2 -> grel_e (rel_v T2 T2') (trm_app v a1) (trm_app v' a2)
      | a_prod T1 T2 => grel_e (rel_v' T1) v (trm_capp co_proj1 v') /\ grel_e (rel_v' T2) v (trm_capp co_proj2 v')
      | _ => True
      end
    | a_prod T1 T2 =>
       grel_e (rel_v T1 T') (trm_capp co_proj1 v) v' /\ grel_e (rel_v T2 T') (trm_capp co_proj2 v) v'
    | a_unit =>
      match T' with
      | a_prod T1 T2 => grel_e (rel_v' T1) v (trm_capp co_proj1 v') /\ grel_e (rel_v' T2) v (trm_capp co_proj2 v')
      | _ => True
      end
    | a_rcd l T1 =>
      match T' with
      | a_prod T1 T2 => grel_e (rel_v' T1) v (trm_capp co_proj1 v') /\ grel_e (rel_v' T2) v (trm_capp co_proj2 v')
      | a_rcd l' T2 => if l == l' then grel_e (rel_v T1 T2) (trm_proj v l) (trm_proj v' l) else True
      | _ => True
      end
    end.

Definition rel_e T T' v v' :=
  grel_e (rel_v T T') v v' /\ nil |= v ~: T /\ nil |= v' ~: T'.

Definition stenv := list (atom * exp).


Inductive rel_g : ctx -> ctx -> stenv -> stenv -> Prop :=
| rel_g_empty : rel_g nil nil nil nil
| rel_g_cons : forall x G1 G2 g1 g2 T1 T2 v1 v2,
    x # G1 -> x # G2 ->
    rel_g G1 G2 g1 g2 ->
    rel_v T1 T2 v1 v2 ->
    rel_g ([(x , T1)] ++ G1) ([(x, T2)] ++ G2) ([(x , v1)] ++ g1) ([(x , v2)] ++ g2).


Inductive all_value : stenv -> Prop :=
| all_empty : all_value nil
| all_cons : forall x v T g,
    value v ->
    nil |= v ~: T ->
    all_value g ->
    all_value ([(x , v)] ++ g).


(** Substitute away all free variabls in a term *)
Definition bind (s : stenv) (t : exp) : exp :=
  fold_left (fun acc p => [fst p ~> snd p] acc) s t.


Definition rel_e_open G1 G2 t1 t2 T1 T2 :=
  G1 |= t1 ~: T1 /\ G2 |= t2 ~: T2 /\
  forall g1 g2, rel_g G1 G2 g1 g2 ->
           rel_e T1 T2 (bind g1 t1) (bind g2 t2).

Definition kleene_equiv t1 t2 :=
  exists k, t1 ->* (trm_lit k) /\ t2 ->* (trm_lit k).


Fixpoint appctx (ctx : cc) (t : exp) : exp :=
  match ctx with
  | cc_Empty => t
  | cc_Lam x c => trm_abs (close_exp_wrt_exp x (appctx c t))
  | cc_AppL c t2 => trm_app (appctx c t) t2
  | cc_AppR t1 c => trm_app t1 (appctx c t)
  | cc_PairL c t2 => trm_pair (appctx c t) t2
  | cc_PairR t1 c => trm_pair t1 (appctx c t)
  | cc_Co co c => trm_capp co (appctx c t)
  | cc_Rcd l c => trm_rcd l (appctx c t)
  | cc_Proj c l => trm_proj (appctx c t) l
  end.

Hint Constructors rel_nat rel_g all_value.
