(** * Variable Sets *)

Set Implicit Arguments.

Require Export language_syntax.
Require Import sublist.
Require Import associations.
Require Import associations_extra.


(** Subcontext relation *)

Notation context := (list fml).
Notation sub_ctx_pre := (@sublist fml fml_dec).

(** Being-in-a-context relation *)

Notation IN_ctx := (@IN fml fml_dec).

(*
(** Relation between context and contants *)

Lemma IN_oc_sub (A:fml) (Ga:context) :
  IN_ctx A Ga ->
  sub_name (oc A) (oc_c Ga).
Proof.
  unfold sublist; induction Ga as [ | B]; simpl; intros; auto.
  case_lang; subst; eauto with datatypes.
Qed.

Implicit Arguments IN_oc_sub [A Ga].

Lemma sub_ctx_oc : 
  forall (Ga De:context),
    sub_ctx_pre Ga De -> sub_name (oc_c Ga) (oc_c De).
Proof.
  unfold sublist; intros; induction Ga as [ | A]; simpl in * ; 
  intros; intuition.
  destruct (IN_app_or H0). 
  - generalize (H A); intros; case_lang; eauto 4 with datatypes.
    apply (IN_oc_sub (H2 I)); auto.
  - apply IHGa; auto.
    intros B HB; generalize (H B); case_lang; tauto.
Qed.

Hint Resolve IN_oc_sub sub_ctx_oc.
 *)

(** Relation between context and parameter *)

Lemma IN_op_sub (A:fml) (Ga:context) :
  IN_ctx A Ga ->
  sub_name (op A) (op_c Ga).
Proof.
  unfold sublist; induction Ga as [ | B]; simpl; intros; auto.
  case_lang; subst; eauto with datatypes.
Qed.

Implicit Arguments IN_op_sub [A Ga].

Lemma sub_ctx_op : 
  forall (Ga De:context),
    sub_ctx_pre Ga De -> sub_name (op_c Ga) (op_c De).
Proof.
  unfold sublist; intros; induction Ga as [ | A]; simpl in * ; 
  intros; intuition.
  destruct (IN_app_or H0). 
  - generalize (H A); intros; case_lang; eauto 4 with datatypes.
    apply (IN_op_sub (H2 I)); auto.
  - apply IHGa; auto.
    intros B HB; generalize (H B); case_lang; tauto.
Qed.

Hint Resolve IN_op_sub sub_ctx_op.


(** inversion properties for variable sets:

   - These properties are used in the definition of substitution. *)

Lemma sub_ol_funL : 
  forall f (t0 t1: trm) l,
    sub_name (ol_t (App f t0 t1)) l ->
    sub_name (ol_t t0) l.
Proof.
  eauto 2 with datatypes.
Qed.

Lemma sub_ol_funR : 
  forall f (t0 t1: trm) l,
    sub_name (ol_t (App f t0 t1)) l ->
    sub_name (ol_t t1) l.
Proof.
  eauto 2 with datatypes.
Qed.

Hint Resolve sub_ol_funL sub_ol_funR.

Lemma IN_inv_atom : 
  forall p l (t: trm),
    sub_name (ol (Atom (p,t))) l ->
    sub_name (ol_t t) l.
Proof.
  auto. 
Qed.

Lemma IN_inv_impL :
  forall l (B C: fml),
    sub_name (ol (B --> C)) l ->
    sub_name (ol B) l.
Proof.
  eauto 2 with datatypes.
Qed.

Lemma IN_inv_impR : 
  forall l (B C: fml),
    sub_name (ol (B --> C)) l ->
    sub_name (ol C) l.
Proof.
  eauto 2 with datatypes.
Qed.
