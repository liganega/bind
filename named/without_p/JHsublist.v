Set Implicit Arguments.

Require Import decidable_IN.

(** * Sublist Relation  *)

(** Lists are considered as sets.
  - sublist relation behaves like subset relation.

  - A list [l] is a sublist of another list [k]
    if [l] is a subset of [k] when they are regarded as sets. 

  - [sublist] relation is defined based on [IN]. *)

Definition sublist A decA (l m: list A) : Prop :=
  forall (a:A), IN decA a l -> IN decA a m.

Hint Unfold sublist.

(** [sub_name] is the [sublist] relation wrt [nat]. *)

Notation sub_name := (@sublist name eqdec).

(** ** Properties of [sublist] *)

(** Reflexivity *)

Lemma sub_refl: forall A decA (l : list A),
  sublist decA l l.
Proof.
  unfold sublist; intros; assumption.
Qed.

(** Transitivity *)
Lemma sub_trans: forall A decA (l m k : list A),
  sublist decA l m ->
  sublist decA m k ->
  sublist decA l k.
Proof.
  unfold sublist; intros; auto.
Qed.

Hint Resolve sub_refl sub_trans : datatypes.

(** The empty list is a sublist of any list. *)

Lemma nil_sub : forall A decA (l: list A),
  sublist decA nil l. 
Proof.
unfold sublist; simpl; intros; intuition.
Qed.

Lemma sub_nil : forall A decA (l:list A),
  sublist decA l nil -> l = nil.
Proof.
unfold sublist; intros ? ? ? H.
induction l as [ | a];
  [ reflexivity
    | elim (H a); apply IN_eq ]. 
Qed.

Hint Resolve nil_sub sub_nil : datatypes.

(** [sublist] and [cons] *)

Lemma sub_cons_1 : forall A decA (l m: list A) (a:A),
  sublist decA (a::l) m ->
  sublist decA l m.
Proof.
unfold sublist; intros; eauto with datatypes.
Qed.

Lemma sub_cons_2 : forall A decA (a:A) (l:list A),
  sublist decA l (a::l).
Proof.
unfold sublist; simpl; intros; case_dec decA; auto. 
Qed. 

Lemma sub_cons_3 : forall A decA (l m: list A) (a:A), 
  sublist decA l m ->
  sublist decA (a::l) (a::m).
Proof.
unfold sublist; simpl; intros; case_dec decA; auto.
Qed.

Hint Resolve sub_cons_1 sub_cons_2 sub_cons_3 : datatypes.

(** [sublist] and [app] *)

Lemma sub_appL : forall A decA (l m k: list A),
  sublist decA (l ++ m) k ->
  sublist decA l k.
Proof.
  unfold sublist; intros; eauto with datatypes.
Qed.

Lemma sub_appR : forall A decA (l m k: list A),
  sublist decA (l ++ m) k ->
  sublist decA m k.
Proof.
  unfold sublist; intros; eauto with datatypes.
Qed.

Lemma app_sub : forall A decA (l m k: list A),
  sublist decA l k ->
  sublist decA m k ->
  sublist decA (l ++ m) k.
Proof.
  unfold sublist; intros.
  elim (IN_app_or H1); auto.
Qed.

Lemma app_sub_2 : forall A decA (l m k i : list A),
  sublist decA l k -> 
  sublist decA m i -> 
  sublist decA (l ++ m) (k ++ i).
Proof.
  unfold sublist; intros.
  elim (IN_app_or H1); auto with datatypes. 
Qed.

Hint Resolve sub_appL sub_appR app_sub app_sub_2 : datatypes.

(** [sublist] and [remove] *)

Lemma sub_rm_1 : forall A decA (l m: list A) (a:A), 
  sublist decA l m ->
  sublist decA (remove decA a l) (remove decA a m).
Proof.
  unfold sublist; induction l as [| v l']; simpl; intros; [contradiction | ].
  repeat case_dec decA; subst.
    apply IHl'; auto.
    intro a; generalize (H a); intro; case_dec decA; auto.

    simpl in H0; case_dec decA; subst.
      generalize (H v); intro; case_dec decA; [ | congruence].
      apply IN_rm_2; firstorder.

      apply IHl'; auto; intros a1 Ha1.
      generalize (H a1); intro; case_dec decA; auto.
Qed.

Lemma sub_rm_2 : forall A decA (l m:list A) (a:A),
  sublist decA (remove decA a m) l ->
  sublist decA m (a :: l).
Proof.
  unfold sublist; simpl; intros.
  case_dec decA; auto with datatypes.
Qed.

Hint Resolve sub_rm_1 sub_rm_2 : datatypes.

(*
Lemma sub_rm_3 : forall A decA (l m: list A) (a:A), 
  sublist decA l (a :: m) ->
  sublist decA (remove decA a l) m.
Proof.
intros; apply sub_trans with (m:= remove decA a (a::m)).
  apply sub_rm_1; assumption.

  simpl; case_dec decA; [ auto with datatypes | congruence].
Qed.

Lemma sub_rm_4 : forall A decA (l m:list A) (x y:A),
  sublist decA l m ->
  x = y ->
  sublist decA (y::l) (y:: remove decA x m).
Proof.
  unfold sublist; simpl; intros; destruct (decA a y);
    [ exact I
      | rewrite H0; apply IN_rm_2; [exact n | apply H; exact H1] ].
Qed.

Hint Resolve sub_rm_3 sub_rm_4 : datatypes.

(* Lemma rm_sub_1 : forall A decA (a:A) (l:list A),  *)
Lemma sub_rm_5 : forall A decA (a:A) (l:list A), 
  sublist decA (remove decA a l) l.
Proof.
unfold sublist; induction l as [| b]; simpl; intros; auto.
repeat case_dec decA; eauto with datatypes.
Qed.

(* Lemma rm_sub_2 : forall A decA (a:A) (l:list A), *)
Lemma sub_rm_6 : forall A decA (a:A) (l:list A),
  sublist decA (remove decA a (a::l)) l.
Proof.
simpl; intros; case_dec decA; 
  [ auto using sub_rm_5 | intuition ].
Qed.

Hint Resolve sub_rm_5 sub_rm_6 : datatypes.
*)