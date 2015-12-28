(** * Sublist Relation  *)

Set Implicit Arguments.

Require Export decidable_IN.

(** Lists are considered as sets.

   - sublist relation behaves like subset relation.

   - A list [l] is a sublist of another list [k]
     if [l] is a subset of [k] when they are regarded as sets. *)

Definition sublist A decA (l m: list A) : Prop :=
  forall (a:A), IN decA a l -> IN decA a m.

Hint Unfold sublist.

Notation sub_name := (@sublist name eqdec).

(** Reflexivity *)

Lemma sub_refl:
  forall A decA (l : list A),
    sublist decA l l.
Proof.
  unfold sublist; intros; assumption.
Qed.

(** Transitivity *)
Lemma sub_trans: 
  forall A decA (l m k : list A),
    sublist decA l m ->
    sublist decA m k ->
    sublist decA l k.
Proof.
  unfold sublist; intros; auto.
Qed.

Hint Resolve sub_refl sub_trans : datatypes.

(** [subist] and empty list *)

Lemma nil_sub : 
  forall A decA (l: list A),
    sublist decA nil l. 
Proof.
  unfold sublist; simpl; intros; intuition.
Qed.

Lemma sub_nil :
  forall A decA (l:list A),
    sublist decA l nil -> l = nil.
Proof.
  unfold sublist ; intros ? ? ? H.
  induction l as [ | a]; auto; elim (H a); apply IN_eq.
Qed.

Hint Resolve nil_sub sub_nil : datatypes.

(** [sublist] and [cons] *)

Lemma sub_cons_0 : 
  forall A decA (l m: list A) (a:A),
    sublist decA (a::l) m ->
    IN decA a m.
Proof.
  intros. unfold sublist in *. apply H. auto with datatypes. 
Qed.

Lemma sub_cons_1 : 
  forall A decA (l m: list A) (a:A),
    sublist decA (a::l) m ->
    sublist decA l m.
Proof.
  unfold sublist; intros; eauto with datatypes.
Qed.

Lemma sub_cons_2 : 
  forall A decA (a:A) (l:list A),
    sublist decA l (a::l).
Proof.
  unfold sublist; simpl; intros; case_dec decA; auto. 
Qed. 

Lemma sub_cons_3 : 
  forall A decA (l m: list A) (a:A), 
    sublist decA l m ->
    sublist decA (a::l) (a::m).
Proof.
  unfold sublist; simpl; intros; case_dec decA; auto.
Qed.

Hint Resolve sub_cons_1 sub_cons_2 sub_cons_3 : datatypes.

(** [sublist] and [app] *)

Lemma sub_appL : 
  forall A decA (l m k: list A),
    sublist decA (l ++ m) k ->
    sublist decA l k.
Proof.
  unfold sublist; intros; eauto with datatypes.
Qed.

Lemma sub_appR :
  forall A decA (l m k: list A),
    sublist decA (l ++ m) k ->
    sublist decA m k.
Proof.
  unfold sublist; intros; eauto with datatypes.
Qed.

Lemma app_sub :
  forall A decA (l m k: list A),
    sublist decA l k ->
    sublist decA m k ->
    sublist decA (l ++ m) k.
Proof.
  unfold sublist; intros.
  elim (IN_app_or H1); auto.
Qed.

Hint Resolve sub_appL sub_appR app_sub : datatypes.

(** [sublist] and [remove] *)

Lemma rm_sub_1 : 
  forall A decA (a:A) (l:list A), 
    sublist decA (remove decA a l) l.
Proof.
  unfold sublist; induction l as [| b]; simpl; intros; auto.
  repeat case_dec decA; eauto with datatypes.
Qed.

Lemma rm_sub_2 :
  forall A decA (a:A) (l:list A),
    sublist decA (remove decA a (a::l)) l.
Proof.
  simpl; intros; case_dec decA; 
  [ auto using rm_sub_1 | intuition ].
Qed.

Hint Resolve rm_sub_1 rm_sub_2 : datatypes.

Lemma sub_rm_1 : 
  forall A decA (l m: list A) (a:A), 
    sublist decA l m ->
    sublist decA (remove decA a l) (remove decA a m).
Proof.
  unfold sublist; induction l as [| v l']; simpl; intros; [contradiction | ].
  repeat case_dec decA; subst.
  - apply IHl'; auto.
    intro a; generalize (H a); intro; case_dec decA; auto.
  - simpl in H0; case_dec decA; subst.
    + generalize (H v); intro; case_dec decA; [ | congruence].
      apply IN_rm_2; firstorder.
    + apply IHl'; auto; intros a1 Ha1.
      generalize (H a1); intro; case_dec decA; auto.
Qed.

Lemma sub_rm_2 : 
  forall A decA (l m:list A) (a:A),
    sublist decA (remove decA a m) l ->
    sublist decA m (a :: l).
Proof.
  unfold sublist; simpl; intros.
  case_dec decA; auto with datatypes.
Qed.

Lemma sub_rm_3 :
  forall A decA (l m: list A) (a:A), 
    sublist decA l (a :: m) ->
    sublist decA (remove decA a l) m.
Proof.
  intros; apply sub_trans with (m:= remove decA a (a::m)).
  - apply sub_rm_1; assumption.
  - auto with datatypes. 
Qed.

Lemma sub_rm_4 : 
  forall A decA (l m:list A) (x y:A),
    sublist decA l m ->
    x = y ->
    sublist decA (y::l) (y:: remove decA x m).
Proof.
  unfold sublist; simpl; intros; destruct (decA a y);
  [ exact I
  | rewrite H0; apply IN_rm_2; auto with datatypes]. 
Qed.

Hint Resolve sub_rm_1 sub_rm_2 sub_rm_3 sub_rm_4 : datatypes.

Lemma IN_singleton : 
  forall A decA (n m : A),
    IN decA n (m :: nil)
    -> n = m.
Proof.
  intros. rew_IN. destruct (in_inv H);  auto. contradiction. 
Qed.

Lemma IN_sublist : 
  forall A decA (l : list A) (n : A),
     sublist decA (n :: nil) l 
    <-> IN decA n l.
Proof.
  split. 
  - apply sub_cons_0 with (l:=nil); auto. 
  -  intros. unfold sublist; intros. pose proof IN_singleton decA _ _ H0. subst; auto. 
Qed.
