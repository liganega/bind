(** * Fresh Constants *)

Set Implicit Arguments.

Require Import Coq.Arith.Max.
Require Export sublist.
Require Import language_syntax.

(** Remember that [constants] play the role of [parameters].
   In particular, we will show that fresh constants are as good as
   fresh parameters. *)

(** [new] chooses a fresh one which does not belong to lists. *)

Definition new (l:list name) : name := S (fold_right max 0 l).

Lemma new_no_zero : forall (l:list name), new l <> 0.
Proof.
  unfold new; intros; auto with arith.
Qed.

Lemma IN_less : forall (n:name)(l:list name),
  IN_name n l ->
  n < new l.
Proof.
  unfold new; induction l; simpl; intro H; [elim H | ].
  case_var; auto with arith.
  apply lt_le_trans with (m:= S (fold_right max 0 l)); eauto 2 with arith.
Qed.

Lemma new_fresh : forall l : list name, (new l) # l.
Proof.
  intros l H.
  elim (lt_irrefl (new l)).
  apply IN_less; exact H.  
Qed.

(** Freshness for a term *)

(*
Lemma fresh_out_t : forall (t : trm),
  (new (oc_t t)) # (oc_t t).
Proof.
  intro t. 
  exact (new_fresh (oc_t t)).
Qed.

(** Freshness for a formula *)

Lemma fresh_out_f : forall (A :fml),
  (new (oc A)) # (oc A).
Proof.
  intros A. 
  exact (new_fresh (oc A)).
Qed.

(** Choosing a fresh variable for a context *)

Definition fresh_out (Ga:list fml) : name := new (oc_c Ga).

(** Freshness for a context *)

Definition fresh (x:name)(Ga:list fml) : Prop :=
  x # (oc_c Ga).

Lemma fresh_out_spec : forall (Ga : list fml),
  fresh (fresh_out Ga) Ga.
Proof.
  unfold fresh; unfold fresh_out; intros Ga.
  exact (new_fresh (oc_c Ga)).
Qed.

Lemma fresh_fml_peel : forall a A Ga, 
  fresh a (A::Ga) ->
  a # (oc A).
Proof.
  unfold fresh; simpl; intros; auto with datatypes.
Qed.

Lemma fresh_peel : forall a A Ga,
  fresh a (A::Ga) ->
  fresh a Ga.
Proof.
  unfold fresh; simpl; intros; auto with datatypes.
Qed.
*)

(** Two tactics in dealing with [~ In]. *)

Ltac destruct_notin :=
  match goal with
    | H : ~ (IN ?decA ?x (?l ++ ?m)) |- _  =>
      destruct (notIN_app_1 decA x l m H); clear H; destruct_notin
    | H : ?x = new ?L |- _ =>
      let Hnew := fresh "Hnew" in
      generalize (new_fresh L); intro Hnew; rewrite <- H in Hnew;
        clear H; destruct_notin
    | x := ?l |- _ =>
      assert (x = l); auto; clearbody x; destruct_notin
    | _ => idtac
  end.


Ltac solve_notin :=
  intros;
  destruct_notin;
  repeat first [ apply notIN_app_2
               | apply notIN_cons_3
               | apply notIN_singleton_1
               | apply notIN_empty_1
               ];
  auto;
  try tauto;
  fail "Not solvable by [solve_notin]; try [destruct_notin]".

