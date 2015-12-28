Set Implicit Arguments.

Require Import Coq.Arith.Max.
Require Import decidable_IN.
Require Import sublist.
Require Import language_syntax.

(** * Fresh Constants *)

(** Remember that [constants] play the role of [parameters]. We will
  show that fresh constants are as good as fresh parameters.

  [new] chooses a fresh name which does not belong to a given list
  of constants. *)

Definition new (l:list name) : name := S (fold_right max 0 l).

(** [new] produces a non-zero and fresh name. *)

Lemma new_no_zero : forall (l:list name), new l <> 0.
Proof.
  unfold new; intros; auto with arith.
Qed.

Lemma IN_less : forall (n:name)(l:list name),
  n @ l ->
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

(** One can use [new] to choose a fresh name. *)

Lemma fresh_out_t : forall (t : trm),
  (new (oc_t t)) # (oc_t t).
Proof.
  intro t. 
  exact (new_fresh (oc_t t)).
Qed.

Lemma fresh_out : forall (A :fml),
  (new (oc A)) # (oc A).
Proof.
  intros A. 
  exact (new_fresh (oc A)).
Qed.

Definition fresh_out_c (Ga:context) : name := new (oc_c Ga).

Definition fresh (x:name)(Ga:context) : Prop :=
  x # (oc_c Ga).

Lemma fresh_out_spec : forall (Ga : context),
  fresh (fresh_out_c Ga) Ga.
Proof.
  unfold fresh; unfold fresh_out_c; intros Ga.
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

(** The following two tactics help in dealing with [~ In], especially
  when it argues about fresh names. *)

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

