Set Implicit Arguments.

Require Export Coq.Lists.List.
Require Export Coq.Arith.Arith.

(** * Decidability and decidable [IN] Predicate *)

(** ** Decidable type *)

(** A type or set is called decidable when the equality between its
    elements is  decidable *)

Definition decidable (A : Type)
  := forall a b : A, {a = b} + { a <> b}.

(** ** Decidable equality *)

(** The [List] module supports membership predicate [In]. It's
  definition uses logical 'or' operation which is not at all
  decidable. In some cases, however, one need to work with decidable
  version of membership predicate. The following new membership
  predicate is an equivalent version of [List.In] predicate when they
  are defined on a decidable type. *)

Fixpoint IN A (decA:decidable A)(a:A)(l:list A) {struct l} : Prop :=
  match l with
    | nil    => False
    | b :: m => if decA a b then True else IN decA a m
  end.

(** [nat] will be used as the basis for representing any kind of
  variables. And some notations will be used when [IN] is used
  combined with [nat]. We remark that any denumerably decidable set
  can be used instead of [nat]. *)

Notation name := nat.
Notation eqdec := eq_nat_dec.

Notation "k == i" := (eqdec k i) (at level 70).
(* Notation IN_name := (@IN name eqdec). *)
Notation " x @ l " := (@IN name eqdec x l) (at level 70).
Notation " x # l " := (~ @IN name eqdec  x l) (at level 70).
(* Notation rm_name := (remove eqdec). *)

(** ** Tactics for dealing with decidable equality *)

(** [case_dec] tactic can  be used when dealing with cases of
  equality *) 

Ltac case_dec decA :=
  match goal with
    | |- context [decA ?a ?b]       => destruct (decA a b)
    | _ : context [decA ?a ?b] |- _ => destruct (decA a b)
  end.

(** [case_var] tactic is more specific and can be used when two
  variable names based on [nat] are to be compared. *) 

Ltac case_var :=
  let ldestr k i := destruct (k == i); [try subst k | idtac] in
  match goal with
  | |- context [?k == ?i]      => ldestr k i
  | H: context [?k == ?i] |- _ => ldestr k i
  end.

(** ** Decidability of membership relation wrt a list *)

(** The membership relation becomes a decidable predicate when it is
  combined with [IN] instead of [List.In]. *)

Lemma decIN : forall A decA (x:A) (l:list A),
  {IN decA x l} + {~ IN decA x l}.
Proof.
  induction l as [| a]; simpl;
    [ right
      | case_dec decA
    ]; auto.
Defined.

Notation "x <-? l" := (decIN eqdec x l) (at level 70).

(** [case_IN] tactic can  be used when dealing with cases of
  membership in a list. *) 

Ltac case_IN :=
  match goal with
    | |- context [?x <-? ?l]       => destruct (x <-? l)
    | H : context [?x <-? ?l] |- _ => destruct (x <-? l)
  end.

(** ** Uniqueness of proofs of membership relation wrt a list *)

(** One consequence of using [IN] is that there is a unique proof of
  membership relation wrt a list *) 

Lemma IN_proof_uniq : forall A decA (a:A)(l:list A)(p q : IN decA a l),
  p = q.
Proof.
  induction l; simpl; intros p q;
    [ elim p
      | case_dec decA;
        [ case p; case q; reflexivity
          | apply IHl
        ]
    ].
Qed.

Hint Resolve decIN IN_proof_uniq : datatypes.

(** ** Equivalence of [IN] and [List.In] *)

(** The [List] module provides a basic infrastructure in dealing with
  lists. By showing the equivalence between [IN] and [In], we can
  use them directly instead of developing extra library for [IN]. *)

Lemma IN_In : forall A decA (l:list A)(a:A),
  IN decA a l <-> In a l.
Proof. 
  induction l; simpl;
    [ tauto
      | split; intros; case_dec decA; firstorder; congruence].
Qed.

(** The following two tactics changes [IN] and [In]. *)

Ltac rew_IN :=
  match goal with
    | |- context [IN _ _ _]       => rewrite IN_In
    | H : context [IN _ _ _] |- _ => rewrite IN_In in H
  end.

Ltac rew_In decA :=
  match goal with
    | |- context [In _ _]       => rewrite <- (IN_In decA)
    | H : context [In _ _] |- _ => rewrite <- (IN_In decA) in H
  end.

(** Here are some useful properties of [IN]. *)

Lemma IN_eq : forall A decA (a:A) (l:list A),
  IN decA a (a :: l). 
Proof.
  intros; rew_IN; auto with datatypes. 
Qed.

Lemma IN_cons : forall A decA (l : list A)(a b:A), 
  IN decA b l ->
  IN decA b (a::l).
Proof.
  intros; repeat rew_IN; auto using in_cons.
Qed.  

Lemma neq_IN_cons : forall A decA (l : list A) (a b:A), 
  a <> b ->
  IN decA b (a::l) ->
  IN decA b l.
Proof.
  intros until 1; simpl; case_dec decA; congruence.
Qed.

Hint Resolve IN_In IN_eq IN_cons neq_IN_cons : datatypes.

Lemma IN_rm_1 : forall A decA (a b : A) (l: list A),
  IN decA a (remove decA b l) ->
  IN decA a l.
Proof.
  induction l as [| c l IHl]; simpl; intros; auto.
  repeat case_dec decA; auto.
  apply IHl; apply neq_IN_cons with c; auto.
Qed.

Lemma IN_rm_2 : forall A decA (a b:A) (l:list A), 
  a <> b ->
  IN decA a l ->
  IN decA a (remove decA b l).
Proof.
  induction l as [|c]; simpl; intros; auto.
  repeat case_dec decA;
    [ congruence
      | auto
      | subst; apply IN_eq
      | repeat rew_IN; auto using in_cons ].
Qed.

Lemma IN_rm_neq : forall A decA (a b : A) (l: list A),
  IN decA a (remove decA b l) ->
  a <> b.
Proof.
  induction l as [| c l IHl]; simpl; intros; auto.
  intro; subst.
  case_dec decA; firstorder.
  elim IHl; eauto using neq_IN_cons.
Qed.

Hint Resolve IN_rm_1 IN_rm_2 IN_rm_neq : datatypes.

Lemma IN_or_app : forall A decA (a:A) (l m :list A),
  IN decA a l \/ IN decA a m ->
  IN decA a (l ++ m).
Proof.
  intros; repeat rew_IN; auto with datatypes.
Qed.
    
Lemma IN_app_or : forall A decA (a:A) (l m :list A),
  IN decA a (l ++ m) ->
  IN decA a l \/ IN decA a m.
Proof.
  intros; repeat rew_IN; auto with datatypes.
Qed.
      
Implicit Arguments IN_app_or [A decA a l m].

Lemma IN_appL : forall A decA (a:A)(l m: list A),
  IN decA a l ->
  IN decA a (l ++ m).
Proof.
  intros; apply IN_or_app; left; assumption.
Qed.

Lemma IN_appR : forall A decA (a:A)(l m: list A),
  IN decA a m ->
  IN decA a (l ++ m).
Proof.
  intros; apply IN_or_app; right; assumption.
Qed.

Hint Resolve IN_or_app IN_app_or IN_appL IN_appR : datatypes.

Lemma notIN_rm_1 : forall A decA (a : A) (l: list A),
  ~ IN decA a (remove decA a l).
Proof.
  induction l; simpl; intros; intuition.
  case_dec decA; auto.
  simpl in H; case_dec decA; auto.
Qed.

Lemma notIN_rm_2 : forall A decA (a b:A) (l:list A), 
  ~ IN decA a (remove decA b l) ->
  a <> b ->
  ~ IN decA a l.
Proof.
  firstorder using notIN_rm_1.
Qed.

Hint Resolve notIN_rm_1 notIN_rm_2 : datatypes.

Lemma notIN_app_1 : forall A decA (a:A) (l m :list A),
  ~ IN decA a (l ++ m) ->
  ~ IN decA a l /\ ~ IN decA a m.
Proof.
  firstorder with datatypes.
Qed.

Lemma notIN_app_2 : forall A decA (a:A) (l m :list A),
  ~ IN decA a l ->
  ~ IN decA a m ->
  ~ IN decA a (l ++ m).
Proof.
  intuition; elim (IN_app_or H1); assumption.
Qed.

Lemma notIN_app_3 : forall A decA (a:A)(l m: list A),
  ~ IN decA a (l ++ m) -> ~ IN decA a l.
Proof.
  intros; elim (notIN_app_1 _ _ _ _ H); tauto.
Qed.

Lemma notIN_app_4 : forall A decA (a:A)(l m: list A),
  ~ IN decA a (l ++ m) -> ~ IN decA a m. 
Proof.
  intros; elim (notIN_app_1 _ _ _ _ H); tauto.
Qed.

Lemma notIN_cons_1 : forall A decA (a b:A)(l:list A),
  ~ IN decA a (b :: l) ->
  a <> b.
Proof.
  red; intros ? ? ? ? ? H ?; subst.
  elim H; apply IN_eq.
Qed.

Lemma notIN_cons_2 : forall A decA (a b:A)(l:list A),
  ~ IN decA a (b :: l) ->
  ~ IN decA a l.
Proof.
  red; intros ? ? ? ? ? H ?.
  elim H; repeat rew_IN; auto with datatypes.
Qed.

Hint Resolve notIN_app_1 notIN_app_2 notIN_app_3 notIN_app_4 : datatypes.
Hint Resolve IN_cons notIN_cons_1 notIN_cons_2 : datatypes.

Lemma notIN_cons_3 : forall A decA (a b:A) (l:list A),
  a <> b ->
  ~ IN decA b l ->
  ~ IN decA b (a :: l).
Proof.
  firstorder; simpl; case_dec decA; auto.
Qed.

Lemma notIN_singleton_1 : forall A decA (a b:A),
  a <> b ->
  ~ IN decA b (a :: nil).
Proof.
  firstorder; simpl; case_dec decA; auto.
Qed.

Lemma notIN_empty_1 : forall A decA (a:A),
  ~ IN decA a nil.
Proof.
  firstorder.
Qed.

Lemma rm_cons : forall A decA a b (l:list A),
  a <> b ->
  b :: remove decA a l = remove decA a (b :: l).
Proof.
  intros; simpl; destruct (decA a b);
    [ elim H
      | ];
    auto.
Qed.
