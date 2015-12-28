Set Implicit Arguments.

Require Import decidable_IN.

(** * Associations *)

(** Given a type [A], asociaions are lists of type
  [name*A]. 

  Associations are used in defining

   - simultaneous substitution
   - simultaneous renaming
   - language semantics such as Kripke semantics, etc. *)

Definition assoc (A:Type) := list (name * A)%type.

(** ** A lookup function *)

(** The [lookup] function returns the object associated with a name in
  an association. *) 

Fixpoint lookup A (rho:assoc A) (x:name) {struct rho} : option A := 
  match rho with
  | nil => None
  | (y,a) :: rho0
    => if eqdec x y then Some a else lookup rho0 x
  end.

Notation " rho ^^ x " := (@lookup _ rho x) (at level 60).

(** A tactic distinguishing values of the lookup function. *)

Ltac case_assoc :=
  match goal with
  | |- context [ ?eta ^^ ?x ]       => destruct (eta ^^ x)
  | H : context [ ?eta ^^ ?x ] |- _ => destruct (eta ^^ x)
  end.

(** Domain and co-domain of an association *)

Fixpoint dom (A : Type) (rho: assoc A) {struct rho} : list name :=
  match rho with
  | nil           => nil
  | (x,a) :: rho0 => x :: dom rho0
  end.

Fixpoint img (A: Type) (rho: assoc A) {struct rho} : list A :=
  match rho with
    | nil           => nil
    | (x,a) :: rho0 => a :: img rho0
  end.

Lemma empty_dom : forall A (x : name), x # dom (@nil (name *A)). 
Proof. 
  intros; unfold not; intro H; inversion H.
Defined.

(** If [a] is not in [dom rho], then [rho ^^ a] is undefined. *)

Lemma notIN_dom_None : forall A (a: name) (rho: assoc A),
    a # (dom rho) ->
    rho ^^ a = None.
Proof.
  induction rho as [| [? ?]]; simpl; intros;
  [ reflexivity
  | case_var; intuition
  ].
Qed.

Hint Resolve notIN_dom_None.

(** If [a] is in [dom rho], there is some [b] s.t. 
  [rho^^a = Some x]. *)

Fixpoint IN_dom_sig A (a : name) (rho : assoc A) {struct rho} :
  a @ (dom rho) -> {x : A | rho ^^ a = Some x} :=
  match rho return a @ (dom rho) -> {x : A | rho ^^ a = Some x} with
  | nil => fun H   => False_rect _ H
  | (b, y) :: rho0 =>
    match a == b as s0
          return (if s0 then True else a @ (dom rho0)) ->
                 {x : A | (if s0 then Some y else rho0 ^^ a) = Some x}
    with
    | left _   =>
      fun _ => exist _ y (eq_refl (Some y))
    | right H0 =>
      fun H => IN_dom_sig a rho0 H
    end
  end.

(* 
Lemma IN_dom_sig' : forall A (a: name) (rho: assoc A),
  (a @ (dom rho)) ->
  {b : A | rho ^^ a = Some b}.
Proof.
induction rho as [| [x y]]; simpl; intros;
  [ intuition
    | case_var;
      [ exact (exist (fun b => Some y = Some b) y (refl_equal (Some y)))
        | auto
      ]
  ].
Qed.
 *)

(*
Lemma in_dom_neq : forall A (rho : assoc A) x y u, 
    x <> y ->
    x @ dom ((y,u)::rho) -> x @ dom rho.
Proof.
  intros; simpl in H0.
  destruct (x==y); try tauto.
Defined.
 *)

(** [lookup x rho] takes the value of "first" occurrence of the form
  [(x, a0)]. *)

Lemma lookup_eq: forall A (rho : assoc A) a b,
    a = b ->
    forall x, ((b, x) :: rho) ^^ a = Some x.
Proof.
  simpl; intros; case_var; intuition.
Qed.

Lemma lookup_neq: forall A (rho : assoc A) a b,
    a <> b ->
    forall x, rho ^^ a  = ((b, x) :: rho) ^^ a.
Proof.
  simpl; intros; case_var; intuition.
Qed.

Lemma lookup_ext_1 : forall A (rho rho0 : assoc A) x y,
    x = y ->
    forall z d d',
      (rho ++ (x, d) :: rho0) ^^ z = 
      (rho ++ (x, d) :: (y, d') :: rho0) ^^ z.
Proof.
  induction rho as [ | [x0 a ]]; simpl; intros; 
  repeat case_var; intuition try congruence; auto.
Qed.

Lemma lookup_ext_2 : forall A (rho rho0 : assoc A) x y,
    x <> y ->
    forall z d d',
      (rho ++ (x, d) :: (y, d') :: rho0) ^^ z =
      (rho ++ (y, d') :: (x, d) :: rho0) ^^ z.
Proof.
  induction rho as [ | [x0 a ]]; simpl; intros; 
  repeat case_var; intuition try congruence; auto.
Qed.

(*
Lemma assoc_neq : forall A x y u (rho rho' : assoc A), 
    x <> y ->
    (rho ++ (y,u) :: rho') ^^ x = (rho ++ rho') ^^ x.
Proof.
  induction rho, rho'; simpl; intro;
  destruct (x==y); try tauto;
  destruct a; destruct (x==n0); try tauto;
  apply IHrho; try tauto.
Defined.
*)

(** ** Removing elements from an association *)

(** [assoc_rm] removes every pair starting with a specific fst
  argument *)

Fixpoint assoc_rm (A : Type)(rho : assoc A)(x : name) {struct rho} 
  : assoc A :=
  match rho with
  | nil           => nil
  | (y,t) :: rho' => if x == y then assoc_rm rho' x
                     else (y,t) :: assoc_rm rho' x
  end.

Notation " rho ^- x " := (@assoc_rm _ rho x) (at level 60).

Lemma assoc_rm_self : forall A (rho : assoc A) x, 
    (rho ^-x) ^^ x = None.
Proof. 
  induction rho as [| [y t]]; simpl; intros.
  - reflexivity.
  - case_var; auto.
    + simpl; case_var; intuition.
Defined.

(* Lemma in_dom_neq_rm : forall A (rho : assoc A) x y,  *)
Lemma assoc_rm_neq_dom : forall A (rho : assoc A) x y, 
    x <> y ->
    x @ dom rho -> x @ dom (rho ^- y).
Proof.
  induction rho; simpl; intros; try tauto. 
  destruct a.
  destruct (y==n).
  rewrite <- e in *.
  apply IHrho; auto.
  apply neq_IN_cons with (a:=y); auto.
  simpl.
  destruct (x==n); auto.
  apply IHrho; auto.
  apply neq_IN_cons with (a:=n); auto.
Defined.

(* Lemma not_in_dom : forall A x (rho : assoc A),  *)
Lemma assoc_rm_dom_self : forall A x (rho : assoc A), 
    x # dom (rho ^- x).
Proof.
  induction rho; simpl; intro; auto.
  destruct a; simpl in *.
  destruct (x==n); try tauto.
  simpl in *.
  destruct (x==n); try tauto.
Defined.

(* Lemma rm_rm : forall A x (rho : assoc A),  *)
Lemma assoc_rm_rm : forall A x (rho : assoc A), 
    rho ^- x = (rho ^-x) ^- x.
Proof.
  induction rho; try destruct a; simpl; intros; auto.
  destruct (x==n); simpl; try assumption.
  rewrite <- IHrho.
  destruct (x==n); try tauto.
Defined.

(* Lemma rm_neq_rm : forall A x y (rho : assoc A),  *)
Lemma assoc_rm_neq_rm : forall A x y (rho : assoc A), 
    x <> y ->
    (rho ^- y) ^- x = (rho ^- x) ^- y.
Proof.
  induction rho; try destruct a; simpl; intros; auto.
  destruct (y==n); try tauto; simpl.  
  rewrite <- e in *.
  destruct (x==y); try tauto; simpl.
  destruct (y==y); try tauto; simpl.
  destruct (x==n); try tauto; simpl.
  destruct (y==n); try tauto; simpl.
  rewrite IHrho; try tauto.
Defined.

(* Lemma rm_neq_rm_r : forall A (rho rho' : assoc A) x y u,  *)
Lemma assoc_rm_neq_rm_r : forall A (rho rho' : assoc A) x y u, 
    x <> y ->
    (rho++(y,u)::rho') ^- x = rho ^- x ++ (y, u) :: rho' ^- x.
Proof.
  induction rho, rho'; try destruct a; try destruct p; simpl; intros; auto;
  try destruct (x==y); try tauto; simpl;
  try destruct (x==n); try tauto; simpl;
  rewrite IHrho; auto.
Defined.

(* Lemma assoc_rm_neq : forall A (rho : assoc A) x y,  *)
Lemma lookup_assoc_rm_neq : forall A (rho : assoc A) x y, 
    x <> y -> 
    rho ^^ x = (rho ^- y) ^^ x.
Proof.
  induction rho; try destruct a; simpl; intros; try tauto;
  destruct (y==n); simpl; try tauto; try apply IHrho; auto; subst; auto;
  destruct (x==n); simpl; try tauto; apply IHrho; auto.
Defined.

Hint Rewrite <- lookup_assoc_rm_neq : assoc_rmi.

