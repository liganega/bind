(** * Associations *)

Set Implicit Arguments.

Require Export decidable_IN.

(** Given a set [A], asociaions are list of elements of [name * A]. 
   Associations are used for

   - simultaneous substitution

   - simultaneous renaming

   - Kripke semantics *)

Definition assoc (A:Type) := list (name * A).

(** Domain of an association *)

Fixpoint dom (A : Type) (rho: assoc A) {struct rho} : list name :=
  match rho with
    | nil           => nil
    | (x,a) :: rho0 => x :: dom rho0
  end.

Fixpoint fun_assoc A (rho:assoc A) (x:name) {struct rho} : option A := 
  match rho with
    | nil => None
    | (y,a) :: rho0
      => if eqdec x y then Some a else fun_assoc rho0 x
  end.

Notation " rho ^^ x " := (@fun_assoc _ rho x) (at level 60).

(** A tactic distinguishing values of function association. *)

Ltac case_assoc :=
  match goal with
    | |- context [ ?eta ^^ ?x ]       => destruct (eta ^^ x)
    | H : context [ ?eta ^^ ?x ] |- _ => destruct (eta ^^ x)
  end.

(** If [a] is not in [dom (rho)], then [rho (a)] is undefined. *)

Lemma notIN_dom_None : forall A (a: name) (rho: assoc A),
  a # (dom rho) ->
  rho ^^ a = None.
Proof.
  induction rho as [| (x, a0)]; auto; simpl; intros; case_var; intuition.
Qed.

Hint Resolve notIN_dom_None.

(** If [a] is in [dom (rho)], there is some [b] s.t. [rho(a) = Some x]. *)

Fixpoint IN_dom_sig X (a : name) (eta : assoc X) {struct eta} :
  IN_name a (dom eta) -> {x : X | eta ^^ a = Some x} :=
  match eta return IN_name a (dom eta) -> {x : X | eta ^^ a = Some x} with
    | nil => fun H   => False_rect _ H
    | (b, y) :: eta0 =>
      match a == b as s0
        return (if s0 then True else IN_name a (dom eta0)) ->
        {x : X | (if s0 then Some y else eta0 ^^ a) = Some x}
        with
        | left _   =>
          fun _ => exist _ y (eq_refl (Some y))
        | right H0 =>
          fun H => IN_dom_sig a eta0 H
      end
  end.


(*
Lemma IN_dom_sig : forall A (a: name) (rho: assoc A),
  (IN_name a (dom rho)) ->
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


Lemma fun_assoc_eq: forall X (eta : assoc X) a b,
  a = b ->
  forall x,
    ((b, x) :: eta) ^^ a = Some x.
Proof.
  simpl; intros; case_var; intuition.
Qed.

Lemma fun_assoc_neq: forall X (eta : assoc X) a b,
  a <> b ->
  forall x,
    eta ^^ a  = ((b, x) :: eta) ^^ a.
Proof.
  simpl; intros; case_var; intuition.
Qed.

Lemma fun_assoc_ext_1 : forall A (eta eta0 : assoc A) x y,
  x = y ->
  forall z d d',
    (eta ++ (x, d) :: eta0) ^^ z = (eta ++ (x, d) :: (y, d') :: eta0) ^^ z.
Proof.
  induction eta as [ | [x0 a ]]; simpl; intros; 
    repeat case_var; intuition try congruence; auto.
Qed.

Lemma fun_assoc_ext_2 : forall A (eta eta0 : assoc A) x y,
  x <> y ->
  forall z d d',
    (eta ++ (x, d) :: (y, d') :: eta0) ^^ z =
    (eta ++ (y, d') :: (x, d) :: eta0) ^^ z.
Proof.
  induction eta as [ | [x0 a ]]; simpl; intros; 
    repeat case_var; intuition try congruence; auto.
Qed.

Lemma fun_assoc_ext_3 : 
  forall A (eta eta0 : assoc A) x y,
    x = y -> IN_name x (dom (eta)) ->  
    forall d,
      (eta ++ eta0) ^^ x = (eta ++ (y, d) :: eta0) ^^ x.
Proof.
  induction eta as [ | [x0 a ] ]; simpl; intros;  
  repeat case_var; intuition try congruence. auto; intuition.
Qed.
