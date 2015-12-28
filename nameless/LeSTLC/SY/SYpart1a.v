(** This file is based on Leory's contribution to POPLmark challenge
  and is modified for STLC (Simply typed lambda calculus).

  We use the same definitions, notations, and structures. Only
  necessay modifications are made in order to test our idea. 

  The main differences are as follows:

  - Simultaneous substitution, renaming
  - No swapping technique
  - Pencil-and-paper style of binding style *)

Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import SYextralibrary.
Require Import SYdecidable_IN.
Require Import SYsublist.

(** * Names and swaps of names *)

(** We use names (also called atoms) to represent variables in terms.
  Any infinite type with decidable equality will do. 

  Only for POPLmark challenge: 

  In preparation for the second part of the POPLmark challenge, we
  attach a kind to every name: either ``type'' or ``term'', and ensure
  that there are infinitely many names of each kind.  Concretely, we
  represent names by pairs of a kind and an integer (type Z). *) 

Inductive name_kind : Set :=
  | TERM: name_kind.

Definition name : Set := (name_kind * Z)%type.

Definition kind (n: name) : name_kind := fst n.

(** Equality between names is decidable. *)

Lemma eq_name: forall (n1 n2: name), {n1 = n2} + {n1 <> n2}.
Proof.
  assert (forall k1 k2: name_kind, {k1 = k2} + {k1 <> k2}).
  decide equality.
  assert (forall p1 p2: positive, {p1 = p2} + {p1 <> p2}).
  decide equality.
  assert (forall z1 z2: Z, {z1 = z2} + {z1 <> z2}).
  decide equality.
  decide equality.
Defined.

(** Moreover, we have the following obvious simplification rules on
  tests over name equality. *)

Lemma eq_name_true:
  forall (A: Set) (n: name) (a b: A), (if eq_name n n then a else b) = a.
Proof.
  intros. case (eq_name n n); congruence.
Qed.

Lemma eq_name_false:
  forall (A: Set) (n m: name) (a b: A),
    n <> m -> (if eq_name n m then a else b) = b.
Proof.
  intros. case (eq_name n m); congruence.
Qed.

(** The following lemma shows that there always exists a name
  of the given kind that is fresh w.r.t. the given list of names, that is,
  distinct from all the names in this list. *)

Definition find_fresh_name (k: name_kind) (l: list name) : name :=
  (k, 1 + fold_right (fun (n:name) x => Zmax (snd n) x) 0 l)%Z.

Lemma find_fresh_name_is_fresh:
  forall k l, let n := find_fresh_name k l in ~In n l /\ kind n = k.
Proof.
  intros.
  set (ident := fun (n: name) => snd n). 
  set (maxid := 
   fold_right (fun (n:name) x => Zmax (ident n) x) 0%Z).
  assert (forall x, In x l -> (ident x <= maxid l)%Z).
    generalize l. induction l0; simpl; intros.
    elim H.
    elim H; intros. subst x. apply Zmax1. 
    apply Zle_trans with (maxid l0). auto. apply Zmax2.
  replace n with (k, 1 + maxid l)%Z. 
  split. red; intro. generalize (H _ H0). unfold ident, snd. omega.
  reflexivity.
  unfold n; reflexivity.
Qed.

Lemma fresh_name:
  forall (k: name_kind) (l: list name), exists n, ~In n l /\ kind n = k.
Proof.
  intros. exists (find_fresh_name k l). apply find_fresh_name_is_fresh.
Qed.

(** * Types and typing environments *)

(** ** Type expressions *)

(** IN case of STLC, types are either atomic types or constructed 
  using the funtional constructor. Therefore, no variables are
  necessary. 

  The constructor [Tparam] below is orginally for parameters. To make
  the modification as simple as possible We use the same name although
  we do not condsider them as parameters. Their role is in fact that
  of atomic types. *)

Inductive type: Set :=
  | Tparam: name -> type
  | Arrow: type -> type -> type.

(** ** Typing environments *)

(** Typing environments are standard: lists of (name, type) pairs.
  Bindings are added to the left of the environment using the
  [cons] list operation.  Thus, later bindings come first. *)

Definition typenv := list (name * type).

Definition dom (e: typenv) := map (@fst name type) e.

Lemma dom_append: forall e1 e2, dom (e1 ++ e2) = dom e1 ++ dom e2.
Proof.
  intros; unfold dom. apply map_append. 
Qed.

(** The [lookup] function returns the type associated with a name in a
  typing environment. *) 

Fixpoint lookup (x: name) (e: typenv) {struct e} : option type :=
  match e with
  | nil => None
  | (y, t) :: e' => if eq_name x y then Some t else lookup x e'
  end.

Lemma lookup_inv: forall x t e, lookup x e = Some t -> In x (dom e).
Proof.
  induction e; simpl. congruence.
  case a; intros x' t'. simpl. 
  case (eq_name x x'); intro. subst x'; tauto.
  intros. right. auto.
Qed.

Lemma lookup_exists:
  forall x e, In x (dom e) -> exists t, lookup x e = Some t.
Proof.
  induction e; simpl; intros.
  elim H.
  destruct a. simpl in H. 
  case (eq_name x n); intro.
  exists t; auto.
  apply IHe. elim H; intro. congruence. auto.
Qed.

Definition env_weaken (e1 e2: typenv) : Prop :=
  forall x t, lookup x e1 = Some t -> lookup x e2 = Some t.

Lemma env_weaken_incl_dom: forall e1 e2, env_weaken e1 e2 -> incl (dom e1) (dom e2).
Proof.
  unfold incl; intros. 
  elim (lookup_exists _ _ H0). intros t LOOKUP. 
  apply lookup_inv with t. apply H. auto.
Qed.

Lemma dom_env_extends: forall e1 x p q e2, dom (e1 ++ (x, p) :: e2) = dom (e1 ++ (x, q) :: e2).
Proof.
  intros. repeat rewrite dom_append. reflexivity.
Qed.

Fixpoint psubst_env (e f: typenv) {struct e} : typenv :=
  match e with
  | nil => nil
  | (y, t) :: e' => (y, psubst_type t f) :: psubst_env e' f
  end.

Lemma dom_psubst_env: forall f e, dom (psubst_env e f) = dom e.
Proof.
  induction e; simpl. auto. destruct a. simpl. congruence. 
Qed.

Fixpoint type_vars_below (t: type) (n: nat) {struct t} : Prop :=
  match t with
  | Tparam x => True
  | Arrow t1 t2 => type_vars_below t1 n /\ type_vars_below t2 n
  end.

Notation sub_name := (@sublist name eq_name).

Notation npart e := (fst (split e)).
Notation tpart e := (snd (split e)).

Notation "n @ l" := (IN eq_name n l).
Notation "n # l" := (not (IN eq_name n l)). 

Lemma psubst_nil : forall t,
    psubst_type t nil = t.
Proof.
  induction t; simpl; auto.
  rewrite IHt1, IHt2; auto.
Qed.

Hint Rewrite psubst_nil.
Hint Resolve psubst_nil.


(* Lemma lookup_None : forall n e,
    n # npart e 
    -> lookup n e = None.

   Lemma psubst_type_inv : forall (t : type) (e : typenv), 
    (forall n : name, n @ (npart e) -> n # (fv_type t)) 
    -> psubst_type t e = t. *)