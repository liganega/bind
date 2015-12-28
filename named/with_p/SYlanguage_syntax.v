(** * Language Syntax *)

(** We follow a novel interpretation of Frege's Begriffsschrift
    which is considered as the origin of using two sorts of variables.

   - Our style is closely related to the McKinna-Pollack's _locally-named_ style
     where variables and parameters are used:
     -- (locally bound) _variables_
     -- _parameters_ (also called _free_ variables)

   - A main difference is that we renounce to use parameters, i.e., free variables.
*)

Set Implicit Arguments.

Require Import decidable_IN.

(** The language syntax for the first-order logic is represented.

   - Implication and universal quantification are the only logical symbols.

   - We assume there are two decidable sets of infinitely many "unary" predicates
     and "binary" functions. 
     This is general enough because predicate and function symbols of different 
     arities can be encoded. *)

Parameter predicate : Set.      (* unary predicates *)
Parameter function : Set.       (* binary functions *)

(** We assume decidability of function and predicate symbols *)

Axiom pred_dec : decidable predicate.
Axiom fun_dec : decidable function.

(* ####################################################### *)
(** *** Constants as parameters *)

(** Syntactically, We don't use parameters (free variables).

   - We let constants play the role of constants.

   - An important consequence at the syntactic level is that substitution
     is needed only for variables.

   - The language itself needs to contain infinitely many constants.
     Note that every language can be conservatively extended to a language
     with infinitely many constants.

   - Even if we formally introduce parameters, the substitution for parameters
     do not play any role

   - For the formalization with parameters, see the Coq files, called [with_FreeVar_*.v]. 
*)

(* ####################################################### *)
(** ** Pseudo-terms *)

(** Any decidable, denumerable set can be used for the representation of variables
   and constants.
   Here we use [name = nat], the set of natural numbers, to make the formlization
   as simple as possible. 
*)

Inductive trm : Set := 
| Ltr : name -> trm             (* local variables *)
| Par : name -> trm             (* global variables *)
| Cst  : name -> trm
| App  : function -> trm -> trm -> trm.

(** ** Pseudo-formulas *)

Definition atom := (predicate * trm)%type.

Inductive fml : Set :=
| Atom   : atom -> fml
| Imply  : fml -> fml -> fml
| Forall : name -> fml -> fml.

Notation "A --> B" := (Imply A B) (at level 69, right associativity).

(* list of constants not NECESSARY

(** List of constants occurring in an expression *)

Fixpoint oc_t (t:trm) {struct t} : list name :=
  match t with
  | Ltr _       => nil
  | Par _ => nil
  | Cst c       => c :: nil
  | App _ t0 t1 => (oc_t t0) ++ (oc_t t1)
  end.

Fixpoint oc (A:fml) {struct A} : list name :=
  match A with
  | Atom (_,t) => oc_t t
  | Imply B C  => oc B ++ oc C
  | Forall x A => oc A
  end.

Fixpoint oc_c (Ga : list fml) {struct Ga} : list name :=
  match Ga with
  | nil      => nil
  | A :: Ga' => oc A ++ oc_c Ga'
  end.

 *)

(** List of letters occurring free in expressions *)

Fixpoint ol_t (t : trm) {struct t} : list name :=
  match t with
  | Ltr x       => x :: nil
  | Par _ => nil
  | Cst _       => nil
  | App _ t0 t1 => (ol_t t0) ++ (ol_t t1)
  end.

Fixpoint ol (A : fml) {struct A} : list name :=
  match A with
  | Atom (_,t) => ol_t t
  | Imply B C  => ol B ++ ol C
  | Forall x B => rm_name x (ol B)
  end.

Fixpoint ol_c (Ga : list fml) {struct Ga} : list name :=
  match Ga with
  | nil => nil
  | (A :: Ga')  => ol A ++ ol_c Ga'
  end.

(** List of parameters occurring free in expressions *)

Fixpoint op_t (t : trm) {struct t} : list name :=
  match t with
  | Ltr _       => nil
  | Par x      => x :: nil
  | Cst _       => nil
  | App _ t0 t1 => (op_t t0) ++ (op_t t1)
  end.

Fixpoint op (A : fml) {struct A} : list name :=
  match A with
  | Atom (_,t) => op_t t
  | Imply B C  => op B ++ op C
  | Forall x B => op B
  end.

Fixpoint op_c (Ga : list fml) {struct Ga} : list name :=
  match Ga with
  | nil => nil
  | (A :: Ga')  => op A ++ op_c Ga'
  end.

(** Fresh constants w.r.t. an expression *)

(* Definition fresh_t c t := c # (oc_t t). *)

(* Definition fresh c A := c # (oc A). *)

(** ** Decidability of syntactic equality *)

(** A specified tactic for uninteresting cases *)

Ltac neq_case :=
  match goal with
    | H : ?x <> ?y |- _ =>
      right; red; intro Heq; inversion Heq; congruence
  end.

(** [fml] is decidable. *)

Ltac neq_trm :=
  match goal with 
    | |- context [{Ltr ?n = Ltr ?m} + {Ltr ?n <> Ltr ?m}]     
      =>  destruct (n == m); subst; try neq_case; left; auto
                                                         
     | |- context [{Par ?n = Ltr ?m} + {Par ?n <> Ltr ?m}]     
      =>  right; discriminate

     | |- context [{Cst ?n = Ltr ?m} + {Cst ?n <> Ltr ?m}]     
      =>  right; discriminate

     | |- context [{App ?f ?n ?m = Ltr ?t} + {App ?f ?n ?m <> Ltr ?t}]     
      =>  right; discriminate
     (* Par *)
     | |- context [{Ltr ?n = Par ?m} + {Ltr ?n <> Par ?m}]
      =>  right; discriminate
                                                         
     | |- context [{Par ?n = Par ?m} + {Par ?n <> Par ?m}]
      =>  destruct (n == m); subst; try neq_case; left; auto

     | |- context [{Cst ?n = Par ?m} + {Cst ?n <> Par ?m}]
      =>  right; discriminate

     | |- context [{App ?f ?n ?m = Par ?t} + {App ?f ?n ?m <> Par ?t}]
      =>  right; discriminate
     (* Cst *)
     | |- context [{Ltr ?n = Cst ?m} + {Ltr ?n <> Cst ?m}]
      =>  right; discriminate
                                                         
     | |- context [{Par ?n = Cst ?m} + {Par ?n <> Cst ?m}]
      =>  right; discriminate

     | |- context [{Cst ?n = Cst ?m} + {Cst ?n <> Cst ?m}]
      =>  destruct (n == m); subst; try neq_case; left; auto

     | |- context [{App ?f ?n ?m = Cst ?t} + {App ?f ?n ?m <> Cst ?t}]
      =>  right; discriminate
     (* App *)
     | |- context [{Ltr ?n = App ?f ?m ?t} + {Ltr ?n <> App ?f ?m ?t}]
      =>  right; discriminate
                                                         
     | |- context [{Par ?n = App ?f ?m ?t} + {Par ?n <> App ?f ?m ?t}]
      =>  right; discriminate

     | |- context [{Cst ?n = App ?f ?m ?t} + {Cst ?n <> App ?f ?m ?t}]
      =>  right; discriminate
  end. 



Lemma trm_dec : 
  forall (t t0 : trm), {t = t0} + {t <> t0}.
Proof.
  induction t, t0; try neq_trm. 
  destruct (fun_dec f f0); destruct (IHt1 t0_1); destruct (IHt2 t0_2); 
  subst; try neq_case; left; auto. 
Defined.

Lemma atom_dec : forall (P Q : atom), {P = Q} + {P <> Q}.
Proof.
  destruct P as [p t]; destruct Q as [q u].
  decide equality; [ apply trm_dec | apply pred_dec ].
Qed.

Lemma fml_dec : forall (A B : fml), {A = B} + {A <> B}.
Proof.
  induction A as [P1 |A1 IHA1 A2 IHA2| x A IHA]; 
  destruct B as [P2 |B1 B2| y B]; try (right; discriminate).

  - decide equality; auto using atom_dec, eq_nat_dec.

  - destruct (IHA1 B1); destruct (IHA2 B2);
    [ subst; left; reflexivity
    | neq_case
    | neq_case
    | neq_case
    ].

  - destruct (eqdec x y).
    + subst x;
          destruct (IHA B) as [ | neq];
          [left; subst; reflexivity | 
           right; intro Heq; elim neq; inversion Heq; reflexivity].
    + right; intro Heq; elim n; inversion Heq; reflexivity.
  Qed.
    
(** A tactic for destructing the decidable equality between pseudo-expressions. *)

Ltac case_lang :=
  let destr t u := destruct (trm_dec t u); [try subst t | idtac] in
    let destr A B := destruct (fml_dec A B); [try subst A | idtac] in
  match goal with
    | |- context [trm_dec ?t ?u]       => destr t u
    | _ : context [trm_dec ?t ?u] |- _ => destr t u
    | |- context [fml_dec ?A ?B]       => destr A B
    | _ : context [fml_dec ?A ?B] |- _ => destr A B
  end.
