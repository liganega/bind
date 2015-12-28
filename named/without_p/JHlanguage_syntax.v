Set Implicit Arguments.

Require Import decidable_IN.
Require Import sublist.
Require Import associations.

(** * Language Syntax *)

(** The language syntax for the first-order logic is represented. The
  language contains implication and universal quantification as 
  the only logical symbols. 
  Moreover, We assume there are two decidable sets of infinitely many
  _unary_ predicates and _binary_ functions. This is general enough
  because predicate and function symbols of different arities can be
  encoded. 

  To deal with variables and variable binding we follow the idea of
  McKinna-Pollack's locally-named style where variables and parameters
  are used:  (locally bound) _variables_ and _parameters_ (also called
  _free_ variables).

  A main difference is that we renounce to use parameters, i.e., free
  variables. We show that we can show the same metatheoretic
  properties as when using parameters. 

  Syntactically, We don't use parameters (free variables). Instead,
  we let constants play the role of constants. An important
  consequence at the syntactic level is that substitution is needed
  only for variables. This results in less work in preparing the basis
  for the formalization.

  The language itself needs to contain infinitely many constants. This
  is because parameters are missing and something else should replace
  its role, both syntactically and semantically. Note that every
  first-order language can be conservatively extended to a language
  with infinitely many constants. *) 

(** We assume a set of unary predicates and a set of binary functions.
  They are both supposed to be decidable. *)

Parameter predicate : Set.      (* unary predicates *)
Parameter function : Set.       (* binary functions *)

Axiom pred_dec : decidable predicate.
Axiom fun_dec : decidable function.

  
(** ** Definition of terms and formulas*)

(** Here we use natural numbers to enumeration variables and
  constants. We note that any decidable, denumerable set can be used
  instead. *) 

Inductive trm : Set := 
| BVar : name -> trm
| Cst  : name -> trm
| App  : function -> trm -> trm -> trm.

(** Extra definition of atomic formulas is useful when dealing with
  Kripke semantics *)

Definition atom := (predicate * trm)%type.

Inductive fml : Set :=
| Atom   : atom -> fml
| Imply  : fml -> fml -> fml
| Forall : name -> fml -> fml.

Notation "A --> B" := (Imply A B) (at level 69, right associativity).

(** Contexts are list of formulas *)

Notation context := (list fml).

(** ** Lists of variables constants occurring in an expression *)

(** Lists of bound variables occurring unbound in an expression *)

Fixpoint bv_t (t : trm) {struct t} : list name :=
  match t with
  | BVar x       => x :: nil
  | Cst _       => nil
  | App _ t0 t1 => (bv_t t0) ++ (bv_t t1)
  end.

Fixpoint bv (A : fml) {struct A} : list name :=
  match A with
  | Atom (_,t) => bv_t t
  | Imply B C  => bv B ++ bv C
  | Forall x B => remove eqdec x (bv B)
  end.

Fixpoint bv_c (Ga : context) {struct Ga} : list name :=
  match Ga with
  | nil => nil
  | (A :: Ga')  => bv A ++ bv_c Ga'
  end.

(** Lists of constants occurring in an expression *)

Fixpoint oc_t (t:trm) {struct t} : list name :=
  match t with
  | BVar _       => nil
  | Cst c       => c :: nil
  | App _ t0 t1 => (oc_t t0) ++ (oc_t t1)
  end.

Fixpoint oc (A:fml) {struct A} : list name :=
  match A with
  | Atom (_,t) => oc_t t
  | Imply B C  => oc B ++ oc C
  | Forall x A => oc A
  end.

Fixpoint oc_c (Ga : context) {struct Ga} : list name :=
  match Ga with
  | nil      => nil
  | A :: Ga' => oc A ++ oc_c Ga'
  end.

(** ** Substitution operations *)

(** We prefer to use simultaneous substitutions for _bound_
  variables. Lists of pairs of names and terms are used to represent
  simultaneous substitutions. Substitutions are defined for terms,
  formulas, and contexts which are lists of formulas.

  Moreover, simultaneous substitution provides a perfect way in
  establishing the relationship between syntax and semantics. For
  example, soundness and completeness can be realized in a natural way
  using simultaneous substitution.

  Note that substitution only for variables are necessary because
  there are no parameters. *) 

Reserved Notation "t [[ rho ]]" (at level 70).
Reserved Notation "A [ rho ]" (at level 70).
Reserved Notation "Ga [! rho !]" (at level 70).

Fixpoint subst_t (t : trm) (rho:assoc trm) {struct t} : trm :=
  match t with
    | BVar y       => match rho ^^ y with
                     | Some u => u
                     | None   => BVar y
                     end
    | Cst c       => Cst c
    | App f t1 t2 => App f (t1 [[rho]]) (t2 [[rho]])
  end
  where "t [[ rho ]]" := (subst_t t rho).

Notation "t [[ rho ]]" := (subst_t t rho) (at level 70).

Fixpoint subst (A : fml) (rho: assoc trm) {struct A} : fml :=
  match A with
    | Atom (P,t) => Atom (P, t [[ rho ]] )
    | B --> C    => (B [ rho ]) --> (C [ rho ])
    | Forall y B => Forall y (B [ rho ^- y ])
  end
  where "A [ rho ]" := (subst A rho).

Notation "A [ rho ]" := (subst A rho) (at level 70).

Fixpoint subst_c (Ga : context) (rho: assoc trm) {struct Ga} : context :=
  match Ga with
    | nil => nil
    | A :: Ga' => (A [ rho ]) :: (Ga' [! rho !])
  end
  where "Ga [! rho !]" := (subst_c Ga rho).

Notation "Ga [! rho !]" := (subst_c Ga rho) (at level 70).

(** ** Opening *)

(** Definitionally, _opening_ is the single substitution which is
  usually used in dealing with substitution. In our work, opening
  playes a specific role in the definition of well-formedness and
  provability. *)

Definition open_t t x u := t [[(x,u)::nil]].
Definition open A x u := A [(x,u)::nil].

(** ** Well-formedness *)

(** The above definitions of terms and formulas involve some
  meaningless expressions in the sense that some bound variables are
  not bound. Therefore, we need distinguish them from the so-called
  _well-formed_ expressions. They are expressions without any free
  occurrence of variables. We inductively characterize well-formed
  terms and formulas. Moreover, we sometimes need to work with
  contexts composed of well-formed formulas only. *)   

Inductive wf_t : trm -> Prop :=
| wCst : forall x, wf_t (Cst x)
| wApp : forall f t1 t2, wf_t t1 -> wf_t t2 -> wf_t (App f t1 t2).

Inductive wf : fml -> Prop :=
| wAtom  : forall P t, wf_t t -> wf (Atom (P,t))
| wImply : forall A1 A2, wf A1 -> wf A2 -> wf (A1 --> A2)
| wForall: forall x c A, 
    c # oc A -> wf (open A x (Cst c)) -> wf (Forall x A).

Inductive wf_c : context -> Prop :=
| wNil : wf_c nil
| wCons : forall Ga A, wf_c Ga -> wf A -> wf_c (A :: Ga).

(** The rule [wForall] deserves attention. Since when a quantification 
  is just eliminated from a formula, a variable becomes suddenly
  unbound. This is the reason why just structural induction does not
  work.  

  There are several ways to deal with this problem. Here we use the
  technique of opening and replace a binder with _one_ fresh
  constant. Many discussions have been made about the style of
  opening. People used to say that the style we use is not so flexible
  enough for doing formalization work althogh the style we use here is
  most close to the pencil-and-paper practice of binding. 

  However, we will show that one could work smoothly with the style of
  dealing with opening we use here. *)

(** ** Decidability of syntactic expressions *)

(** In order to work with [IN] wrt [fml] it is necessary to show the
  decidability of each expression sets. *)

Lemma trm_dec : forall (t t0 : trm), {t = t0} + {t <> t0}.
Proof.
  induction t, t0;
  try destruct (n==n0); subst; auto;
  try do 4 (right; intro H; inversion H; auto).
  destruct (IHt1 t0_1), (IHt2 t0_2), (fun_dec f f0); 
    try rewrite e, e0, e1;
    solve [ left; auto | right; intro H; inversion H; auto].
Qed.

Lemma atom_dec : forall (P Q : atom), {P = Q} + {P <> Q}.
Proof.
  destruct P as [p t]; destruct Q as [q u].
  decide equality; [ apply trm_dec | apply pred_dec ].
Qed.

(** The following tacic is specified for dealing with uninteresting
  cases *) 

Ltac neq_case :=
  match goal with
    | H : ?x <> ?y |- _ =>
      right; red; intro Heq; inversion Heq; congruence
  end.

Lemma fml_dec : forall (A B : fml), {A = B} + {A <> B}.
Proof.
  induction A as [P1 |A1 IHA1 A2 IHA2| x A IHA]; 
  destruct B as [P2 |B1 B2| y B]; try (right; discriminate).

  - decide equality; auto using atom_dec, eq_nat_dec.
  - destruct (IHA1 B1); destruct (IHA2 B2);
    solve [ subst; left; reflexivity | neq_case].
  - destruct (eqdec x y).
    + subst x;
      destruct (IHA B) as [ | neq];
      [left; subst; reflexivity | 
       right; intro Heq; elim neq; inversion Heq; reflexivity].
    + right; intro Heq; elim n; inversion Heq; reflexivity.
Qed.
    
Hint Resolve trm_dec atom_dec fml_dec : datatypes.

(** We will need a tactic for destructing the decidable equality
  between pseudo-expressions. *) 

Ltac case_lang :=
  let destr t u := destruct (trm_dec t u); [try subst t | idtac] in
    let destr A B := destruct (fml_dec A B); [try subst A | idtac] in
  match goal with
    | |- context [trm_dec ?t ?u]       => destr t u
    | _ : context [trm_dec ?t ?u] |- _ => destr t u
    | |- context [fml_dec ?A ?B]       => destr A B
    | _ : context [fml_dec ?A ?B] |- _ => destr A B
  end.

(** ** Relation wrt contexts and formulas *)

(** The sub-context relation plays an important role in dealing with
  provability and Kripke semantics. However, we have to focus on
  well-formed contexts.

  First the sub-context relation [sub_ctx_pre] is defined for all
  contexts then we will focus on well-formed contexts when [sub_ctx]
  is defined. *)

Notation sub_ctx_pre := (@sublist fml fml_dec).

Definition sub_ctx (Ga Ga' : context) : Prop :=
  (Ga = Ga') \/( (sub_ctx_pre Ga Ga' /\ wf_c Ga')).

(** A notation for the membership wrt contexts and formulas *)

Notation IN_ctx := (IN fml_dec).

(** Some properties on contexts *)

Lemma IN_oc_sub (A:fml) (Ga:context) :
  IN_ctx A Ga ->
  sub_name (oc A) (oc_c Ga).
Proof.
  unfold sublist; induction Ga as [ | B]; simpl; intros; auto.
  case_lang; subst; eauto with datatypes.
Defined.

Implicit Arguments IN_oc_sub [A Ga].

Lemma sub_ctx_oc : forall (Ga De:context),
  sub_ctx_pre Ga De -> sub_name (oc_c Ga) (oc_c De).
Proof.
  unfold sublist; intros; induction Ga as [ | A]; simpl in * ; intros; intuition.
  destruct (IN_app_or H0). 
    generalize (H A); intros; case_lang; eauto 4 with datatypes.
    apply (IN_oc_sub (H2 I)); auto.

    apply IHGa; auto.
    intros B HB; generalize (H B); case_lang; tauto.
Defined.

Hint Resolve IN_oc_sub sub_ctx_oc : datatypes.
