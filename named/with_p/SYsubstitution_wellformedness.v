(** * Substitution for completeness  *)

Set Implicit Arguments.

Require Import associations.
Require Import associations_extra.
Require Import sublist.
Require Import language_syntax.
Require Export variable_sets.


(** Defining substitution requires special consideration for two reasons.

   - First, the relationship between syntax and semantics such as soundness
     and completeness should be realized in a natural way.

     For this purpose, we find that simultaneous substitution provides
     a convenient way in establishing the relationship.

   - Second, because of the trace part, it is not clear to which class
     the resulting expression of a substitution should belong.

     Thus we decided to state clearly the type of the resulting expression
     in the definition of substitution.


   - Notice the special role of the [Bvar] case because it needs relocation.

   - No alpha-conversion is used.

   - Since there are no parameters, substitution only for variables are necessary. *)

(** The type of simultaneous substitutions =: [name -> trm].
    Instead of using funntion type, lists of pairs of names and terms can be
    used for the simultaneous substitutions, but this is less handy. *)
(* ------------------------------ *)


(** *** Substitution functions *)

(** The type of simultaneous substitutions =: [name -> trm].
    Instead of using funntion type, lists of pairs of names and terms can be
    used for the simultaneous substitutions, but this is less handy. *)

Reserved Notation "t [[ rho , eta ]]" (at level 69).
Reserved Notation "A [ rho , eta ]" (at level 69).
Reserved Notation "Ga [! rho , eta !]" (at level 69).

Fixpoint subst_t (t : trm) (rho eta:assoc trm) {struct t} : trm :=
  match t with
    | Ltr y       => match eta ^^ y with
                     | Some u => u
                     | None   => Ltr y
                     end
    | Par x       => match rho ^^ x with
                     | Some u => u
                     | None   => Par x
                     end
    | Cst c       => Cst c
    | App f t1 t2 => App f (t1 [[rho, eta]]) (t2 [[rho, eta]])
  end
  where "t [[ rho , eta ]]" := (subst_t t rho eta).

Notation "t [[ rho , eta ]]" := (subst_t t rho eta) (at level 69).

Fixpoint subst (A : fml) (rho eta: assoc trm) {struct A} : fml :=
  match A with
    | Atom (P,t) => Atom (P, t [[ rho , eta ]] )
    | B --> C    => (B [ rho, eta ]) --> (C [ rho, eta ])
    | Forall y B => Forall y (B [ rho , eta ^- y])
  end
  where "A [ rho , eta ]" := (subst A rho eta).

Notation "A [ rho , eta ]" := (subst A rho eta) (at level 69).

Fixpoint subst_c (Ga : list fml) (rho eta: assoc trm) {struct Ga} : list fml :=
  match Ga with
    | nil => nil
    | A :: Ga' => (A [ rho , eta]) :: (Ga' [! rho , eta !])
  end
  where "Ga' [! rho , eta !]" := (subst_c Ga' rho eta).

Notation "Ga [! rho , eta !]" := (subst_c Ga rho eta) (at level 69).


(** Opening a term: replacing a letter by a term *)

Definition open_t t x u := t [[nil , (x,u)::nil ]].

Definition open A x u := A [ nil , (x,u)::nil ].


(** Substitution  *)

(** Defining substitution requires special consideration for two reasons.

   - First, the relationship between syntax and semantics such as soundness
     and completeness should be realized in a natural way.

     For this purpose, we find that simultaneous substitution provides
     a convenient way in establishing the relationship.

   - Second, because of the trace part, it is not clear to which class
     the resulting expression of a substitution should belong.

     Thus we decided to state clearly the type of the resulting expression
     in the definition of substitution.


   - Notice the special role of the [Bvar] case because it needs relocation.

   - No alpha-conversion is used.

   - Since there are no parameters, substitution only for variables are necessary. *)

(** The type of simultaneous substitutions =: [name -> trm].
    Instead of using funntion type, lists of pairs of names and terms can be
    used for the simultaneous substitutions, but this is less handy. *)


Definition substitution := assoc trm.

Definition par_substitution := assoc name.

Fixpoint subst_emb (rho: par_substitution) : substitution :=
  match rho with
  | nil            => nil
  | (x, a) :: rho' => (x, Par a) :: subst_emb rho'
  end.



(** ** Well-formedness *)

(** Well-formed expressions are expressions without any free occurrence of letters. *)

Inductive wf_t : trm -> Prop :=
| wCst : forall x, wf_t (Cst x)
| wPar : forall x, wf_t (Par x)
| wApp : forall f t1 t2, wf_t t1 -> wf_t t2 -> wf_t (App f t1 t2).

Inductive wf : fml -> Prop :=
| wAtom  : forall P t, wf_t t -> wf (Atom (P,t))
| wImply : forall A1 A2, wf A1 -> wf A2 -> wf (A1 --> A2)
| wForall: forall x c A, c # op A -> wf (open A x (Par c)) -> wf (Forall x A).

(** A list of well-formed formulas is called [context].
    That condition is expressed by ok-ness. *)

Inductive wf_c : list fml -> Prop :=
| wNil : wf_c nil
| wCons : forall Ga A, wf_c Ga -> wf A -> wf_c (A :: Ga).



(** * sub_ctx : this is used in completeness  *)
Definition sub_ctx (Ga Ga' : context) : Prop :=
  (Ga = Ga') \/( (sub_ctx_pre Ga Ga' /\ wf_c Ga')).

Lemma indeed_sub_ctx_is : 
  forall Ga Ga',
    sub_ctx Ga Ga' ->
    sub_ctx_pre Ga Ga'.
Proof.
  intros. destruct H as [Heq | Hsub Hwf];
  [ rewrite Heq; auto with datatypes 
  | apply Hsub].
Defined.

(* ------------------------------ *)

Lemma nil_subst_t : 
  forall t,
    t = (t [[nil, nil]]).
Proof.
  induction t; simpl; auto; f_equal; auto.
Defined. 

Lemma nil_subst :
  forall A,
    A = (A [nil, nil]).
Proof.
  induction A as [ [p t] | |]; auto; simpl.
  - rewrite <- nil_subst_t; auto.
  - f_equal; auto.
  - rewrite <- IHA; auto.
Defined.

(* a bunch of definitions about subst/open belongs language_syntax *)

(* Coercion does not work correctly with Fixpoint??

Coercion subst_emb : cst_substitution >-> substitution. *)

Lemma par_sub_par : 
  forall rho m u,
    subst_emb rho ^^ m = Some u -> exists a, u = Par a.
Proof. 
  induction rho as [| [n t] rho]; auto; simpl; intros. 
  - discriminate.
  - case_var; auto. 
    + exists t; inversion H; auto. 
    + apply IHrho with m; auto. 
Defined.


Lemma open_subst_t : 
  forall u (eta: par_substitution) n t, 
    open_t (u [[nil , subst_emb eta ^- n]]) n t 
    = (u [[ nil , (n, t) :: subst_emb eta]]).
Proof.
  unfold open_t; induction u as [ m | m | m | ]; simpl; intros; auto.
  - case_var.
    + rewrite assoc_rm_self; simpl; destruct (n==n); intuition. 
    + rewrite <- assoc_rm_neq; auto.
      pose proof (par_sub_par eta m).
      destruct (subst_emb eta ^^ m). 
      * { pose proof (H t0).
          assert (exists c, t0 = Par c).
          - apply H0; auto.
          - destruct H1; rewrite H1; auto.   
        }
      * simpl; auto.
        destruct (m==n); firstorder.
  - f_equal; auto. 
Defined.

Lemma emb_rm : 
  forall rho m,
    subst_emb (rho ^- m) = subst_emb rho ^- m.
Proof.
  induction rho as [| [n n'] rho]; auto; simpl; intros.
  case_var; auto.
  simpl; f_equal; auto. 
Defined.

Lemma open_subst :
  forall A eta n t, 
    open (A [nil, subst_emb eta ^- n]) n t 
    = ( A [nil , (n, t) :: subst_emb eta]).
Proof.
  unfold open; induction A as [ [P u]| | m ]; simpl; intros; f_equal; auto.
  - f_equal;
    apply open_subst_t; auto. 
  - case_var. 
    * rewrite <- nil_subst, <- rm_rm; auto. 
    * rewrite rm_neq_rm, <- emb_rm; auto. 
Defined.

Lemma IN_ren_sub :
  forall n rho,
    n @ dom rho -> n @ dom (subst_emb rho).
Proof.
  induction rho as [| [m m'] rho]; auto; simpl.
  case_var; auto.
Defined.

