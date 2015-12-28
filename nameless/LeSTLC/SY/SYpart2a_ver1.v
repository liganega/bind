(** This chapter addresses part 2A of the POPLmark challenge, namely the proof
  of soundness of the $F_{<:}$ type systems without records. *)

Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import SYextralibrary.
Require Import SYdecidable_IN.
Require Import SYsublist.
Require Import SYpart1a.


(** * Terms *)

(** We now define the syntax of $F_{<:}$ terms and basic syntactic notions such
  as free variables, substitutions, and well-formedness of terms.
  We follow the same approach used for types in chapter 2.  *)

(** ** Syntax and syntactic operations *)

(** The syntax of terms is defined as follows. 
  As in types, bound variables are represented by de Bruijn indices,
  while free variables are represented by names.  Bound term variables
  and bound type variables are numbered independently.  In a
  lambda-abstraction [TFun t a], the term variable [Var 0] is bound in
  [a].  In a type abstraction [TApp t a], the type variable [TVar 0]
  is bound in [a]. *)

(* list lemma *)
Lemma notIn_app : forall A  (a:A) (l m :list A),
  ~ In a (l ++ m) ->
  ~ In  a l /\ ~ In  a m.
Proof.
  firstorder. 
Qed.

Lemma notIn_app_1 : 
  forall A (a: A) (l m : list A),
    ~ In a l -> ~ In a m -> ~ In a (l ++ m).
Proof.
  intuition. elim (in_app_or l m a H1); auto.
Qed.
(* list lemma *)

Inductive term : Set :=
  | Param: name -> term
  | Var: nat -> term
  | Fun: type -> term -> term
  | App: term -> term -> term.

(** The free names of a term include both type names and term names. *)

Fixpoint fv_term (a: term) : list name :=
  match a with
  | Param v => v :: nil
  | Var n => nil
  | Fun t a1 => fv_term a1
  | App a1 a2 => fv_term a1 ++ fv_term a2
  end.

Definition v_termenv := list (nat * term).
Definition p_termenv := list (name * term).
Definition renaming := list (name * name).

Fixpoint v_dom (e: v_termenv) {struct e} : list nat :=
  match e with
    | nil           => nil
    | (x,t) :: e0 => x :: (v_dom e0)
  end.

Fixpoint fun_v_assoc (e: v_termenv) (x: nat) {struct e} : option term := 
  match e with
    | nil => None
    | (y,t) :: e0
      => if eqdec x y then Some t else fun_v_assoc e0 x
  end.

Notation " e ^^ x " := (@fun_v_assoc e x) (at level 60).

Fixpoint v_shift (e: v_termenv) : v_termenv :=
  match e with
  | nil => nil
  | (x, t) :: e0 => (S x, t) :: v_shift e0
  end.

Fixpoint v_less (e: v_termenv) n : nat :=
  match e with
  | nil => 0
  | (i, t) :: e0 => if lt_dec i n
                    then S (v_less e0 n)
                    else v_less e0 n
  end.

Fixpoint vsubst_term (a: term) (e: v_termenv) {struct a} : term :=
  match a with
  | Param v => Param v
  | Var n =>
      match e ^^ n with
      | Some t => t
      | None => Var (n - (v_less e n))
      end
  | Fun t a1 => Fun t (vsubst_term a1 (v_shift e)) 
  | App a1 a2 => App (vsubst_term a1 e) (vsubst_term a2 e)
  end.

(** There are 4 substitution operations over terms,
  depending on whether we are substituting a named variable ([psubst_])
  or a de Bruijn variable ([vsubst_]), and whether we are substituting
  a term for a term variable ([_term]) or a type for a type variable
  ([_tety]). *)

Fixpoint p_dom (e: p_termenv) {struct e} : list name :=
  match e with
    | nil           => nil
    | (x,t) :: e0 => x :: (p_dom e0)
  end.

Fixpoint fun_p_assoc (e: p_termenv) (x: name) {struct e} : option term := 
  match e with
    | nil => None
    | (y,t) :: e0
      => if eq_name x y then Some t else fun_p_assoc e0 x
  end.

Notation " e ^^^ x " := (@fun_p_assoc e x) (at level 60).

Fixpoint psubst_term (a: term) (e: p_termenv) {struct a} : term :=
  match a with
  | Param v => 
       match e ^^^ v with
         | Some t => t
         | None => Param v
       end
  | Var n => Var n
  | Fun t a1 => Fun t (psubst_term a1 e)
  | App a1 a2 => App (psubst_term a1 e) (psubst_term a2 e)
  end.

Fixpoint subst_term (a: term) (ep: p_termenv) (ev: v_termenv) {struct a} : term :=
  match a with
  | Param v => 
       match ep ^^^ v with
         | Some t => t
         | None => Param v
       end
  | Var n =>
      match ev ^^ n with
      | Some t => t
      | None => Var (n - (v_less ev n))
      end
  | Fun t a1 => Fun t (subst_term a1 ep (v_shift ev))
  | App a1 a2 => App (subst_term a1 ep ev) (subst_term a2 ep ev)
  end.

  
(** Here are the two ``freshening'' operations that replace the bound variable
  0 with a term or type name, respectively. *)

Definition freshen_term (a: term) (x: name) : term :=
  vsubst_term a ((0, (Param x)) :: nil).


(** Substitutions and freshening play well with free variables. *)
Lemma fv_term_vsubst_term:
  forall x a e, In x (fv_term a) -> In x (fv_term (vsubst_term a e)).
Proof.
  induction a; simpl; intros; auto;
  try contradiction;
  elim (in_app_or _ _ _ H); eauto. 
Qed. 


Lemma fv_term_freshen_term:
  forall x a y, In x (fv_term a) -> In x (fv_term (freshen_term a y)).
Proof.
  intros; unfold freshen_term; apply fv_term_vsubst_term; auto.
Qed.




Inductive wf_term: typenv -> term -> Prop :=
  | wf_term_param: forall (e : typenv) (x:name),
      kind x = TERM -> In x (dom e) -> wf_term e (Param x)
  | wf_term_fun: 
      forall (e : typenv) (t:type) (a:term),    
      (forall (x: name) , kind x = TERM 
                         -> ~In x ((fv_term a) ++ (dom e)) 
                         -> wf_term ((x, t) :: e) (freshen_term a x)) 
      -> wf_term e (Fun t a)
(*  | wf_term_fun: forall e t a,
      (forall x,
       kind x = TERM ->
       ~In x (fv_term a) -> ~In x (dom e) ->
       wf_term (freshen_term a x)) ->
      wf_term (Fun t a)
*)
  | wf_term_app: forall e a1 a2,
      wf_term e a1 
      -> wf_term e a2 
      -> wf_term e (App a1 a2).

(* added *)
(*
Lemma fv_dom_type: forall x e t, dom_type e t -> In x (fv_type t) -> In x (dom e).
Proof.
  induction 1; simpl; intros.
  - intuition; subst; auto. 
  - elim (in_app_or _ _ _ H1); 
    intros; [apply IHdom_type1 | apply IHdom_type2]; auto.
 Qed.
(* added *)

Lemma fv_wf_term: forall x e t, wf_term e t -> In x (fv_term t) -> In x (dom e).
Proof.
  induction 1; simpl; intros.
  - intuition; subst; auto.

  - elim (in_app_or _ _ _ H1); intros; induction t; simpl. 
    + eapply fv_dom_type; eauto. constructor; auto.  with t; eauto. admit.
    + 

        destruct (fresh_name TERM (x :: fv_term a ++ dom e)) as [y [F K]].
        assert (In x (dom ((y, t) :: e))). 
        apply H0; eauto. apply fv_term_freshen_term. auto. 
  simpl dom in H3. eauto.
  (* app *)
-   elim (in_app_or _ _ _ H1); auto.


  (* tfun *)
  elim (in_app_or _ _ _ H2); intro.
  eapply fv_wf_type; eauto.
  destruct (fresh_name TYPE (x :: fv_term a ++ dom e)) as [y [F K]].
  assert (In x (dom ((y, t) :: e))). 
    apply H1; eauto. apply fv_term_freshen_tety. auto. 
  simpl dom in H4; eauto.
  (* tapp *)
  elim (in_app_or _ _ _ H1); intro.
  auto.
  eapply fv_wf_type; eauto.
Qed.

unfold dom_type. red. destruct dom_type. destruct (fresh_name TERM (x :: fv_term a ++ dom e)) as [y [F K]].
  assert (In x (dom ((y, t) :: e))). 
    apply H1; eauto. apply fv_term_freshen_term. auto. 
  simpl dom in H4. eauto.
  (* app *)
  elim (in_app_or _ _ _ H1); auto.
  (* tfun *)
  elim (in_app_or _ _ _ H2); intro.
  eapply fv_wf_type; eauto.
  destruct (fresh_name TYPE (x :: fv_term a ++ dom e)) as [y [F K]].
  assert (In x (dom ((y, t) :: e))). 
    apply H1; eauto. apply fv_term_freshen_tety. auto. 
  simpl dom in H4; eauto.
  (* tapp *)
  elim (in_app_or _ _ _ H1); intro.
  auto.
  eapply fv_wf_type; eauto.
Qed.
*)

Lemma fv_wf_term: forall t x e, wf_term e t -> In x (fv_term t) -> In x (dom e).
Proof.
  induction 1; simpl; intros; auto. inversion H; subst; auto. 
  - intuition; subst; auto. 
  - destruct (fresh_name TERM (x :: fv_term a ++ dom e)) as [y [F K]].
  assert (In x (dom ((y, t) :: e))). 
  apply H0; eauto. apply fv_term_freshen_term; auto. 
  simpl dom in H2; eauto.
  - elim (in_app_or _ _ _ H1); auto. 
Qed.

(*
Lemma fv_term_freshen_tety:
  forall x a y, In x (fv_term a) -> In x (fv_term (freshen_tety a y)).
Proof.
  intros; unfold freshen_tety; apply fv_term_vsubst_tety; auto.
Qed.
*)

(** Swaps of two names in a term. *)

(** Swaps commute with the free variables operation. *)

(** Swaps are self-inverse. *)

(** Swaps commute with substitutions and freshening. *)

(** ** Well-formedness of terms *)

(** A term is well-formed in a typing environment if:
  - all types contained within are well-formed as per [wf_type];
  - all names [n] appearing free in a [Param n] subterm are of kind [TERM]
    and are bound in the environment;
  - it does not contain free de Bruijn variables.
*)

(** A term well formed in [e] has all its free names in the domain of [e]. *)

(** Well-formedness is stable under swaps. *)

(** A term well-formed in [e] remains well-formed if extra bindings are added to [e]. *)

(** Here are two admissible rules that prove the well-formedness of [Fun] and [TFun]
  abstractions.  These rules are similar to the [wf_term_fun] and
  [wf_term_tfun] rules, but with a premise of the form ``there exists
  a name'' instead of the original ``for all names''.  *)

(** ** Properties of term substitutions *)

(** To prove the usual properties of term substitutions, we follow the
  same approach as for type substitutions, starting with a
  characterization of terms that have no free de Bruijn variables, or
  all such variables below some threshold. *)

Fixpoint term_vars_below (a: term) (nterm ntype: nat) {struct a} : Prop :=
  match a with
  | Param x => True
  | Var n => n < nterm
  | Fun t b => term_vars_below b (S nterm) ntype
  | App b c => term_vars_below b nterm ntype /\ term_vars_below c nterm ntype
(*  | TFun t b => type_vars_below t ntype /\ term_vars_below b nterm (S ntype)
  | TApp b t => term_vars_below b nterm ntype /\ type_vars_below t ntype*)
  end.

Lemma term_vars_below_vsubst_term:
  forall a nterm ntype a',
  term_vars_below (vsubst_term a ((nterm, a'):: nil)) nterm ntype -> 
  term_vars_below a  (S nterm) ntype.
Proof.
  induction a; auto; intros. 
  - destruct (compare_nat n nterm); subst; auto; simpl;
    [ omega
    | auto
    | simpl in H; 
      destruct (n == nterm); auto with arith; firstorder;
      simpl in H; replace (if lt_dec nterm n then 1 else 0) with 1 in H;
      [ omega
      | destruct lt_dec; auto; contradiction] ]. 
  - simpl in *; auto. 
    apply IHa with a'; auto.
  - simpl in *; destruct H; split; auto; [apply IHa1 with a' | apply IHa2 with a']; auto.
Qed.

(*
Lemma term_vars_below_vsubst_tety:
  forall a nterm ntype a',
  term_vars_below (vsubst_tety a ntype a') nterm ntype -> 
  term_vars_below a nterm (S ntype).
Proof.
  generalize type_vars_below_vsubst; intro.
  induction a; simpl; intros; firstorder.
Qed.
*)
(*
Fixpoint In_fv_type (x : name) (t: type) : Prop :=
  match t with
  | Tparam x => In x (fv_type t) 
  | Arrow t1 t2 => (In_fv_type x t1) /\ (In_fv_type x t2)
  end.

Lemma wf_type_vars_below_0: forall x e t, In_fv_type x t -> In x (dom e) -> type_vars_below t 0.
Proof.
  induction t; simpl. auto.
  intros; auto. split; destruct H as [Hl Hr] ; [apply IHt1 | apply IHt2]; auto.
Qed.
*)

Lemma wf_term_vars_below_0: forall a e, wf_term e a -> term_vars_below a 0 0.
Proof.
  (* generalize wf_type_vars_below_0; intro. *)
  induction 1; simpl; firstorder.
  destruct (fresh_name TERM (fv_term a ++ dom e)) as [x [F K]].
  apply notIn_app with (l:= (fv_term a)) (m := (dom e)) in F; destruct F as [Fv  Fd].
  apply term_vars_below_vsubst_term with (Param x). apply H0; eauto.
  apply notIn_app_1; auto. 
Qed.


Lemma vsubst_term_invariant_below:
  forall a n1 n2 m b, term_vars_below a n1 n2 -> n1 <= m -> vsubst_term a ((m, b) :: nil) = a.
Proof.
  induction a; simpl; intros; try decEq; firstorder.
  destruct ( n == m); auto. subst; omega. 
  destruct (lt_dec m n); firstorder. 
Qed.

(*
Lemma vsubst_tety_invariant_below:
  forall a n1 n2 m t, term_vars_below a n1 n2 -> n2 <= m -> vsubst_tety a m t = a.
Proof.
  generalize vsubst_invariant_below; intro.
  induction a; simpl; intros; decEq; firstorder.
Qed.
*)

Lemma vsubst_term_wf_term:
  forall a n b e, wf_term e a -> vsubst_term a ((n, b):: nil) = a.
Proof.
  intros. apply vsubst_term_invariant_below with 0 0. 
  eapply wf_term_vars_below_0; eauto.  omega.
Qed.

(*
Lemma vsubst_tety_wf_term:
  forall e a n t, wf_term e a -> vsubst_tety a n t = a.
Proof.
  intros. apply vsubst_tety_invariant_below with 0 0. 
  eapply wf_term_vars_below_0; eauto. omega.
Qed.
*)

Lemma psubst_vsubst_term:
  forall e a x b n c,
  wf_term e b -> 
  vsubst_term (psubst_term a ((x, b) :: nil)) ((n, (psubst_term c ((x, b) :: nil))) :: nil)
  = psubst_term (vsubst_term a ((n, c) :: nil)) ((x, b) :: nil).
Proof.
  induction a; intros; simpl; try decEq; auto.
  - case (eq_name n x); intro; simpl; auto.
    eapply vsubst_term_wf_term; eauto. 
  - destruct ( n == n0); subst; auto. 
Qed.

Lemma psubst_freshen_term:
  forall e a x b y,
  wf_term e b -> x <> y ->
  freshen_term (psubst_term a ((x, b) :: nil)) y = psubst_term (freshen_term a y) ((x, b) :: nil).
Proof.
  intros; unfold freshen_term. 
  rewrite <- (psubst_vsubst_term e); auto.
  simpl. rewrite eq_name_false; auto.
Qed.

(*S
Lemma psubst_vsubst_tety:
  forall e a x b n c,
  wf_type e b -> 
  vsubst_tety (psubst_tety a x b) n (psubst_type c x b) =
  psubst_tety (vsubst_tety a n c) x b.
Proof.
  induction a; intros; simpl; try decEq; auto;
  eapply psubst_vsubst_type; eauto.
Qed.

Lemma psubst_freshen_tety:
  forall e a x b y,
  wf_type e b -> x <> y ->
  freshen_tety (psubst_tety a x b) y = psubst_tety (freshen_tety a y) x b.
Proof.
  intros. unfold freshen_tety. 
  rewrite <- (psubst_vsubst_tety e); auto.
  simpl. rewrite eq_name_false; auto.
Qed.

Lemma psubst_vsubst_tetety:
  forall e a x b n c,
  wf_type e b -> 
  vsubst_term (psubst_tety a x b) n (psubst_tety c x b) = 
  psubst_tety (vsubst_term a n c) x b.
Proof.
  induction a; intros; simpl; try decEq; auto.
  destruct (compare_nat n n0); auto. 
Qed.

Lemma psubst_freshen_tetety:
  forall e a x b y,
  wf_type e b -> x <> y ->
  freshen_term (psubst_tety a x b) y = psubst_tety (freshen_term a y) x b.
Proof.
  intros. unfold freshen_term. 
  rewrite <- (psubst_vsubst_tetety e); auto.
Qed.

Lemma psubst_vsubst_tetyte:
  forall e a x b n c,
  wf_term e b -> 
  vsubst_tety (psubst_term a x b) n c = psubst_term (vsubst_tety a n c) x b.
Proof.
  induction a; intros; simpl; try decEq; auto.
  destruct (eq_name n x); auto. eapply vsubst_tety_wf_term; eauto.
Qed.

Lemma psubst_freshen_tetyte:
  forall e a x b y,
  wf_term e b -> x <> y ->
  freshen_tety (psubst_term a x b) y = psubst_term (freshen_tety a y) x b.
Proof.
  intros; unfold freshen_tety. eapply psubst_vsubst_tetyte; eauto.
Qed.
S*)

Lemma vsubst_psubst_term:
  forall x a2 a1 n,
  ~In x (fv_term a1) ->
  (subst_term a1 nil ((n, a2) :: nil)) = (subst_term (subst_term a1 nil ((n, Param x) :: nil)) ((x, a2) :: nil) nil).
(* vsubst_term a1 n a2 = psubst_term (vsubst_term a1 n (Param x)) x a2. *)
Proof.
  induction a1; simpl; intros.
  - rewrite eq_name_false; tauto. 
  (* destruct (compare_nat n n0); auto. *) 
  (* simpl. rewrite eq_name_true; auto. *)
  - destruct (n == n0); subst; auto. 
    + unfold subst_term. simpl. destruct (eq_name x x); subst; tauto. 
    + destruct (lt_dec n0 n); auto; simpl; auto with arith. 
  - rewrite IHa1; auto. 
  - destruct (notIn_app name x (fv_term a1_1) (fv_term a1_2) H). rewrite IHa1_1, IHa1_2; auto. 
Qed.

Lemma subst_vsubst :
  forall a ev,
    subst_term a nil ev = vsubst_term a ev.
Proof. 
  induction a, ev; auto; intros; simpl;
  [ rewrite IHa 
  | rewrite IHa
  | rewrite IHa1, IHa2
  | rewrite IHa1, IHa2] ; auto. 
Qed.

Lemma subst_psubst :
  forall a ep,
    subst_term a ep nil = psubst_term a ep.
Proof. 
  induction a, ep; intros; simpl; auto with arith; 
  [ rewrite IHa 
  | rewrite IHa
  | rewrite IHa1, IHa2
  | rewrite IHa1, IHa2] ; auto. 
Qed.

Lemma vsubst_psubst_freshen_term:
  forall x a1 a2,
  ~In x (fv_term a1) ->
  (subst_term a1 nil ((0, a2) :: nil)) = (subst_term (freshen_term a1 x) ((x, a2) :: nil) nil).
Proof.
  intros; unfold freshen_term. 
  rewrite vsubst_psubst_term with (x:=x); auto. 
  rewrite subst_vsubst; auto.
Qed.

(*S
Lemma vsubst_psubst_tety:
  forall x t2 a1 n,
  ~In x (fv_term a1) ->
  vsubst_tety a1 n t2 = psubst_tety (vsubst_tety a1 n (Tparam x)) x t2.
Proof.
  generalize vsubst_psubst_type; intro.
  induction a1; simpl; intros; decEq; auto.
Qed.

Lemma vsubst_psubst_freshen_tety:
  forall x a1 t2,
  ~In x (fv_term a1) ->
  vsubst_tety a1 0 t2 = psubst_tety (freshen_tety a1 x) x t2.
Proof.
  intros; unfold freshen_tety; apply vsubst_psubst_tety; auto.
Qed.
S*)

(** * Typing rules *)

(** We now define the typing judgement ``term [a] has type [t] in 
  environment [e]'' as an inductive predicate [has_type e a t]. *)

(* well-formed environment : no duplicate names *)

Inductive wf_env: typenv -> Prop :=
  | wf_env_nil:
      wf_env nil
  | wf_env_cons: forall x t e,
      wf_env e -> ~In x (dom e) -> 
      wf_env ((x, t) :: e).

(* Typing *)

Inductive has_type: typenv -> term -> type -> Prop :=
  | t_var: forall e x t,
      wf_env e -> kind x = TERM -> lookup x e = Some t ->
      has_type e (Param x) t
  | t_abs: forall e t1 a t2,
      (forall x,
        kind x = TERM -> ~In x (fv_term a ++ dom e) ->
        has_type ((x, t1) :: e) (freshen_term a x) t2
      ) 
      -> has_type e (Fun t1 a) (Arrow t1 t2)
  | t_app: forall e a b t1 t2,
      has_type e a (Arrow t1 t2) -> has_type e b t1 ->
      has_type e (App a b) t2.

(** Well-formedness properties: if [has_type e a t] holds, then
  [e] is a well-formed environment, [t] a well-formed type
  and [a] a well-formed term. *)


Lemma has_type_wf_env: forall e a t, has_type e a t -> wf_env e.
Proof.
  induction 1; auto. 
  destruct (fresh_name TERM ((fv_term a) ++ (dom e))) as [x [FRESH KIND]]. assert (~ In x (fv_term a)). eauto using notin_app_l. 
  (* assert (~ In x (dom e)); eauto using notin_app_r.  *)
  generalize (H0 x KIND FRESH); intros H2. inversion H2; auto.
Qed.


Lemma has_type_wf_term: forall e a t, has_type e a t -> wf_term e a.
Proof.
  induction 1; auto; intros; constructor; auto.
  eapply lookup_inv; eauto.
Qed.

Lemma env_concat_weaken:
  forall delta gamma,
  wf_env (delta ++ gamma) -> env_weaken gamma (delta ++ gamma).
Proof.
  induction delta; red; auto; intros. inversion H; simpl. 
  rewrite eq_name_false. 
  - apply IHdelta; auto. 
  - intro; subst; auto.
    apply H4; unfold dom; rewrite map_append; 
    apply in_or_app; right; eauto using lookup_inv. 
Qed.

Hint Resolve has_type_wf_env has_type_wf_term.

(** The [has_type] predicate is stable by addition of hypotheses. *)
(*
Lemma wf_type_weaken: forall e e' t, wf_type e t -> env_weaken e e' -> wf_type e' t.
Proof.
  intros. apply wf_type_env_incr with e; auto. apply env_weaken_incl_dom; auto.
Qed.

Lemma wf_term_weaken: forall e e' a, wf_term e a -> env_weaken e e' -> wf_term e' a.
Proof.
  intros. apply wf_term_env_incr with e; auto. apply env_weaken_incl_dom; auto.
Qed.
*)
Lemma env_weaken_add:
  forall e e' x t, 
    env_weaken e e' 
    -> env_weaken ((x, t) :: e) ((x, t) :: e').
Proof.
  intros; red; intros x' t'. simpl. 
  case (eq_name x' x); intro; auto. 
Qed.

Hint Resolve env_weaken_add.

(*Lemma trm_dec : 
  forall (t t0 : trm), {t = t0} + {t <> t0}.
Proof.
  induction t, t0; try neq_trm. 
  destruct (fun_dec f f0); destruct (IHt1 t0_1); destruct (IHt2 t0_2); 
  subst; try neq_case; left; auto. 
*)

(* type is decidable *)

Lemma eq_type : 
  forall (t t0 : type), { t = t0 } + {t <> t0}.
  induction t, t0. 
  - decide equality;
    case (eq_name n1 n2); subst; auto. 
  - right; discriminate. 
  - right; discriminate. 
  - decide equality; 
    case (eq_name n n0); subst; auto. 
Qed. 

Lemma eq_te : 
  forall (te te0 : (name * type)), {te = te0} + {te <> te0}.
  induction te, te0. 
  destruct (eq_name a n); subst; auto. 
  - destruct (eq_type b t); subst; auto. 
    + right; red; intro F; apply n0; congruence. 
  - right; red; intro F; apply n0; congruence.
Qed.

Notation sub_env := (@sublist (name * type) eq_te). 
(*
lookup = 
fix lookup (x : name) (e : typenv) {struct e} : option type :=
  match e with
  | nil => None
  | (y, t) :: e' => if eq_name x y then Some t else lookup x e'
  end
     : name -> typenv -> option type

IN = 
fix IN (A : Type) (decA : decidable A) (a : A) (l : list A) {struct l} :
  Prop :=
  match l with
  | nil => False
  | b :: m => if decA a b then True else IN A decA a m
  end
     : forall A : Type, decidable A -> A -> list A -> Prop

*)

Lemma lookup_IN :
  forall x e t,
    lookup x e = Some t -> IN (eq_te) (x, t) e.
Proof.
  induction e; intros; simpl; auto. 
  inversion H. 
  destruct (eq_te (x, t) a); subst; auto. inversion H.  destruct a as [y u]. 
  apply IHe; auto. destruct (eq_name x y); auto. subst; auto.
  simpl in H. destruct (eq_name y y); subst; congruence. 
Qed.

Lemma wf_cons_e :
  forall x t e,
    wf_env ((x,t) :: e) ->
    wf_env e.
Proof.
  intros ? ? ? H. inversion H; auto.
Qed.

(* need to move *)
Lemma IN_dom :
  forall x t e,
    IN (eq_te) (x, t) e -> In x (dom e).
Proof. 
  induction e as [| [y u] e]; auto; intros; simpl.
  destruct (eq_te (x,t) (y, u)); 
    [left; inversion e0
    | right; apply IHe; eapply neq_IN_cons]; eauto.
Qed.

Lemma IN_lookup :
  forall x e t,
    wf_env e ->
    IN (eq_te) (x, t) e -> lookup x e = Some t.
Proof.
  induction e as [ | [y u] e] ; intros; auto. 
  - inversion H0.
  - destruct (eq_te (y, u) (x, t) ).
    + rewrite e0; auto. simpl; destruct (eq_name x x); subst; auto; congruence. 
    + generalize (neq_IN_cons eq_te e n H0); intro H1. inversion H; subst.
      destruct (eq_name x y); subst; auto. 
      apply (IN_dom y t e) in  H1. contradiction. 
      simpl. destruct (eq_name x y); subst; auto. contradict n0; auto.
Qed.
    
Lemma sub_env_weaken :
  forall e2,
    wf_env e2 -> (forall e1, sub_env e1 e2 <-> env_weaken e1 e2).
Proof. 
(*  split; intros. 
  red; intros. unfold sublist in H. 
  induction e1. inversion H0. 
  apply IHe1; intros. apply H; auto with datatypes. 
  destruct a as [n t0]; subst; auto. inversion H0.
  destruct (eq_name x n); subst; auto. apply H2.  
*)
  
  induction e1; split; simpl; auto; intros.
  - red; intros. inversion H1. 
  - red; intros. inversion H1. 
  - red; intros. 

destruct a as [n t]; subst; auto. red; intros. 
    apply IHe1; auto with datatypes. 
    case (eq_name x n); intro; subst; auto. inversion H0. destruct (eq_name n n) in H2. simpl. destruct (eq_name n n); subst; auto. discriminate.  red.  replace (lookup n ((n, t) :: e1)) with (Some t) in H0; auto. 
red.  simpl.  apply H0. decEq. eqDec.

red in IHe1. apply IHe1. eapply sub_cons_1; eauto.  
    inversion H0. destruct (eq_name x n); subst; auto. inversion H2; subst.   assert (t = t0). inversion H2; auto. congruence. discriminate. 
    rewrite H2. discriminate. red in H0. 
congruence.  with datatypes. 
    
 simpl; auto. 

(*
Lemma 0 :
  forall x t, look
Lemma has_type_weaken_wf_env :
  forall (x : name) e (t : type), lookup x e = Some t -> 
                                   forall e', lookup x e' = Some t ->
                                                                          (* forall e e' a t,  
                                                                             has_type e a t -> *)
                                     wf_env e' -> 
      (* forall e, env_weaken e e'  *)
                                     wf_env e.
Proof. 
  induction e'; intros. simpl in H0. discriminate. 
  destruct a as [y u]; inversion H1; subst; auto.  apply IHe'; auto. case (eq_name x y); intros; subst; auto. replace (lookup y e' = Some t) with (exists t, lookup y e' = Some t). apply lookup_exists. apply False_rect. apply H6. simpl in H6. red in H6. intuition. auto congruence. contradiction.  using H6. inversion H1. simpl. apply H6. contradict H4. inversion H0. destruct (

contrapose H. case H.
  generalize (H x t).  apply False_rect. apply H.  in H.
*)

Lemma lookup_env_extends:
  forall e2 x p q y e1,
  wf_env (e1 ++ (x, q) :: e2) ->
  lookup y (e1 ++ (x, p) :: e2) = if eq_name y x then Some p else lookup y (e1 ++ (x, q) :: e2).
Proof.
  induction e1; simpl; intros.
  case (eq_name y x); auto.
  destruct a. inversion H. subst x0; subst t0; subst e.
  case (eq_name y n); intro. subst n.
  rewrite eq_name_false. auto. red; intros; subst x. 
  elim H4. unfold dom. rewrite map_append. 
  apply in_or_app. right. simpl. tauto.
  apply IHe1. auto.
Qed.

Lemma has_type_cons_notIn_dom : 
  forall x t1 e a t2,
    has_type ((x, t1) :: e) a t2 -> ~ In x (dom e).
Proof. 
  intros. generalize (has_type_wf_env ((x, t1) :: e) a t2 H); intro H0; inversion H0; auto.
Qed.

(*Lemma has_type_weaken00 :
  forall e1 e2 e3 a t, has_type ( e1 ++ e2) a t ->
                       wf_env (e3 ++ e1++ e2) ->
                       has_type (e3 ++ e1 ++ e2) a t.
Proof. 
  intros e1 e2 e3 a t H. generalize dependent e3. induction H; intros e3 HH; subst. 
  - apply t_var; auto. set (e0 := (e3 ++ e)).  lookup_exists with (x := x) (e:=e0).  (e3 ++ e)).   unfold lookup. red. 
(*  generalize dependent G.
  induction H; intros G Eq Ok; subst.
  Case "typing_var".
    apply typing_var.
      apply Ok.
      apply binds_weaken. apply H0. apply Ok.
  Case "typing_abs".
    pick fresh x and apply typing_abs.
    rewrite <- cons_concat_assoc.
    apply H0.
      auto.
      rewrite cons_concat_assoc. reflexivity.
      rewrite cons_concat_assoc. apply ok_cons.
        apply Ok.
        auto.
  Case "typing_app".
    eapply typing_app.
      eapply IHtyping1. reflexivity. apply Ok.
      eapply IHtyping2. reflexivity. apply Ok.
Qed.*)




Lemma has_type_weaken0 : 
  forall e a t1 t2 x, has_type e a t2 -> wf_env ((x, t1) :: e) 
                                               ->  has_type ((x, t1) :: e) a t2.
Proof.
  intros. induction H0; auto. simpl. intuition. contradiction. discriminate. induction 1; auto; intros; try constructor; auto.  change (lookup x0 ((x, t1) :: e)) with (lookup x0 (nil ++ ((x, t1) :: e))). rewrite lookup_env_extends with (e1:=nil) (q:= t1). assert (x0 <> x). apply has_type_wf_env in H2.
  case (eq_name x0 x); intros; subst; auto. auto. asserthas_type.
*)

Lemma has_type_weaken:
  forall e a t, has_type e a t -> 
                forall e', wf_env e' -> env_weaken e e' -> has_type e' a t.
Proof.
  assert (X: forall e e' x, env_weaken e e' -> ~In x (dom e') -> ~In x (dom e)).
  - intros. generalize (env_weaken_incl_dom _ _ H); auto. 
  - induction 1; simpl; intros; try constructor; auto. 
    + intros. apply H0; auto. 
      * apply notIn_app_1; auto. apply X with e'; auto. 
      * constructor; auto. 
    + econstructor; eauto.       
Qed.

(** The [has_type] predicate is equivariant, i.e. stable by swapping. *)
(*
Lemma has_type_swap:
  forall u v, kind u = kind v ->
  forall e a t, has_type e a t -> 
  has_type (swap_env u v e) (swap_term u v a) (swap_type u v t).
Proof.
  intros u v KINDuv. induction 1; simpl.
  (* var *)
  constructor. apply wf_env_swap; auto. rewrite swap_kind; auto. 
  apply lookup_swap; auto.
  (* fun *)
  constructor. apply wf_type_swap; auto. 
  intros. pose (x' := swap u v x).
  assert (kind x' = TERM).  unfold x'. rewrite swap_kind; auto.
  assert (~In x' (dom e)). 
    generalize (in_dom_swap u v x' e). unfold x'. rewrite swap_inv. tauto.
  generalize (H1 x' H4 H5). rewrite freshen_term_swap. simpl. 
  replace (swap u v x') with x. auto. unfold x'. rewrite swap_inv. auto.
  (* app *)
  simpl in IHhas_type1. econstructor; eauto. 
  (* tfun *)
  constructor. apply wf_type_swap; auto. 
  intros. pose (x' := swap u v x).
  assert (kind x' = TYPE).  unfold x'. rewrite swap_kind; auto.
  assert (~In x' (dom e)). 
    generalize (in_dom_swap u v x' e). unfold x'. rewrite swap_inv. tauto.
  generalize (H1 x' H4 H5). rewrite freshen_tety_swap. 
  rewrite freshen_type_swap. simpl. 
  replace (swap u v x') with x. auto. unfold x'. rewrite swap_inv. auto.
  (* tapp *)
  simpl in IHhas_type. rewrite vsubst_type_swap. 
  econstructor; eauto. apply is_subtype_swap; auto.
  (* sub *)
  econstructor; eauto. apply is_subtype_swap; auto.
Qed.

(** As a consequence of equivariance, we obtain admissible typing
  rules for functions and type abstractions, similar to rules [t_abs]
  and [t_tabs] but where the variable name is quantified existentially
  rather than universally. *)

Lemma kind_fv_type: forall e t, wf_type e t -> forall x, In x (fv_type t) -> kind x = TYPE.
Proof.
  induction 1; simpl; intros.
  replace x0 with x. auto. tauto. 
  tauto.
  elim (in_app_or _ _ _ H1); auto.
  elim (in_app_or _ _ _ H2); intros. auto.
    destruct (fresh_name TYPE (x :: fv_type t2 ++ dom e)) as [y [F K]].
    eapply H1; eauto. apply fv_type_freshen_type. auto. 
Qed.

Lemma fv_wf_type_kind: forall x e t, wf_type e t -> kind x = TERM -> ~In x (fv_type t).
Proof.
  intros; red; intros. generalize (kind_fv_type _ _ H _ H1). congruence.
Qed.
*)

Lemma fresh_freshen_term:
  forall x t e a y,
    wf_term ((x, t) :: e) (freshen_term a x) -> ~In y (dom e) -> x <> y ->
    ~In y (fv_term a).
Proof.
  intros. 
  red; intro.
  assert (In y (dom ((x, t) :: e))). 
  eapply fv_wf_term; eauto. apply fv_term_freshen_term; auto.
  elim H3; simpl; intros; contradiction.
Qed.

(* rename  *)
Fixpoint fun_rename (e: renaming) (x: name) {struct e} : option name := 
  match e with
    | nil => None
    | (y,z) :: e0
      => if eq_name x y then Some z else fun_rename e0 x
  end.

Fixpoint rename_name (e : renaming) (x : name) : name :=
  match e with 
    | nil => x
    | (y, z) :: e0 => if eq_name x y then y else rename_name e0 x
  end. 


Notation " e // x " := (@rename_name e x) (at level 60).

Fixpoint rename_tp (e : renaming) (t : type) : type := 
  match t with
    | Tparam x => Tparam (e // x)
    | Arrow a1 a2 => Arrow (rename_tp e a1) (rename_tp e a2)
  end.


Fixpoint rename (e : renaming) (a : term) : term := 
  match a with
    | Var n    => Var n
    | Param v   => Param (e // v)
    | Fun t a1 => Fun t (rename e a1)
    | App a1 a2 => App (rename e a1)  (rename e a2)
  end.

Fixpoint rename_env (e : renaming) (env : typenv) : typenv :=
  match env with 
      | nil => nil
      | (x, t) :: e0 => ((e // x), (rename_tp e t)) :: (rename_env e e0)
  end.


(* S : Properties of rename  *)
Lemma rename_tp_nil :
  forall (t : type),
    rename_tp nil t = t.
Proof. 
  induction t; simpl; f_equal; auto. 
Qed.

Lemma rename_nil :
  forall (a : term),
    rename nil a = a.
Proof. 
  induction a; simpl; f_equal; auto. 
Qed.

Lemma rename_env_nil :
  forall (env : typenv),
    rename_env nil env = env.
 Proof.
   induction env; simpl; auto; destruct a; rewrite rename_tp_nil, IHenv; auto.  
Qed.

  
Lemma rename_env_weaken :
  forall e e1 e2,
    env_weaken e1 e2 ->
    env_weaken (rename_env e e1) (rename_env e e2).
Proof.
  induction e1; simpl; intros; auto. 
  - red; intros; inversion H0.
  - { - destruct a as [x t]; auto. 

Lemma env_weaken_weaken :
  forall e1 e2 x t,
    env_weaken ((x, t) :: e1) e2 ->
    env_weaken e1 e2.
Proof.
  intros. unfold env_weaken in *; intros. apply H. simpl. 
  destruct (eq_name x0 x); auto. specialize (H x0 t0). rewrite e in *; auto. 
  assert (lookup x ((x, t) :: e1) = Some t). auto. simpl. destruct (eq_name x x); auto. contradict n; auto. rewrite   with (Some t) in H. simpl in H; red in H.  discriminate.  assert (t= t0). 
  discriminate.  H. 
        apply IHe1; auto. 
      
  - inversion H. 



e1, e; simpl; auto; intros.
  - rewrite! rename_env_nil; auto. 
  - red; intros. inversion H0.
  - destruct a as [x t]; subst; auto. 
    rewrite! rename_env_nil, rename_tp_nil; auto. 
  - destruct a as [x t].  destruct p as [y u]; auto. 
    destruct (eq_name x y); subst; auto. 
    + unfold env_weaken in *; intros.
      apply IHe1; auto; intros. 
      * apply H. simpl. rewrite H1. 
      destruct (eq_name x0 y); auto. simpl in IHe1.  assert (t = t1). congruence. 
      simpl in H. 
      set (t1:= (rename_tp ((y, u) :: e) t)).
      (* lookup x
         ((y, t1) :: rename_env ((y, u) :: e) e1) = Some t0 *)
    
unfold env_weaken in *; intros.
    destruct a as [y u].
    
    case  (rename_env ((y, u) :: e) e2). intuition. firstorder. congruence. 


 replace (rename_env ((y, u) :: e) e2) with 
                         (rename_env ((y, u) :: nil) e2).
    simpl. 

unfold rename_env.
    simpl. 

  - red; intros; inversion H0.
  - destruct a as [x t]; subst; auto. 
    generalize (env_weaken_incl_dom ((x, t) :: e1) e2 H); intros.
    induction e; intros; simpl. auto. 
    rewrite! rename_env_nil, rename_tp_nil; auto.
    destruct a as [y u]; subst; auto. 
    destruct (eq_name x y); subst; auto. 
    + red; intros. apply IHe. 
unfold env_weaken in IHe1. unfold env_weaken in *; intros.   
    apply IHe1; auto. 
    intros. apply H. assert (x1 <> x). 
    
congruence. consimpl. rewrite H1; auto. 
    destruct (eq_name x1 x); subst; auto. 
    unfold env_weaken; intros. inversion H0. 
    destruct (eq_name x0 x). subst; auto. 
    + destruct (eq_name x (e // x)). 
      rewrite H2. unfold env_weaken in IHe1. apply IHe1; auto. intros. 
      unfold env_weaken in H. apply H; auto. simpl. 
      destruct (eq_name x0 x). auto. rewrite <- H1.  congruence. subst x; auto.
  
      assert (x0 <> x).  destruct (eq_name x0 x); subst; auto. case (e // x); intros. apply IHe1. apply H; auto.
    simpl.
    destruct (eq_name x0 x); subst; auto. simpl in H. contradict H. . congruence. 
    inversion H0. auto. simpl in H0.  inversion H0. auto.  simpl in H0. inversion H0. auto. tauto. simpl. inversion H.  
tauto. simpl. rewrite! rename_env_nil; auto.
  - destruct a as [x t]. change (rename_env ((x, t) :: e) e1 ) with ((e // x, rename_tp e t) :: rename_env e e1).  unfold rename_env; simpl; auto. case (e0 // x); subst; auto.  env_weaken; intros. unfold env_weaken in H.
    unfold rename_env in H0.
    

inversion H0.
  - destruct a as [x t].
    
    unfold env_weaken; intros.
    inversion H0. 
    destruct (eq_name x0 (e // x)); subst; auto.
    + rewrite H2. unfold env_weaken in H. simpl in H0. apply H.  destruct ( simpl in H0. 



Lemma t_abs': 
  forall e t1 a t2 x,
  kind x = TERM -> ~In x (fv_term a ++ dom e) ->
  has_type ((x, t1) :: e) (freshen_term a x) t2 ->
  has_type e (Fun t1 a) (Arrow t1 t2).
Proof.
  intros;
  generalize (has_type_wf_env _ _ _ H1); intro. inversion H2; subst.
  (* generalize (has_type_wf_type _ _ _ H2); intro. *)
  generalize (has_type_wf_term _ _ _ H1); intro.
  apply t_abs; auto. intros y KIND DOM.
  case (eq_name x y); intro; subst; auto.
  (* assert (kind x = kind y). *)
  (* + congruence. *)
  (*  assert (~In x (fv_type t1)). eapply fv_wf_type_kind; eauto.
  assert (~In x (fv_type t2)). eapply fv_wf_type_kind; eauto. 
  assert (~In y (fv_type t1)). eapply fv_wf_type_kind; eauto.
  assert (~In y (fv_type t2)). eapply fv_wf_type_kind; eauto.*)
  assert (~In y (fv_term a)). apply notIn_app in DOM; destruct DOM as [Fv DOM]; auto.
    
  (* eapply fresh_freshen_term; eauto. *)
  generalize (has_type_swap x y H6 _ _ _ H2). 
  rewrite freshen_term_swap. simpl. rewrite swap_left.
  rewrite (swap_type_not_free x y t1); auto.
  rewrite (swap_type_not_free x y t2); auto.
  rewrite (swap_term_not_free x y a); auto.
  rewrite (swap_env_not_free x y e); auto.
Qed.

Lemma fresh_freshen_tety:
  forall x t1 e a y,
  wf_term ((x, t1) :: e) (freshen_tety a x) -> ~In y (dom e) -> x <> y ->
  ~In y (fv_term a).
Proof.
  intros. 
  red; intro.
  assert (In y (dom ((x, t1) :: e))).
    eapply fv_wf_term. eauto. apply fv_term_freshen_tety. auto.
  elim H3; simpl; intros. contradiction. contradiction.
Qed.

Lemma t_tabs': 
  forall e t1 a t2 x,
  kind x = TYPE -> ~In x (dom e) -> ~In x (fv_term a) -> ~In x (fv_type t2) ->
  has_type ((x, t1) :: e) (freshen_tety a x) (freshen_type t2 x) ->
  has_type e (TFun t1 a) (Forall t1 t2).
Proof.
  intros. generalize (has_type_wf_env _ _ _ H3); intro. inversion H4; subst.
  generalize (has_type_wf_type _ _ _ H3); intro.
  generalize (has_type_wf_term _ _ _ H3); intro.
  apply t_tabs. auto. intros y KIND DOM.
  case (eq_name x y); intro. subst x; auto.
  assert (kind x = kind y). congruence.
  assert (~In x (fv_type t1)). generalize (fv_wf_type x _ _ H10); tauto. 
  assert (~In y (fv_type t1)). generalize (fv_wf_type y _ _ H10); tauto.
  assert (~In y (fv_type t2)). eapply fresh_freshen_type; eauto.
  assert (~In y (fv_term a)).  eapply fresh_freshen_tety; eauto.
  generalize (has_type_swap x y H7 _ _ _ H3). 
  rewrite freshen_type_swap. rewrite freshen_tety_swap. 
  simpl. rewrite swap_left.
  rewrite (swap_type_not_free x y t1); auto.
  rewrite (swap_type_not_free x y t2); auto.
  rewrite (swap_term_not_free x y a); auto.
  rewrite (swap_env_not_free x y e); auto.
Qed.
*)
(*S
(** * Stability of the typing judgement under substitutions *)

(** We now show that the typing judgement is stable under
  substitutions.  There are two substitutions to consider: of a type
  for a type variable, and of a term for a term variable. *)

Lemma has_type_stable_type_subst:
  forall e1 x p q e2 a t,
  kind x = TYPE ->
  is_subtype e1 p q ->
  has_type (e2 ++ (x, q) :: e1) a t ->
  has_type (psubst_env e2 x p ++ e1) (psubst_tety a x p) (psubst_type t x p).
Proof.
  assert (forall e1 x p q, kind x = TYPE -> is_subtype e1 p q ->
          forall e a t, has_type e a t ->
          forall e2, e = e2 ++ (x, q) :: e1 ->
          has_type (psubst_env e2 x p ++ e1) (psubst_tety a x p) (psubst_type t x p)).
  induction 3; intros; simpl; subst e.
  (* var *)
  elim (lookup_env_concat _ _ _ p _ _ _ H1 H3); intros [A B].
  congruence.
  constructor; auto.
  eapply wf_env_psubst; eauto.
  (* fun *)
  destruct (fresh_name TERM (x :: dom (e2 ++ (x, q) :: e1) ++
                             dom (psubst_env e2 x p ++ e1) ++
                             fv_type (psubst_type t2 x p) ++
                             fv_term (psubst_tety a x p)))
  as [y [F K]].
  apply t_abs' with y; eauto. 
  change ((y, psubst_type t1 x p) :: psubst_env e2 x p ++ e1)
    with (psubst_env ((y, t1) :: e2) x p ++ e1).
  rewrite (psubst_freshen_tetety e1). apply H3; eauto. 
  eauto. eauto.
  (* app *)
  simpl in IHhas_type1. econstructor; eauto.
  (* tfun *)  
  destruct (fresh_name TYPE (x :: dom (e2 ++ (x, q) :: e1) ++
                             dom (psubst_env e2 x p ++ e1) ++
                             fv_type (psubst_type t2 x p) ++
                             fv_term (psubst_tety a x p)))
  as [y [F K]].
  apply t_tabs' with y; eauto. 
  change ((y, psubst_type t1 x p) :: psubst_env e2 x p ++ e1)
    with (psubst_env ((y, t1) :: e2) x p ++ e1).
  rewrite (psubst_freshen_tety e1). 
  rewrite (psubst_freshen_type e1).
  apply H3; eauto. eauto. eauto. eauto. eauto.
  (* tapp *)
  rewrite <- (psubst_vsubst_type e1). simpl in IHhas_type.
  econstructor; eauto.
  eapply sub_stable_subst; eauto. eauto.
  (* sub *)
  econstructor; eauto. eapply sub_stable_subst; eauto.

  eauto.
Qed.
S*)



Lemma lookup_env_append:
  forall e2 x p y e1,
  wf_env (e1 ++ (x, p) :: e2) -> 
  lookup y (e1 ++ (x, p) :: e2) = if eq_name y x then Some p else lookup y (e1 ++ e2).
Proof.
  induction e1; simpl; intros.
  auto.
  destruct a. inversion H; subst.
  case (eq_name y n); intro. 
  rewrite eq_name_false. auto. subst n. 
  rewrite dom_append in H4. simpl in H4. eauto. 
  auto.
Qed.

Lemma wf_env_append:
  forall e2 x p e1, wf_env (e1 ++ (x, p) :: e2) -> kind x = TERM -> wf_env (e1 ++ e2).
Proof.
  induction e1; simpl; intros.
  inversion H; auto.
  inversion H; subst. 
  constructor. auto.
  rewrite dom_append. rewrite dom_append in H4. simpl in H4.
  red; intro. elim H4. apply in_or_app. simpl. elim (in_app_or _ _ _ H1); auto.
(*  apply wf_type_strengthen with (e1 ++ (x, p) :: e2). auto.
  intros. rewrite dom_append in H2. simpl in H2. rewrite dom_append.
  apply in_or_app. elim (in_app_or _ _ _ H2); intro. auto. 
  elim H6; intro. congruence. auto.*)
Qed.

(*
Lemma is_subtype_strengthen:
  forall e s t, is_subtype e s t ->
  forall e', wf_env e' -> (forall x : name, kind x = TYPE -> lookup x e' = lookup x e) ->
  is_subtype e' s t.
Proof.
  assert (forall e e',
           (forall x : name, kind x = TYPE -> lookup x e' = lookup x e) ->
           (forall x : name, kind x = TYPE -> In x (dom e) -> In x (dom e'))).
    intros. destruct (lookup_exists _ _ H1) as [t L]. 
    apply lookup_inv with t. rewrite H; auto.
  induction 1; intros.
  (* top *)
  constructor; auto. apply wf_type_strengthen with e; eauto.
  (* refl *)
  econstructor; eauto. rewrite H4; eauto.
  (* trans *)
  econstructor; eauto. rewrite H4; auto.
  (* arrow *)
  constructor; auto.
  (* forall *)
  destruct (fresh_name TYPE (dom e ++ dom e' ++ fv_type s2 ++ fv_type t2)) as [x [F K]].
  apply sa_all' with x; eauto. 
  apply H2; eauto. constructor; eauto. 
  intros x0 K0. simpl. case (eq_name x0 x); auto.
Qed.
*)

Lemma has_type_stable_term_subst:
  forall e1 x b s e2 a t,
  kind x = TERM -> has_type e1 b s -> has_type (e2 ++ (x, s) :: e1) a t ->
  has_type (e2 ++ e1) (subst_term a ((x, b):: nil) nil) t.
Proof.
  - { assert (forall e1 x b s, kind x = TERM -> has_type e1 b s ->
          forall e a t, has_type e a t ->
          forall e2, e = e2 ++ (x, s) :: e1 ->
          has_type (e2 ++ e1) (subst_term a ((x, b)::nil) nil) t).
  induction 3; intros; simpl; subst e.
      - (* var *)
        rewrite lookup_env_append in H3; auto. 
        assert (wf_env (e2 ++ e1)); 
        [ eapply wf_env_append; eauto
        | destruct (eq_name x0 x)]; 
          [ replace t with s;
            [eapply has_type_weaken; eauto;
             apply env_concat_weaken; auto
            | congruence]  
        | constructor; auto].
      - (* fun *)
        destruct (fresh_name TERM (x :: dom (e2 ++ (x, s) :: e1) ++
                             dom (e2 ++ e1) ++
                             fv_type t1 ++
                             fv_term (subst_term a ((x, b):: nil) nil)))
          as [y [F K]].  (* apply t_abs_ generalize (t_abs (e2 ++ e1) t1 (subst_term a ((x, b) :: nil) nil) t2); intros. simpl in  H3.  y K F).  H3. HH.  with y; intros.  *)
        constructor; intros. 
        change ((x0, t1) :: e2 ++ e1) with (((x0, t1) :: e2) ++ e1).
        rewrite subst_psubst; auto. rewrite psubst_freshen_term; eauto. 
        rewrite <- subst_psubst.
        eapply H2; eauto. apply notIn_app in H4; destruct H4 as [H4l H4r].
        apply notIn_app_1; auto. intro FF; apply H4l. rewrite subst_psubst. simpl in H4r. with (e0; auto. apply H1; eauto. eauto. eauto. 
  rewrite (psubst_freshen_term). apply H3; eauto. eauto. eauto. 
  (* app *)
  simpl in IHhas_type1. econstructor; eauto.
  (* tfun *)  
  destruct (fresh_name TYPE (x :: dom (e2 ++ (x, s) :: e1) ++
                             dom (e2 ++ e1) ++
                             fv_type t2 ++
                             fv_term (psubst_term a x b)))
  as [y [F K]].
  apply t_tabs' with y; eauto. 
  change ((y, t1) :: e2 ++ e1)
    with (((y, t1) :: e2) ++ e1).
  rewrite (psubst_freshen_tetyte e1). 
  apply H3; eauto. eauto. eauto.
  (* tapp *)
  simpl in IHhas_type.
  econstructor; eauto.
  eapply is_subtype_strengthen. eauto. 
  eapply wf_env_append; eauto. 
  intros. rewrite lookup_env_append. rewrite eq_name_false. auto.
  congruence.
  eauto.
  (* sub *)
  econstructor; eauto. 
  eapply is_subtype_strengthen. eauto. 
  eapply wf_env_append; eauto.
  intros. rewrite lookup_env_append. rewrite eq_name_false. auto.
  congruence. eauto.

  eauto.
Qed.
*)

(** * Dynamic semantics *)

(** The dynamic semantics of $F_{<:}$ is specified by a one-step reduction relation,
  in small-step operational style.  We first define values (final results of reduction
  sequences) as a subset of terms. *)

(* value-eval for Abs-term : value-ABS *)

Inductive isvalue: term -> Prop :=
  | isvalue_fun: forall t a,
      isvalue (Fun t a).

(* value-eval for variable term env *)

Inductive v_isvalue : v_termenv -> Prop :=
| v_Nil : v_isvalue nil
| v_Cons : forall ev t n, v_isvalue ev -> isvalue t -> v_isvalue ((n, t) :: ev).

(** We first give a Plotkin-style specification of the reduction
  relation: it uses inductive rules [red_appfun], [red_apparg],
  [red_tapp] instead of contexts to describe reductions inside
  applications.  The two rules [red_appabs] and [red_tapptabs] are the
  familiar beta-reduction rules for term and type applications,
  respectively. *)

(* call-by-value evaluation : reduction  *)

Inductive red: term -> term -> Prop :=
  | red_appabs: forall t a ep v, (* red-beta  *)
      isvalue v ->
      red (App (Fun t a) v) (subst_term a ep ((0,v)::nil))
  | red_appfun: forall a a' b,  (* red-app-1 *)
      red a a' -> red (App a b) (App a' b)
  | red_apparg: forall v b b',  (* red-app-2 *)
      isvalue v -> red b b' -> red (App v b) (App v b').

(** We now give an alternate specification of the reduction relation
  in the style of Wright and Felleisen.  The [red_top] relation
  captures beta-reductions at the top of a term.  Reductions within
  terms are expressed using reduction contexts (see the [red_context]
  relation).  Contexts are represented as functions from terms to
  terms whose shape is constrained by the [is_context] predicate. *)

(*
Inductive red_top: term -> term -> Prop :=
  | red_top_appabs: forall t a v,
      isvalue v ->
      red_top (App (Fun t a) v) (vsubst_term a 0 v)
  | red_top_tapptabs: forall t a t',
      red_top (TApp (TFun t a) t') (vsubst_tety a 0 t').

Inductive is_context: (term -> term) -> Prop :=
  | iscontext_hole:
      is_context (fun a => a)
  | iscontext_app_left: forall c b,
      is_context c -> is_context (fun x => App (c x) b)
  | iscontext_app_right: forall v c,
      isvalue v -> is_context c -> is_context (fun x => App v (c x))
  | iscontext_tapp: forall c t,
      is_context c -> is_context (fun x => TApp (c x) t).

Inductive red_context: term -> term -> Prop :=
  | red_context_intro: forall a a' c,
      red_top a a' -> is_context c -> red_context (c a) (c a').
*)

(** The Plotkin-style relation is more convenient for doing formal
  proofs.  Since the challenge is given in terms of contexts,
  we feel obliged to prove the equivalence between the two formulations
  of reduction.  The proofs are routine inductions over
  the derivations of [red] and [is_context], respectively. *)
(*S
Lemma red_red_context: forall a a', red a a' -> red_context a a'.
Proof.
  induction 1; intros.
  change (App (Fun t a) v) with ((fun x => x) (App (Fun t a) v)).
  change (vsubst_term a 0 v) with ((fun x => x) (vsubst_term a 0 v)).
  constructor. constructor. auto. constructor.
  change (TApp (TFun t a) t') with ((fun x => x) (TApp (TFun t a) t')).
  change (vsubst_tety a 0 t') with ((fun x => x) (vsubst_tety a 0 t')).
  constructor. constructor. constructor.
  inversion IHred; subst. 
  change (App (c a0) b) with ((fun x => App (c x) b) a0).
  change (App (c a'0) b) with ((fun x => App (c x) b) a'0).
  constructor. auto. constructor. auto.
  inversion IHred; subst. 
  change (App v (c a)) with ((fun x => App v (c x)) a).
  change (App v (c a')) with ((fun x => App v (c x)) a').
  constructor. auto. constructor. auto. auto.
  inversion IHred; subst. 
  change (TApp (c a0) t) with ((fun x => TApp (c x) t) a0).
  change (TApp (c a'0) t) with ((fun x => TApp (c x) t) a'0).
  constructor. auto. constructor. auto. 
Qed.

Lemma red_context_red: forall a a', red_context a a' -> red a a'.
Proof.
  assert (forall c, is_context c ->
          forall a a', red_top a a' -> red (c a) (c a')).
  induction 1; intros.
  inversion H; constructor; auto.
  apply red_appfun; auto.
  apply red_apparg; auto.
  apply red_tapp; auto.

  intros. inversion H0. auto.
Qed.
S*)

(** * Type soundness proof *)

(** Type soundness for $F_{<:}$ is established by proving the standard properties of
  type preservation (also called subject reduction) and progress. *)

(** ** Preservation *)

(** Technical inversion lemmas on typing derivations. These lemmas are 
  similar (but not fully identical) to lemma A.13 in the on-paper proof. *)
(*S
Lemma has_type_fun_inv:
  forall e a t, has_type e a t ->
  forall b s1 u1 u2, a = Fun s1 b -> is_subtype e t (Arrow u1 u2) ->
  is_subtype e u1 s1 /\ 
  exists s2, 
    is_subtype e s2 u2 /\
    (forall x, kind x = TERM -> ~In x (dom e) -> has_type ((x, s1) :: e) (freshen_term b x) s2).
Proof.
  induction 1; intros; try discriminate. 
  injection H2; intros; clear H2; subst s1; subst b.
  inversion H3; subst. split. auto. 
  exists t2; split; assumption.
  eapply IHhas_type; eauto. eapply sub_trans; eauto.
Qed.

Lemma has_type_tfun_inv:
  forall e a t, has_type e a t ->
  forall b s1 u1 u2, a = TFun s1 b -> is_subtype e t (Forall u1 u2) ->
  is_subtype e u1 s1 /\ 
  exists s2, 
    (forall x, kind x = TYPE -> ~In x (dom e) ->
        is_subtype ((x, u1) :: e) (freshen_type s2 x) (freshen_type u2 x)) /\
    (forall x, kind x = TYPE -> ~In x (dom e) ->
        has_type ((x, s1) :: e) (freshen_tety b x) (freshen_type s2 x)).
Proof.
  induction 1; intros; try discriminate. 
  injection H2; intros; clear H2; subst s1 b.
  inversion H3; subst. split. auto. 
  exists t2; split. assumption. assumption.
  eapply IHhas_type; eauto. eapply sub_trans; eauto.
Qed.
S*)

(** The preservation theorem states that if term [a] reduces to [a'], then
  all typings valid for [a] are also valid for [a'].  It is
  proved by an outer induction on the reduction and an inner induction
  on the typing derivation (to get rid of subtyping steps). *)


Theorem preservation: forall e a a' t, red a a' -> has_type e a t -> has_type e a' t.
Proof. 
  assert (forall a a', red a a' ->
          forall e a0 t, has_type e a0 t -> forall (EQ: a = a0), 
          has_type e a' t).
  induction 1; induction 1; intros; simplify_eq EQ; clear EQ; intros; subst.
  (** Case app abs *)
  - (*assert (is_subtype e (Arrow t1 t2) (Arrow t1 t2)). apply sub_refl; eauto.
  destruct (has_type_fun_inv _ _ _ H0_ _ _ _ _ (refl_equal _) H0)
  as [A [s2 [B C]]].
  apply t_sub with s2; auto.*)
  destruct (fresh_name TERM (dom e ++ fv_term a)) as [x [F K]].
  
  rewrite (vsubst_psubst_freshen_term x); eauto.
  change e with (nil ++ e). 
  apply has_type_stable_term_subst with t; auto.
  apply t_sub with t1; auto.
  simpl; eauto.
  (** Case tapp tabs *)
  assert (is_subtype e (Forall t1 t2) (Forall t1 t2)). apply sub_refl; eauto.
  destruct (has_type_tfun_inv _ _ _ H _ _ _ _ (refl_equal _) H1)
  as [A [s2 [B C]]].
  destruct (fresh_name TYPE (dom e ++ fv_term a ++ fv_type t2)) as [x [F K]].
  rewrite (vsubst_psubst_freshen_tety x); eauto. 
  rewrite (vsubst_psubst_freshen_type x); eauto. 
  apply t_sub with (psubst_type (freshen_type s2 x) x t0).
  change e with (psubst_env nil x t0 ++ e).
  apply has_type_stable_type_subst with t; eauto. 
  apply sub_trans with t1; auto.
  simpl; auto. 
  change e with (psubst_env nil x t0 ++ e).
  apply sub_stable_subst with t1; eauto. simpl; auto.
  (** Case context left app *)
  apply t_app with t1; eauto.
  (** Case context right app *)
  apply t_app with t1; eauto.
  (** Case context left tapp *)
  apply t_tapp with t1; eauto. 
  (** Final conclusion *)
  eauto.
Qed.

(** ** Progress *)

(** The following lemma, which corresponds to lemma A.14 in the challenge statement,
  determines the shape of a value from its type.  Namely, closed values of function
  types are function abstractions, and closed values of polymorphic types are 
  type abstractions. *)

Lemma canonical_forms:
  forall e a t, has_type e a t -> e = nil -> isvalue a ->
  match t with 
  | Arrow t1 t2 => exists s, exists b, a = Fun s b
  | Forall t1 t2 => exists s, exists b, a = TFun s b
  | Top => True
  | _ => False
  end.
Proof.
  induction 1; intros; subst e.
  inversion H3.
  exists t1; exists a; auto.
  inversion H2.
  exists t1; exists a; auto.
  inversion H2.
  generalize (IHhas_type (refl_equal _) H2). 
  inversion H0; auto.
  simpl in H3; discriminate.
Qed.

(** The progress theorem shows that a term well-typed in the empty environment
  is never ``stuck'': either it is a value, or it can reduce.
  The theorem is proved by a simple induction on the typing derivation for the term
  and a case analysis on whether the subterms of the term are values
  or can reduce further. *)

Theorem progress: forall a t, has_type nil a t -> isvalue a \/ exists a', red a a'.
Proof. 
  assert (forall e a t, has_type e a t -> e = nil -> isvalue a \/ exists a', red a a').
  induction 1; intros; subst e.
  (** Free variable: impossible in the empty typing environment. *)
  simpl in H1. discriminate.
  (** Function: already a value. *)
  left; constructor.
  (** Application [App a b]. *)
  right.
  destruct (IHhas_type1 (refl_equal _)) as [Va | [a' Ra]].
  destruct (IHhas_type2 (refl_equal _)) as [Vb | [b' Rb]].
    (** [a] and [b] are values.  [a] must be a [Fun].  
        Beta-reduction is possible. *)
    generalize (canonical_forms _ _ _ H (refl_equal _) Va).
    intros [s [c EQ]]. subst a. 
    exists (vsubst_term c 0 b). constructor. auto.
    (** [a] is a value, but [b] reduces. [App a b] therefore reduces. *)
    exists (App a b'). constructor; auto.
    (** [a] reduces. [App a b] reduces as well. *)
    exists (App a' b). constructor; auto.
  (** Type abstraction: already a value. *)
  left; constructor.
  (** Type application [TApp a t]. *)
  right. destruct (IHhas_type (refl_equal _)) as [Va | [a' Ra]].
    (** [a] is a value. [a] must be a [TFun].  Beta-reduction is possible. *)
    generalize (canonical_forms _ _ _ H (refl_equal _) Va).
    intros [s [b EQ]]. subst a. 
    exists (vsubst_tety b 0 t). constructor. 
    (** [a] reduces, and so does [TApp a t]. *)
    exists (TApp a' t). constructor; auto.
  (** Subtyping step. *)
  auto.
  (** Final conclusion. *)
  eauto.
Qed.


