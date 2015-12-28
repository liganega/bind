(** * Completeness of [LJT] w.r.t. Kripke Semantics *)

Set Implicit Arguments.

Require Import associations.
Require Import associations_extra.
Require Import sublist.
Require Import language_syntax.
Require Import variable_sets.
Require Import substitution_wellformedness.
Require Import fresh_name.
Require Import renaming.
Require Import soundness.


(** The completeness of [LJT] w.r.t. Kripke semantics follows
   from the Universal Completeness.

   The universal Kripke model consists of contexts as worlds,
   the sub-context relation, and the provability for atomic
   sentences, and term as the constant domain. *)


(** ** The Universal Model *)

(* projections related with well-formedness  *)

Notation wf_trm := (@sig trm wf_t).

Definition wf_Cst (n:name) : wf_trm := 
  exist wf_t (Cst n)(wCst n).

Definition wf_Par (n:name) : wf_trm := 
  exist wf_t (Par n)(wPar n).

Definition wf_App (f:function)(t u: wf_trm) : wf_trm :=
  exist wf_t
        (App f (proj1_sig t) (proj1_sig u)) 
        (wApp f (proj2_sig t) (proj2_sig u)).

Definition wf_atoms Ga (P : predicate * wf_trm) := 
  (Ga |- Atom (fst P, proj1_sig (snd P))).

(** Monotonicity of forcing relation *)

Lemma weakening_gen' : forall Ga De A eta,
    sub_ctx Ga De ->
    Ga |- A ->
    rename_c eta De |- rename eta A
                                
with weakening_stoup_gen' : forall Ga De A C eta,
    sub_ctx Ga De ->
    Ga ;; A |- C ->
    rename_c eta De ;; rename eta A |- rename eta C.
Proof.
 - intros; apply weakening_gen with Ga; auto. 
   + apply indeed_sub_ctx_is; assumption. 
   + destruct H as [Heq | Hsub Hwf];
     [ rewrite <- Heq; apply (@wf_prove Ga A H0); auto 
     | apply Hsub].

 - intros; apply weakening_stoup_gen with Ga; auto.
   + apply indeed_sub_ctx_is; assumption.
   + destruct H as [Heq | Hsub Hwf];
     [ rewrite <- Heq; apply (@wf_prove_stoup Ga A C H0); auto
     | apply Hsub].
Defined.     

Lemma weakening_atom : forall (Ga Ga': context),
    sub_ctx Ga Ga' ->
    forall (P : predicate * wf_trm),
    wf_atoms Ga P ->
    wf_atoms Ga' P.
Proof. 
  intros; apply weakening with Ga; 
  [ apply indeed_sub_ctx_is
  | destruct H as [Heq | Hsub ?];
    [ rewrite <- Heq; unfold wf_atoms in H0;
      apply (@wf_prove Ga (Atom (fst P, proj1_sig (snd P))))
     |apply Hsub]
    | ]; auto.
Defined.

(** Reflexivity of sub-context relation. *)

Lemma sub_ctx_refl : forall Ga, sub_ctx Ga Ga.
Proof.
  unfold sub_ctx; intuition. 
Qed.

(** Transitivity of sub-context relation. *)

Lemma sub_ctx_trans : forall Ga Ga0 Ga1, 
  sub_ctx Ga Ga0 -> sub_ctx Ga0 Ga1 -> sub_ctx Ga Ga1.
Proof.
  unfold sub_ctx; intros Ga Ga0 Ga1 H H0.
  destruct H as [Heq | Hneq]; destruct H0 as [H0eq | H0neq]; 
  subst; intuition. 
Qed.

(** Universal model's domain is the set of well-formed terms. *)

Canonical Structure Universal := @Build_Kripke
  context
  sub_ctx
  sub_ctx_refl
  sub_ctx_trans
  wf_trm
  (wf_Cst)
  (wf_App)
  (fun Ga Pt => Ga |- Atom (fst Pt, proj1_sig (snd Pt)))
  weakening_atom.

(** In the universal model, substitution plays the role of
   semantic interpretation. *)

Lemma sub_ctx_wf_c : forall Ga Ga0,
    sub_ctx Ga Ga0 -> wf_c Ga -> wf_c Ga0.
Proof.
  intros; unfold sub_ctx in H. 
  destruct H as [Heq | Hneq]; subst; intuition. 
Defined.

Notation ">>" := (proj1_sig).
Notation "<<" := (exist wf_t).


Fixpoint fn_pro (eta : assoc wf_trm) :=
  match eta with
    nil => nil
  | (n, t) :: eta' => (n, >> t) :: (fn_pro eta')
  end.

Notation ">>>" := (fn_pro).

(* fun_assoc is preserved under fn_pro *)

Lemma fn_pro_eq_val : forall eta n t u,
eta ^^ n = Some t ->
(>>> eta) ^^ n = Some u ->
>> t = u.
Proof.
  unfold fn_pro; induction eta, t; auto; simpl; intros; auto. 
  - inversion H; auto.
  - destruct a as [m t]; simpl in H0. 
    case_var. 
    + inversion H0; inversion H; simpl; auto. 
    + set (x0 := (<< x w)); assert (x= >> x0) as H1; auto; 
      rewrite H1; apply IHeta with n; auto. 
Defined.

Lemma fn_pro_dom_eq : forall eta,
  dom eta = dom (>>> eta).
Proof.
  induction eta as [ | nw eta0]; auto; 
  destruct nw as [n w]; simpl; rewrite IHeta0; auto.
Defined.

Lemma wf_t_sub_ol : forall t rho eta,
    sub_name (ol_t t) (dom eta) -> 
    wf_t (t [[>>> rho, >>> eta]]).
Proof.
  induction t; auto; simpl; intros. 
  - apply IN_sublist in H. generalize H; intro H1. 
    rewrite fn_pro_dom_eq in H. 
    apply IN_dom_sig in H; apply IN_dom_sig in H1.
    destruct H as [ u H ]; destruct H1 as [ wt H1]; destruct wt as [t H2]. 
    rewrite H; auto. 
    rewrite <- fn_pro_eq_val with (eta := eta) (n:=n) (t:=(<< t H2)); auto. 
  - destruct (decIN eqdec n (dom (>>> rho))) as [H1 | H1]. 
    + generalize H1; intro H2;
       rewrite <- fn_pro_dom_eq in H2. 
      apply IN_dom_sig in H1; apply IN_dom_sig in H2.
      destruct H1 as [ u H1 ]; destruct H2 as [ wt H2]; destruct wt as [t H3].
      rewrite H1; auto;
      rewrite <- fn_pro_eq_val with (eta := rho) (n:=n) (t:=(<< t H3)); auto.
    + generalize (notIN_dom_None n (>>> rho) H1); 
      intro H2; rewrite H2; apply wPar.
  - apply wCst.
  - apply wApp; [apply IHt1 | apply IHt2]; auto with datatypes.
Defined. 

Lemma fn_pro_nil : 
  >>> nil = nil.
Proof.
  auto.
Defined.


Lemma fn_pro_rm_comm : forall eta n,
  ((>>> eta) ^- n) = (>>> (eta ^- n)).
Proof.
  induction eta as [| a eta]; auto; simpl; intros;
  destruct a as (m, wft); destruct wft as (t, wf); auto. 
  simpl; case_var; rewrite IHeta; auto. 
Defined.


Lemma psem_tsubst : forall (t:trm) (rho eta:assoc wf_trm),
  sub_name (ol_t t) (dom eta) -> sub_name (op_t t) (dom rho) -> 
  >> (psem Universal t rho eta) = (t [[>>> rho , >>> eta]]).
Proof.
  induction t; try tauto; intros.  
  - simpl in *. apply IN_sublist in H. 
    generalize H; intro H1; rewrite fn_pro_dom_eq in H1.
    
    destruct (IN_dom_sig n  eta H) as [wft H2];  
    destruct (IN_dom_sig n (>>> eta) H1) as [wfu H3]. 
    rewrite H2, H3; auto. apply fn_pro_eq_val with (eta:=eta) (n:=n); auto. 
  - simpl in *. apply IN_sublist in H0. 
    generalize H0; intro H1; rewrite fn_pro_dom_eq in H1.
    destruct (IN_dom_sig n rho H0) as [wft H2];
    destruct (IN_dom_sig n (>>> rho) H1) as [wfu H3]. 
    rewrite H2, H3; auto. apply fn_pro_eq_val with (eta:=rho) (n:=n); auto. 
  - simpl in *; f_equal; auto; [apply IHt1| apply IHt2]; auto with datatypes. 
Defined.


Lemma open_eq_subst_t : forall t n u,
    wf_t t ->
    (t [[nil, (n, u) :: nil]]) = t.
Proof.
  induction t; simpl; intros; auto; try inversion H; try f_equal; auto.
Defined.

Lemma open_eq_subst_t_rm : forall t eta a n,
    ((t [[nil, >>>eta ^- n]]) [[nil, (n, Par a) :: nil]]) = (t [[nil, (n, Par a) ::(>>> eta)]]).
Proof.
  induction t; simpl; intros; auto.
  - case_var.
    + rewrite assoc_rm_self; simpl; case_var; try tauto; auto.
    + rewrite <- assoc_rm_neq; auto.
      induction eta; simpl.
      * case_var; tauto. 
      * destruct a0 as [n2 t]; destruct t; simpl; case_var; auto.
        rewrite open_eq_subst_t; auto. 
  - f_equal; auto. 
Defined.

Hint Resolve open_eq_subst_t.
Hint Rewrite open_eq_subst_t.


Lemma fn_pro_cons : forall n a eta,
    (>>>((n, wf_Par a) :: eta)) = ((n, Par a) :: >>> eta).
Proof.
  auto.
Defined.

Lemma fn_pro_IN_dom : forall eta n u,
    >>> eta ^^ n = Some u ->
    wf_t u.
Proof.
  induction eta; simpl; intros; try discriminate.
  destruct a; destruct s; simpl in *.
  case_var.
  - inversion H.
    rewrite <- H1; auto.
  - eapply IHeta; eauto.
Defined.

(*------------ subst rel w/ wft associations ------------------*)

Lemma fn_pro_wf_t_sig : 
  forall u,
    wf_t u -> 
    (exists c, (u = Cst c) \/ (u = Par c))
    \/ (exists f u1 u2, ((u = App f u1 u2) /\ (wf_t u1) /\ (wf_t u2))).
Proof. 
  induction 1; auto; intros; [ left | left | right]; try exists x; auto. 
  destruct IHwf_t1, IHwf_t2; eauto; do 2 destruct H1, H2; 
  try do 2 destruct H1, H2; try destruct H3; try exists f, t1, t2; subst; auto.
Defined.

Lemma open_wf_trm_subst_t : 
  forall u (eta: assoc wf_trm) n t, 
    open_t (u [[nil , >>> eta ^- n]]) n t 
    = (u [[ nil , (n, t) :: >>> eta]]).
Proof.
  unfold open_t; induction u as [ m | m | m | ]; simpl; intros; auto.
  - case_var.
    + rewrite assoc_rm_self; simpl; case_var; intuition.
    + rewrite <- assoc_rm_neq; auto.
      pose proof (fn_pro_IN_dom eta m) as H;
      pose proof fn_pro_wf_t_sig as H0. 
      destruct (>>> eta ^^ m). 
      * specialize H with t0; specialize H0 with t0; destruct H0; 
         try apply H; auto.
      * simpl; case_var; auto; try contradict H; intuition.
  -  f_equal; auto.
Defined.

Lemma open_wf_trm_subst :
  forall A eta n t, 
    open (A [nil,  >>> eta ^- n]) n t = ( A [nil , (n, t) :: >>> eta]).
Proof.
  unfold open; induction A as [ [P u]| | m ]; simpl; intros.
  - do 2 f_equal.  
    apply open_wf_trm_subst_t; auto. 
  - f_equal; auto.
  - f_equal; case_var. 
    * rewrite <- nil_subst; rewrite <- rm_rm; auto. 
    * rewrite rm_neq_rm; auto; rewrite fn_pro_rm_comm; auto. 
Defined.

Lemma ol_t_ind_rho :
  forall t (rho eta : assoc wf_trm),
    ol_t (t [[ >>> rho, >>> eta]]) = ol_t (t [[>>> nil, >>> eta]]).
Proof.
  induction t, rho; auto; intros.
  - destruct p as [m w]; destruct w as [t wt]; simpl. 
    case_var; auto; pose proof (fn_pro_IN_dom rho n);
    case_assoc; auto. 
  - destruct p as [n w].   
    case w; intros; unfold subst; simpl;
    rewrite IHt1 with (rho := ((n, << x w0) :: rho)); 
    rewrite IHt2 with (rho := ((n, << x w0) :: rho)). 
    rewrite fn_pro_nil; auto. 
Defined. 

Lemma ol_ind_rho :
  forall A (rho eta : assoc wf_trm),
    ol (A [ >>> rho, >>> eta]) = ol (A [>>> nil, >>> eta]).
Proof.
  induction A as [ [p  t] | | ]; induction rho as [ | [ m w ] rho ]; auto; intros
  ; simpl; 
    replace ((m, >> w) :: >>> rho) with (>>> ((m , w ) :: rho)); auto. 
  - rewrite ol_t_ind_rho; auto using fn_pro_nil. 
  - rewrite IHA1, IHA2; auto using fn_pro_nil.
  - rewrite fn_pro_rm_comm; 
    rewrite IHA with (eta:= eta ^-n); auto using fn_pro_nil.
Defined. 

Lemma open_eq_subst_wf_t : forall t u eta rho n,
    wf_t u ->
    ((t [[>>>rho, >>>eta ^- n]]) [[>>> nil, (n, u) :: nil]]) 
    = (t [[>>>rho, (n, u) ::(>>> eta)]]).
Proof.
  induction t; auto; intros. 
  - rewrite <- fn_pro_nil; simpl; case_var. 
    + rewrite assoc_rm_self; simpl; case_var; intuition. 
    + rewrite <- assoc_rm_neq; auto. 

       destruct (decIN eqdec n (dom (>>> eta))) as [H1 | H1]. 
      * generalize H1; intro H2. rewrite <- fn_pro_dom_eq in H2.
        apply IN_dom_sig in H1; destruct H1 as [t St]; 
        apply IN_dom_sig in H2; destruct H2 as [tt Stt];
        rewrite St.
        assert (H0 := fn_pro_eq_val eta n Stt St). 
        destruct tt as [tt wt]; simpl in H0; subst. 
        case wt; intros; auto; simpl.  
        rewrite! open_eq_subst_t; auto. 
      * pose proof (notIN_dom_None n (>>> eta) H1) as H0;
        rewrite H0; simpl. case_var; intuition.
  - rewrite! open_eq_subst_t; auto. 
    apply empty_ol_wf_t; rewrite fn_pro_rm_comm, ol_t_ind_rho; auto. 
  -  simpl; rewrite IHt1, IHt2; auto. 
Defined.
 
Lemma open_eq_subst : forall A eta rho t n,
    wf_t t ->
    ((A [>>>rho, >>>eta ^- n]) [>>> nil, (n, t) :: nil]) 
    = (A [>>>rho, (n, t) ::(>>> eta)]).
Proof. 
  induction A as [ [p t] | |]; auto; intros; simpl. 
  - do 2 f_equal; apply open_eq_subst_wf_t; auto.
  - rewrite IHA1, IHA2; auto. 
  - f_equal. case_var; auto.  
    + rewrite <- rm_rm, nil_subst; auto. 
    + rewrite <- rm_neq_rm; auto; rewrite fn_pro_rm_comm;
      rewrite IHA with (eta := eta ^- n); auto.
Defined. 

Lemma wf_trm_subst_wf_t : 
  forall t (rho eta : assoc wf_trm),
    sub_name (ol_t t) (dom eta)
    -> ol_t (t[[ >>> rho, >>> eta]])= nil.
Proof.
  induction t; intros. 
  - simpl in H; pose proof (fn_pro_IN_dom eta n); apply IN_sublist in H; 
    rewrite fn_pro_dom_eq in H.
    pose proof (IN_dom_sig n (>>> eta) H).
    simpl; destruct H1 as [t St]; rewrite St. 
    apply wf_t_ol_empty; apply H0; auto. 
  - rewrite ol_t_ind_rho, fn_pro_nil; auto. 
  - rewrite ol_t_ind_rho, fn_pro_nil; auto. 
  - simpl; rewrite IHt1, IHt2; simpl in H; auto with datatypes.   
Defined.    


Lemma ol_wf_trm_subst : forall A (eta : assoc wf_trm), 
    sub_name (ol A) (dom eta) ->
    wf (A [nil, >>> eta]).
Proof.      
  induction A as [ [p t] | |]; simpl; intros eta Hsub.
  - apply wAtom;  auto with datatypes. 
    rewrite <- fn_pro_nil. apply empty_ol_wf_t, wf_trm_subst_wf_t; auto. 
  - apply wImply; auto with datatypes.
  - set (a := new (op (A [nil,>>> eta ^- n]))).
    apply wForall with (c := a);
      [ apply new_fresh
      | rewrite (open_wf_trm_subst); rewrite <- fn_pro_cons; apply IHA; 
        simpl; auto with datatypes]. 
Defined.

Lemma wf_trm_subst_wf: 
  forall A (rho eta : assoc wf_trm),
     sub_name (ol A) (dom eta)
    -> ol ( A [ >>> rho, >>> eta])= nil.
Proof.
  intros; rewrite ol_ind_rho; apply wf_ol_empty, ol_wf_trm_subst; auto. 
Defined.

  (** ** Universal Completeness *)

Theorem univ_cpltness : forall (A:fml) (Ga:context) (rho eta:assoc wf_trm),
    sub_name (ol A) (dom eta) -> 
    sub_name (op A) (dom rho)->
    wf_c Ga ->
    Ga ||- A {[rho, eta]} ->
    Ga |- (A [>>> rho, >>> eta])

    with univ_cpltness_stoup : forall (A:fml) (Ga:context) (rho eta:assoc wf_trm),
    sub_name (ol A) (dom eta) ->
    sub_name (op A) (dom rho) ->
    wf_c Ga ->
    (forall C Ga', sub_ctx Ga Ga' ->
                   (Ga' ;; (A [>>> rho, >>> eta]) |- C )-> (Ga' |- C )) ->
    Ga ||- A {[rho, eta]}.
Proof.
  - {destruct A as [ [p t] | | ]; simpl; intros.
     - rewrite <- psem_tsubst; assumption.
     - generalize (sub_appL _ _ H); intro.
       generalize (sub_appR _ _ H); intro; clear H.
       apply ProofImplyR.
       apply univ_cpltness; auto with datatypes.
       
       + apply wCons; auto.
         apply empty_ol_wf, wf_trm_subst_wf; auto with datatypes.
       + apply X; auto. 
         * unfold sub_ctx; right. split;
                                  [ idtac 
                                  | apply wCons; auto; 
                                    apply empty_ol_wf, wf_trm_subst_wf]; 
           auto with datatypes.
         * apply univ_cpltness_stoup; auto with datatypes;
            [apply wCons; auto;
             apply empty_ol_wf, wf_trm_subst_wf; auto
            | intros; apply ProofCont with  (A1 [>>> rho, >>> eta]); 
              unfold sub_ctx in H]; auto.
             destruct H; [rewrite <- H | apply H]; auto with datatypes. 
          
     - set (a:= new (op_c ((Forall n (A [>>> rho, >>> eta ^- n])) :: Ga))).
              apply ProofForallR with a; intros.
              apply new_fresh.  unfold open; rewrite open_eq_subst. 
       + rewrite <- fn_pro_cons;
         apply univ_cpltness; auto.
         * simpl; auto with datatypes.
         * apply X; apply sub_ctx_refl. 
       + apply wPar. 
          }
  - { destruct A as [ [p t] | |]; simpl; intros.
      - apply H2; auto using sub_ctx_refl. 
        rewrite psem_tsubst; auto. 
        apply ProofAxiom; auto; apply wAtom; apply wf_t_sub_ol; auto.
      - apply univ_cpltness_stoup; auto with datatypes.
        + apply sub_ctx_wf_c with Ga; auto. 
        + intros; apply H2; auto. 
          * apply wle_trans with w'; auto. 
          * { apply ProofImplyL ; auto. 
               apply univ_cpltness; auto with datatypes. 
              - apply sub_ctx_wf_c with Ga; auto. apply sub_ctx_trans with w'; auto.  
              - apply mono_force with w'; auto.
}
      - apply univ_cpltness_stoup; auto. apply sub_rm_2; auto.
       * apply sub_ctx_wf_c with Ga; auto. 
       * intros; apply H2; auto. 
        + apply wle_trans with w'; auto.
        + destruct d as [m wf]; apply ProofForallL with m; auto. 
          unfold open; rewrite open_eq_subst; auto. 
}
Defined.


Notation cl_a := (fun (A: fml) => sub_name (op A) nil).

Notation cl_c :=
  (fun (Ga:context) => forall A, IN_ctx A Ga -> sub_name (op A) nil).

Theorem univ_cpltness' : 
  forall A (Ga: context),
    cl_a A ->
    wf A -> wf_c Ga ->
    Ga ||- A {[nil, nil]} ->
    Ga |- A.
Proof.
  intros; rewrite nil_subst. 
  rewrite <- fn_pro_nil; apply univ_cpltness; auto; 
  rewrite wf_ol_empty; auto with datatypes.
Defined.

Theorem univ_cpltness_stoup' : forall A (Ga: context),
    cl_a A ->
    wf A -> wf_c Ga ->
    (forall C Ga', sub_ctx Ga Ga' -> Ga' ;; A |- C -> Ga' |- C) ->
    Ga ||- A {[nil, nil]}.
Proof. 
  intros.
  apply univ_cpltness_stoup; auto;
  [ rewrite wf_ol_empty; auto with datatypes
  | intros; apply H2; auto; rewrite nil_subst with A; rewrite <- fn_pro_nil; auto].
Defined.

Lemma univ_cpltness_axiom : forall A (Ga : context),
    cl_a A -> wf A -> wf_c Ga ->
    IN_ctx A Ga ->
    Ga ||- A {[nil, nil]}.
Proof.
  induction Ga as [ | B Ga]; try contradiction; simpl; intros. 
  apply univ_cpltness_stoup; auto. 
  - rewrite wf_ol_empty; auto. 
  - intros. apply ProofCont with (A [>>> nil, >>> nil]) ; auto. 
    rewrite fn_pro_nil; rewrite <- nil_subst. destruct H3; subst; intuition. 
Defined. 

Lemma universal_force_context : forall (Ga: worlds Universal) De,
    cl_c De -> wf_c De ->
    sub_ctx De Ga -> 
    list_forall (fun B => Ga ||- B {[nil, nil]}) De.
Proof.
  induction De as [|A]; intros; constructor.
  - apply univ_cpltness_axiom; auto using IN_eq; auto.
    + inversion H0; subst; auto. 
    + unfold sub_ctx in H1; intuition; subst; auto. 
    + unfold sub_ctx in H1; destruct H1; subst. 
      * apply IN_eq.  
      * apply H1; auto with datatypes. 
  - apply IHDe; auto with datatypes. 
    * inversion H0; auto. 
    * unfold sub_ctx; destruct H1; subst; auto with datatypes. 
      right; destruct H1; eauto using sub_cons_1. 
Defined.

Theorem completeness : forall (Ga: context) A,
    cl_a A ->
    cl_c Ga ->
    wf A -> wf_c Ga ->
    (forall K (w: worlds K),
        (list_forall (fun B => w ||- B {[nil, nil]}) Ga) -> w ||- A {[nil, nil]}) ->
    Ga |- A.
Proof.
  intros; apply univ_cpltness'; auto. 
  apply X. apply (universal_force_context H0 H2 (sub_ctx_refl Ga)). 
Defined.

(** ** Cut-admissibility *)

Lemma cut_ad : 
  forall Ga A B,
    cl_c Ga -> cl_a B-> 
    Ga ;; A |- B -> Ga |- A -> Ga |- B.
Proof.
  intros.
  apply completeness; auto. 
  - destruct (wf_prove_stoup H1) as [H3 H4]; destruct H4; auto.
  - apply (wf_prove H2).
  - intros. apply soundness_stoup with (Ga:=Ga) (A:=A) (C:=B); auto. 
    apply soundness with Ga; auto.
Defined.