(** * Completeness of [LJT] w.r.t. Kripke Semantics *)

Set Implicit Arguments.

Require Import decidable_IN.
Require Import associations.
Require Import sublist.
Require Import language_syntax.
Require Import renaming_substitution.
Require Import fresh_cst.
Require Import LJT_and_weakening.
Require Import kripke_semantics.
Require Import soundness.

(** The completeness of [LJT] w.r.t. Kripke semantics follows
   from the Universal Completeness.

   The universal Kripke model consists of contexts as worlds,
   the sub-context relation, and the provability for atomic
   sentences, and term as the constant domain. *)

(** ** The Universal Model *)

(** Monotonicity of forcing relation *)
(* Notation context_wf := (@sig context wf_c). *)

(*
Definition sub_ctx (Ga Ga' : context) : Prop :=
  (Ga = Ga') \/( (sub_ctx_pre Ga Ga' /\ wf_c Ga')).
*)

Lemma indeed_sub_ctx_is : forall Ga Ga',
    sub_ctx Ga Ga' ->
    sub_ctx_pre Ga Ga'.
Proof.
intros.
destruct H; try rewrite H; auto; destruct H; auto.
Defined.

Notation wf_trm := (@sig trm wf_t).

Definition wf_Cst (n:name) : wf_trm := 
  exist wf_t (Cst n)(wCst n).

Definition wf_App (f:function)(t u: wf_trm) : wf_trm :=
  exist wf_t
        (App f (proj1_sig t) (proj1_sig u)) 
        (wApp f (proj2_sig t) (proj2_sig u)).

Definition wf_atoms Ga (P : predicate * wf_trm) := 
  (Ga |- Atom (fst P, proj1_sig (snd P))).

Lemma weakening_gen' : forall Ga De A eta,
    sub_ctx Ga De ->
    Ga |- A ->
    rename_c eta De |- rename eta A
                                
with weakening_stoup_gen' : forall Ga De A C eta,
    sub_ctx Ga De ->
    Ga ;; A |- C ->
    rename_c eta De ;; rename eta A |- rename eta C.
Proof.
intros.
apply weakening_gen with (Ga:=Ga); auto.
apply indeed_sub_ctx_is; auto.
destruct H; try tauto; rewrite <- H; cut(wf_c Ga /\ wf A); try tauto;
apply wf_prove; auto.
intros.
apply weakening_stoup_gen with (Ga:=Ga); auto.
apply indeed_sub_ctx_is; auto.
destruct H; try tauto; rewrite <- H; cut(wf_c Ga /\ wf A /\ wf C); try tauto.
apply wf_prove_stoup; auto.
Defined.

Hint Resolve weakening_gen' weakening_stoup_gen'.
Hint Rewrite weakening_gen' weakening_stoup_gen'.

Lemma weakening_atom : forall (Ga Ga': context),
    sub_ctx Ga Ga' ->
    forall (P : predicate * wf_trm),
    wf_atoms Ga P ->
    wf_atoms Ga' P.
Proof.
  intros.
  pose proof weakening_gen'.
  pose proof X Ga Ga' (Atom (fst P, proj1_sig (snd P))) nil H H0.
  rewrite rename_c_nil in H1.
  rewrite rename_nil in H1.
  auto.
Defined.

(** Reflexivity of sub-context relation. *)

Lemma sub_ctx_refl : forall (Ga:context), 
    sub_ctx Ga Ga.
Proof.
  unfold sub_ctx; auto.
Defined.

(** Transitivity of sub-context relation. *)

Lemma sub_ctx_trans : forall (Ga Ga0 Ga1:context), 
    sub_ctx Ga Ga0 -> sub_ctx Ga0 Ga1 -> sub_ctx Ga Ga1.
Proof.
  unfold sub_ctx.
  intros.
  destruct H, H0; try rewrite H in *; try rewrite H0 in *.
  left; auto.
  right; auto.
  right; auto.
  right; split; try tauto.
  destruct H, H0.
  eapply sub_trans; auto.
Defined.

(** Universal model's domain is the set of well-formed terms. *)

Canonical Structure Universal := @Build_Kripke
  context
  sub_ctx
  sub_ctx_refl
  sub_ctx_trans
  wf_trm
  (@wf_Cst)
  (@wf_App)
  (fun Ga P => Ga |- Atom (fst P, proj1_sig (snd P)))
  weakening_atom.

(** In the universal model, substitution plays the role of
   semantic interpretation. *)

Lemma sub_ctx_wf_c : forall Ga Ga0,
    sub_ctx Ga Ga0 -> wf_c Ga -> wf_c Ga0.
Proof.
intros.
unfold sub_ctx in H.
destruct H as [H1 | H2]; try rewrite H1 in *; tauto.
Defined.

Notation ">>" := (proj1_sig).
Notation "<<" := (exist wf_t).

Fixpoint fn_pro (eta : assoc wf_trm) :=
  match eta with
    nil => nil
  | (n, t) :: eta' => (n, >> t) :: (fn_pro eta')
  end.

Notation ">>>" := (fn_pro).

Lemma fn_pro_0 : forall eta n t u,
eta ^^ n = Some t ->
>>> eta ^^ n = Some u ->
>> t = u.
Proof.
unfold fn_pro.
induction eta, t, u; auto; simpl; intros; try inversion H.
destruct a as [m s]; destruct s.
clear H2.
simpl in H0.
destruct (n==m); try tauto.
inversion H0.
clear H.
rewrite H2 in w0.
inversion w0.
pose proof IHeta n (<< x w) (BVar n0) H H0.
simpl in H1; auto.
destruct a as [m s]; destruct s.
destruct (n==m); try tauto.
rewrite <- e in *; clear e.
simpl in H0.
inversion H.
destruct (n==n); try tauto.
inversion H0; rewrite H3 in *; auto.
simpl in H0.
destruct (n==m); try tauto.
pose proof IHeta n (<< x w) (Cst n0) H H0.
simpl in H1; auto.
destruct a.
simpl in H0.
destruct (n==n0); try tauto.
inversion H; inversion H0.
rewrite H3 in *; simpl; auto.
pose proof IHeta n (<< x w) (App f u1 u2) H H0.
simpl in H1; auto.
Defined.

Lemma fn_pro_1 : forall eta,
  dom eta = dom (>>> eta).
Proof.
induction eta; try destruct a; simpl; auto.
rewrite IHeta; auto.
Defined.

Lemma fn_pro_2 : forall t eta,
    sub_name (bv_t t) (dom eta) ->
    wf_t (t [[>>> eta]]).
Proof.
induction t; simpl; intros.
unfold sublist in H.
pose proof H n; simpl in *; case_var; try tauto; clear H.
assert (n @ dom eta); auto; clear e H0.
assert (n @ dom (>>> eta)). rewrite <- fn_pro_1; auto.
apply IN_dom_sig in H. apply IN_dom_sig in H0.
destruct H, H0.
destruct x.
rewrite e0.
assert (>>(<< x w) = x0).
apply fn_pro_0 with (eta:=eta) (n:=n); auto.
rewrite <- H; auto.
auto with datatypes.
assert (H0: sub_name (bv_t t1 ++ bv_t t2)(dom eta)); auto; 
apply sub_appL in H; apply sub_appR in H0.
apply wApp; auto.
Defined.

Lemma fn_pro_3 : 
  >>> nil = nil.
Proof.
auto.
Defined.

Lemma fn_pro_4 : forall eta x,
    wf_t x ->
    x = (x [[>>> eta]]).
Proof.
induction x; simpl; intros; auto; inversion H.
f_equal; auto.
Defined.

Lemma fn_pro_5 : forall t n x eta,
    wf_t x ->
    (t [[(n, x) :: >>> eta]]) = ((t [[(n, x) :: nil]]) [[>>> eta]]).
Proof.
induction t; simpl in *; intros; auto.
destruct (n==n0). apply fn_pro_4; auto.
simpl; auto.
f_equal; auto.
Defined.

Lemma fn_pro_6 : forall a t n x,
    wf_t x ->
    a @ bv_t (t [[(n, x) :: nil]]) ->
    a @ bv_t t.
Proof.
induction t.
intros.
destruct (n==n0).
rewrite e in *.
simpl in H0.
destruct (n0==n0); try tauto.
rewrite wf_t_bv_empty in H0; auto; destruct H0.
simpl in H0.
destruct (n==n0).
rewrite wf_t_bv_empty in H0; auto; destruct H0.
auto. intros; simpl in *; auto.
simpl in *; intros; apply IN_app_or in H0; destruct H0.
apply IN_or_app. left; eapply IHt1; eauto. 
apply IN_or_app. right; eapply IHt2; eauto. 
Defined.

Lemma subst_list_1 : forall eta t a,
    a @ bv_t (t [[>>> eta]]) ->
    a @ bv_t t.
Proof.
induction eta.
simpl.
intros.
rewrite <- nil_subst_t in H.
auto.
destruct a.
destruct s.
simpl in *.
intros.
rewrite fn_pro_5 in H; auto.
pose proof IHeta ((t [[(n, x) :: nil]])) a H.
eapply fn_pro_6; eauto.
Defined.

Lemma fn_pro_7 : forall eta n,
  ((>>> eta) ^- n) = (>>> (eta ^- n)).
Proof.
intros.
induction eta.
simpl; auto.
destruct a.
destruct s.
simpl in *.
destruct w; destruct (n==n0); try tauto; auto; rewrite IHeta; simpl in *; auto.
Defined.

Lemma subst_list_2 : forall A a eta,
    a @ bv (A [>>> eta]) ->
    a @ bv A.
Proof.
induction A; simpl; intros.
destruct a.
eapply subst_list_1; eauto.
apply IN_or_app; apply IN_app_or in H.
destruct H.
left; eapply IHA1; eauto.
right; eapply IHA2; eauto.
destruct (a==n).
rewrite e in *; clear e.
apply notIN_rm_1 in H; try tauto.
apply IN_rm_1 in H. 
pose proof IHA a (eta ^- n).
rewrite fn_pro_7 in H; auto; apply IN_rm_2; auto.
Defined.

Lemma subst_list_3 : forall eta t,
    (forall a, a @ dom eta -> a # bv_t t) ->
    t [[>>> eta]] = t.
Proof.
induction t; simpl; intros; auto.
pose proof H n.
destruct (n==n) in H0; try tauto.
clear e.
assert (n # dom eta).
try tauto.
clear H0.
rewrite fn_pro_1 in H1.
pose proof notIN_dom_None. 
pose proof H0 trm n (>>> eta) H1; clear H0 H1.
rewrite H2; auto.
rewrite IHt1, IHt2; auto; intros; pose proof H a H0; apply notIN_app_1 in H1; tauto.
Defined.

Lemma subst_list_4 : forall A eta,
    (forall a, a @ dom eta -> a # bv A) ->
    A [>>> eta] = A.
Proof.
induction A; simpl; intros; auto.
destruct a.
f_equal; f_equal; auto; apply subst_list_3; auto.
f_equal; [apply IHA1 | apply IHA2]; intros; eapply notIN_app_1 in H; eauto; tauto.
f_equal.
rewrite fn_pro_7.
apply IHA with (eta:=(eta ^- n)).
intros.
destruct (a==n).
(* rewrite e in *; apply not_in_dom in H0; tauto. *)
rewrite e in *; apply assoc_rm_dom_self in H0; tauto.
apply IN_dom_sig in H0.
destruct H0.
(* rewrite <- assoc_rm_neq in e; auto. *)
rewrite <- lookup_assoc_rm_neq in e; auto.
assert (eta ^^ a <> None). 
rewrite e; intro; inversion H0.
pose proof notIN_dom_None. 
pose proof H1 wf_trm a eta; clear H1.
destruct (decIN eqdec a (dom eta)).
pose proof H a i.
eapply notIN_rm_2; eauto.
pose proof H2 n1.
auto.
Defined.

Corollary subst_list_5 : forall A eta,
    wf A ->
    A [>>> eta] = A.
Proof.
intros A eta H; apply wf_bv_empty in H.
apply subst_list_4; rewrite H; auto.
Defined.

Lemma subst_list_6 : forall t a eta,
    a @ bv_t (t [[>>> eta]]) ->
    a # dom eta.
Proof.
induction t; simpl; intros; try tauto.
pose proof (@IN_dom_sig trm n (>>>eta)).
destruct (decIN eqdec n (dom (>>> eta)));try tauto.
pose proof H0 i.
destruct H1.
pose proof (@IN_dom_sig wf_trm n eta).
rewrite <- fn_pro_1 in i.
pose proof H1 i.
destruct H2.
destruct x0.
assert (>> (<< x0 w) = x). eapply fn_pro_0; eauto.
simpl in H2.
rewrite e in H.
rewrite wf_t_bv_empty in H; auto. rewrite <- H2 in *; auto.
rewrite fn_pro_1.
apply notIN_dom_None in n0.
rewrite n0 in H.
simpl in H.
destruct (a==n); try tauto.
rewrite e in *.
destruct (decIN eqdec n (dom (>>> eta))); try tauto.
pose proof H0 i.
destruct H1.
rewrite n0 in e0.
inversion e0.
apply IN_app_or in H.
destruct H.
apply IHt1; auto.
apply IHt2; auto.
Defined.

Lemma subst_list_7 : forall A a eta,
    a @ bv (A [>>> eta]) ->
    a # dom eta.
Proof.
induction A; simpl; intros; try tauto.
destruct a.
simpl in H.
eapply subst_list_6; eauto.
apply IN_app_or in H; destruct H; auto.
pose proof H as I.
apply IN_rm_1 in H.
apply IN_rm_neq in I.
rewrite fn_pro_7 in H.
pose proof IHA a (eta ^-n) H.
(* pose proof (@in_dom_neq_rm wf_trm eta a n I). *)
pose proof (@assoc_rm_neq_dom wf_trm eta a n I).
destruct (decIN eqdec a (dom eta)).
pose proof H1 i.
contradiction.
assumption.
Defined.

Lemma psem_tsubst : forall (t:trm) (eta:assoc wf_trm),
  sub_name (bv_t t) (dom eta) ->
  >> (psem Universal t eta) = (t [[>>>eta]]).
Proof.
  induction t; try tauto. 
  intros.
   assert (n @ dom eta).
   unfold sublist in H; simpl in H; pose proof H n; case_var; auto. clear H.
   assert (n @ dom (>>> eta)). rewrite <- fn_pro_1; auto.
   pose proof IN_dom_sig as X; pose proof X trm n (>>> eta) H; clear X.
   pose proof IN_dom_sig as X; pose proof X wf_trm n eta H0; clear X.
   destruct H1, H2. 
   assert (>> x0 = x). apply fn_pro_0 with (eta:=eta) (n:=n); auto. 
   simpl; rewrite e, e0; auto. simpl; intros.
   assert (sub_name (bv_t t1 ++ bv_t t2) (dom eta)); auto.
   apply sub_appL in H; apply sub_appR in H0.
   rewrite IHt1, IHt2; auto.
Defined.

Lemma open_eq_subst_t_1 : forall t n u,
    wf_t t ->
    (t [[(n, u) :: nil]]) = t.
Proof.
induction t; simpl; intros; auto; try inversion H; try f_equal; auto.
Defined.

Lemma open_eq_subst_t_2 : forall t eta a n,
    ((t [[>>>eta ^- n]]) [[(n, Cst a) :: nil]]) = (t [[(n, Cst a) ::(>>> eta)]]).
Proof.
induction t; simpl; intros; auto.
destruct (n==n0).
rewrite <- e in *.
rewrite assoc_rm_self; simpl; case_var; try tauto; auto.
(* rewrite <- assoc_rm_neq; auto. *)
rewrite <- lookup_assoc_rm_neq; auto.
induction eta; simpl.
destruct (n==n0); try tauto.
destruct a0.
destruct s.
simpl.
destruct (n==n2); auto.
rewrite open_eq_subst_t_1; auto.
f_equal; auto.
Defined.

Lemma open_eq_subst : forall A eta a n,
    open (A [>>>eta ^- n]) n (Cst a) = (A [(n, (Cst a)) :: (>>>eta)]).
Proof.
induction A; unfold open; simpl; intros.
destruct a; simpl.
f_equal; f_equal; auto.
rewrite <- open_eq_subst_t_2; auto.
f_equal.
apply IHA1.
apply IHA2.
destruct (n==n0).
rewrite e in *.
rewrite <- nil_subst.
(* rewrite <- rm_rm; auto. *)
rewrite <- assoc_rm_rm; auto.
pose proof IHA (eta ^- n) a n0.
unfold open in H.
(* pose proof (@rm_neq_rm trm n n0 (>>> eta) n1). *)
pose proof (@assoc_rm_neq_rm trm n n0 (>>> eta) n1).
rewrite <- fn_pro_7 in H.
rewrite <- H0 in H.
rewrite H.
auto.
Defined.

Lemma open_eq_subst_2 : forall t eta u n,
    wf_t u ->
    ((t [[>>> eta ^- n]]) [[(n, u) :: nil]]) = (t [[(n, u) :: >>> eta]]).
Proof.
induction t; simpl; intros; auto.
destruct (n==n0); try tauto.
rewrite e in *.
rewrite assoc_rm_self.
simpl.
destruct (n0==n0); try tauto.
(* rewrite <- assoc_rm_neq. *)
rewrite <- lookup_assoc_rm_neq.
destruct (decIN eqdec n (dom (>>> eta))).
pose proof i.
rewrite <- fn_pro_1 in H0.
apply IN_dom_sig in i. 
apply IN_dom_sig in H0.
destruct i.
destruct H0.
rewrite e.
destruct x0.
pose proof fn_pro_0.
assert (>>(<< x0 w) = x).
eapply fn_pro_0; eauto.
simpl in H1.
rewrite <- H1.
apply open_eq_subst_t_1; auto.
apply notIN_dom_None in n2.
rewrite n2.
simpl.
destruct (n==n0); try tauto.
assumption.
f_equal; auto.
Defined.

Lemma open_eq_subst_3 : forall A eta t n,
    wf_t t ->
    open (A [>>>eta ^- n]) n t = (A [(n, t) :: (>>>eta)]).
Proof.
induction A; simpl; intros.
destruct a; unfold open; simpl.
f_equal; f_equal.
apply open_eq_subst_2; try tauto.
unfold open.
simpl.
f_equal.
apply IHA1; auto.
apply IHA2; auto.
unfold open.
simpl.
f_equal.
destruct (n==n0); try tauto.
rewrite e in *.
(* rewrite <- rm_rm. *)
rewrite <- assoc_rm_rm.
rewrite <- nil_subst.
auto.
unfold open in IHA.
(* rewrite rm_neq_rm. *)
rewrite assoc_rm_neq_rm.
rewrite fn_pro_7.
auto. auto.
Defined.

Lemma fn_pro_8 : forall n a eta,
    (>>>((n, wf_Cst a) :: eta)) = ((n, Cst a) :: >>> eta).
Proof.
auto.
Defined.

Lemma fn_pro_9 : forall eta n u,
    >>> eta ^^ n = Some u ->
    wf_t u.
Proof.
induction eta; simpl; intros. 
inversion H.
destruct a.
destruct s.
simpl in *.
destruct (n==n0).
inversion H.
rewrite <- H1; auto.
eapply IHeta; eauto.
Defined.

Lemma fn_pro_10 : forall t n a eta,
    ((t [[(n, Cst a) :: nil]]) [[>>> eta]]) =
    ((t [[>>> eta ^- n]]) [[(n, Cst a) :: nil]]).
Proof.
induction t; simpl; intros; auto.
destruct (n==n0); try tauto.
rewrite <- e in *; clear e; simpl.
rewrite assoc_rm_self; simpl.
destruct (n==n); try tauto.
simpl. 
(* rewrite <- assoc_rm_neq. *)
rewrite <- lookup_assoc_rm_neq.
pose proof fn_pro_9 eta n.
destruct (decIN eqdec n (dom (>>> eta))).
pose proof (@IN_dom_sig trm n (>>> eta) i).
destruct H0.
rewrite e.
apply H in e.
rewrite open_eq_subst_t_1; auto.
apply notIN_dom_None in n2.
rewrite n2.
simpl.
destruct (n==n0); try tauto. auto.
f_equal.
rewrite IHt1; auto.
rewrite IHt2; auto.
Defined.

Lemma subst_eq_1 : forall A n a eta,
    ((A [(n, Cst a) :: nil]) [>>> eta]) = ((A [>>> eta ^- n]) [(n, Cst a) :: nil]).
Proof.
induction A; simpl; intros; auto. 
destruct a.
simpl.
f_equal.
f_equal.
simpl.
rewrite fn_pro_10; auto.
f_equal; auto.
f_equal; auto.
destruct (n==n0); try tauto.
rewrite <- e in *; clear e.
rewrite <- nil_subst.
rewrite <- nil_subst.
(* rewrite <- rm_rm. *)
rewrite <- assoc_rm_rm.
auto.
pose proof IHA n0 a (eta ^- n).
(* rewrite rm_neq_rm; auto. *)
rewrite assoc_rm_neq_rm; auto.
rewrite fn_pro_7.
rewrite <- H; auto.
Defined.

Lemma subst_list_8 : forall A eta,
    sub_name (bv A) (dom eta) ->
    wf (A [>>> eta]).
Proof.
intros; apply empty_bv_wf.
pose proof subst_list_7 A.
pose proof subst_list_2 A.
unfold sublist in H.
apply (@sub_nil name eqdec).
intro; intro.
pose proof H0 a eta H2.
pose proof H1 a eta H2.
pose proof H a H4.
contradiction.
Defined.

(** ** Universal Completeness *)

Theorem univ_cpltness : forall (A:fml) (Ga:context) (eta:assoc wf_trm),
    sub_name (bv A) (dom eta) ->
    wf_c Ga ->
    Ga ||- A {[eta]} ->
    Ga |- (A [>>> eta])

with univ_cpltness_stoup : forall (A:fml) (Ga:context) (eta:assoc wf_trm),
    sub_name (bv A) (dom eta) ->
    wf_c Ga ->
    (forall C Ga', sub_ctx Ga Ga' -> (Ga' ;; (A [>>> eta]) |- C )-> (Ga' |- C )) ->
    Ga ||- A {[eta]}.
Proof.
  destruct A as [ [p t] | | ]; simpl; intros.

    rewrite <- psem_tsubst; try assumption. 
  
    assert (I1 : sub_name (bv A1) (dom eta)). 
     apply sub_appL with (m:=bv A2); try assumption.
    assert (I2 : sub_name (bv A2) (dom eta)).
     apply sub_appR with (l:=bv A1); try assumption. clear H.
    assert (J1 : wf_c ((A1 [>>>eta]) :: Ga)). 
     apply wCons; try apply subst_list_8; try assumption.
    assert (K : sub_ctx Ga ((A1 [>>> eta]) :: Ga)); unfold sub_ctx. right.
     split; try assumption; intro; intro; simpl.
     destruct (fml_dec a (A1 [>>> eta])); try apply I; try assumption.
    apply ProofImplyR.
    apply univ_cpltness; try assumption.
    apply X; try assumption.
    apply univ_cpltness_stoup; try assumption; intros.
    apply ProofCont with (A:=(A1[>>>eta])); try assumption.
    apply indeed_sub_ctx_is in H; pose proof H (A1 [>>> eta]) as L;
    apply L; apply IN_eq.

    set (a:= new (oc_c ((A[>>> eta ^- n]) :: Ga))).
    assert (new : a # oc_c ((A [>>> eta ^- n]) :: Ga)). apply new_fresh.
    pose proof (@ProofForallR n (A [>>> eta ^- n]) Ga a new) as I.
    apply I; clear I.
    assert (J : sub_name (bv A) (dom ((n, wf_Cst a) :: eta))). intro; intro.
     simpl; destruct (a0==n); try apply I.
     apply H. apply IN_rm_2; try assumption.
    pose proof univ_cpltness A Ga ((n, wf_Cst a) :: eta) J H0 as K.
    rewrite open_eq_subst. 
    rewrite <- fn_pro_8.
    apply K.
    apply X.
    apply sub_ctx_refl.
   
  destruct A as [ [p t] | | ]; simpl; intros. 

    assert (I : wf (Atom (p, t [[>>> eta]]))); 
     try apply wAtom; try apply fn_pro_2; try assumption.
    apply H1; try apply wle_refl; try rewrite psem_tsubst; 
    try apply ProofAxiom; try assumption.
 
    assert (I1 : sub_name (bv A1) (dom eta)). 
     apply sub_appL with (m:=bv A2); try assumption.
    assert (I2 : sub_name (bv A2) (dom eta)).
     apply sub_appR with (l:=bv A1); try assumption. clear H.
    assert (J : wf_c w'). unfold sub_ctx in H2. destruct H2.
     rewrite <- H; try assumption. apply H.    
    apply univ_cpltness_stoup; try assumption; intros.
    assert (K : sub_ctx Ga Ga'); try apply wle_trans with (w':=w'); try assumption.
    assert (L : wf_c Ga'). unfold sub_ctx in K. 
     destruct K as [K1 | K2]; try apply K2; try rewrite <- K1; try assumption.
    apply H1; try assumption.
    apply ProofImplyL; try assumption.
    apply univ_cpltness; try assumption.
    apply mono_force with (w:=w'); try assumption.

    apply univ_cpltness_stoup.
    apply sub_rm_2; try assumption.
    apply sub_ctx_wf_c with (Ga:=Ga); try assumption.
    intros.
    apply H1.
    apply wle_trans with (w':=w'); try assumption.
    destruct d as [u h].
    pose proof @ProofForallL Ga' C n u (A [>>> eta ^- n]) h.
    apply H5.
    simpl in H4.
    rewrite open_eq_subst_3; auto.
Defined.

Lemma subst_list_9 : forall Ga eta,
    sub_name (bv_c Ga) (dom eta) ->
    wf_c (Ga [!>>> eta!]).
Proof.
induction Ga; simpl; intros; try apply wNil; try apply wCons.
apply IHGa.
eapply sub_appR; eauto.
apply subst_list_8; eapply sub_appL; eauto.
Defined.

Lemma subst_list_10 : forall Ga eta,
    wf_c Ga ->
    Ga [!>>> eta!] = Ga.
Proof.
induction Ga; simpl; intros; auto.
inversion H; rewrite IHGa; try assumption.
rewrite subst_list_5; try assumption.
reflexivity.
Defined.


Theorem univ_cpltness_2 : forall (A:fml) (Ga:context) (eta eta':assoc wf_trm), 
    sub_name (bv A) (dom eta)->
    sub_name (bv_c Ga) (dom eta')->
    Ga[!>>>eta'!] ||- A {[eta]}->
    Ga[!>>>eta'!] |- (A [>>>eta])
with univ_cpltness_stoup_2 : forall (A:fml) (Ga:context) (eta eta' :assoc wf_trm), 
    sub_name (bv A) (dom eta)->
    sub_name (bv_c Ga) (dom eta')->
    (forall C Ga', sub_ctx (Ga[!>>> eta'!]) Ga' ->
                   (Ga' ;; (A[>>>eta]) |- C)->
                   (Ga' |- C))-> 
    Ga[!>>>eta'!] ||- A {[eta]}.
Proof.       
  destruct A as [ [p t] | | ]; simpl; intros. 

    rewrite <- psem_tsubst; try assumption.

    assert (I1 : sub_name (bv A1) (dom eta)).
    eapply sub_appL; eauto.
    assert (I2 : sub_name (bv A2) (dom eta)). 
    eapply sub_appR; eauto.
    assert (J : wf_c ((A1 [>>> eta]) :: (Ga [!>>> eta'!])));
    try apply wCons; try apply subst_list_8; try apply subst_list_9; try assumption.
    apply ProofImplyR. 
    apply univ_cpltness; try assumption.
    apply X; try assumption ;
    unfold sub_ctx; try right; try split; try assumption; try apply sub_cons_2.
    apply univ_cpltness_stoup; try assumption.
    intros.
    apply (@ProofCont (A1 [>>> eta])); apply indeed_sub_ctx_is in H1.
    apply H1; apply IN_eq.
    try assumption.

    set (a:= new (oc_c ((A[>>> eta ^- n]) :: (Ga[!>>> eta'!])))).
    assert (I : a # (oc_c ((A[>>> eta ^- n]) :: (Ga[!>>> eta'!])))). apply new_fresh.
    assert (J : sub_name (bv A) (dom ((n, wf_Cst a) :: eta))).
     simpl; try apply app_sub; apply sub_rm_2; try assumption.
    apply (@ProofForallR n (A [>>> eta ^-n]) (Ga [!>>> eta'!]) a I). 
    rewrite open_eq_subst; rewrite <- fn_pro_8.
    apply univ_cpltness_2; try assumption.
    apply X; apply sub_ctx_refl.

  destruct A as [ [p t] | | ]; simpl; intros. 

    rewrite psem_tsubst; try assumption.
    apply H1; try apply sub_ctx_refl.
    apply ProofAxiom.
    apply subst_list_9; try assumption.
    apply wAtom; apply fn_pro_2; try assumption.

    eapply univ_cpltness_stoup; eauto.
    eapply sub_appR;            eauto.
    eapply sub_ctx_wf_c;        eauto.
    eapply subst_list_9;        eauto.
    intros.
    eapply H1;                  eauto.
    eapply sub_ctx_trans;       eauto.
    eapply ProofImplyL;         eauto.
    eapply univ_cpltness;       eauto.
    eapply sub_appL;            eauto.
    eapply sub_ctx_wf_c;        eauto.
    eapply sub_ctx_wf_c;        eauto.
    eapply subst_list_9;        eauto.
    eapply mono_force;          eauto.

    apply univ_cpltness_stoup.
    simpl; apply sub_rm_2; try assumption.
    eapply sub_ctx_wf_c; eauto.
    apply subst_list_9; auto.
    intros.    
    apply H1.
    eapply sub_ctx_trans; eauto.
    destruct d as [u h].
    eapply ProofForallL; eauto.
    simpl in H4.
    rewrite open_eq_subst_3; auto.
Defined.


(** ** Completeness for _closed_ formulae *)

(** Remark:

   - Because we don't consider parameters, every term/formula are closed. *)

Theorem univ_cpltness' : forall A Ga,
    wf A -> wf_c Ga ->
    Ga ||- A {[nil]} ->
    Ga |- A.
Proof.
intros.
pose proof @univ_cpltness A Ga nil.
rewrite wf_bv_empty in X0; try assumption.
assert (I : A = (A [>>> nil])); simpl; try apply nil_subst.
rewrite <- I in X0; clear I.
apply X0; try tauto.
apply nil_sub.
Defined.

Theorem univ_cpltness_stoup' : forall A Ga,
    wf A -> wf_c Ga ->
    (forall C Ga', sub_ctx Ga Ga' -> Ga' ;; A |- C -> Ga' |- C) ->
    Ga ||- A {[nil]}.
Proof. 
  intros.
  apply univ_cpltness_stoup; try assumption.
  rewrite wf_bv_empty; try assumption; try apply nil_sub.
  intros.
  apply H1; try assumption.
  assert (I : A = (A [>>> nil])); simpl; try apply nil_subst.
  rewrite I.
  auto.
Defined.

Lemma univ_cpltness_axiom : forall A Ga,
    wf A -> wf_c Ga ->
    IN_ctx A Ga ->
    Ga ||- A {[nil]}.
Proof.
  induction Ga.
  intros A1 H1 H2. try elim H2.
  intros.
  destruct (fml_dec a A); subst.
  apply univ_cpltness_stoup'; auto; intros.
  eapply ProofCont; eauto.
  unfold sub_ctx in H2. destruct H2.
  rewrite <- H2; apply IN_eq.
  apply H2; apply IN_eq.
  apply mono_force with Ga.
  change (sub_ctx Ga (a :: Ga)).
  unfold sub_ctx; right; split; try apply sub_cons_2; auto.
  apply IHGa; auto.
  inversion H0; auto.
  eapply neq_IN_cons; eauto.
Defined. 

Lemma universal_force_context : forall (Ga: worlds Universal) De,
    wf_c De ->
    sub_ctx De Ga -> 
    list_forall (fun B => Ga ||- B {[nil]}) De.
Proof.
  induction De as [|A]; intros; constructor;
    [ apply univ_cpltness_axiom; auto using IN_eq
      | apply IHDe; eauto using sub_cons_1;
        intros; auto using IN_cons
    ].
    inversion H; auto; unfold sub_ctx in H0;
    destruct H0; subst; try tauto; try apply IN_eq.
    unfold sub_ctx in H0; destruct H0; subst; try tauto.
    unfold sub_ctx in H0; destruct H0; subst; try apply IN_eq; try tauto;
    destruct H0. apply H0; try apply IN_eq.
    eapply wle_trans; eauto.
    change (sub_ctx De (A :: De)).
    unfold sub_ctx; right; split; try assumption; eapply sub_cons_1; eauto.
Defined.

Theorem completeness : forall Ga A,
    wf A -> wf_c Ga ->
    (forall K (w: worlds K),
        (list_forall (fun B => w ||- B {[nil]}) Ga) -> w ||- A {[nil]}) ->
    Ga |- A.
Proof.
  intros; apply univ_cpltness'; try assumption;
  apply X; apply universal_force_context with (Ga:=Ga)(De:=Ga); auto; 
  try apply wle_refl.
Defined.

(** ** Cut-admissibility *)

Lemma cut_ad : forall Ga A B,
    Ga ;; A |- B -> Ga |- A -> Ga |- B.
Proof.
  intros.
  pose proof @wf_prove_stoup Ga A B H; destruct H1; destruct H2.
  apply completeness; try assumption.
  intros.
  pose proof @soundness Ga A H0 K w X.
  pose proof @soundness_stoup Ga A B H K w X X0.
  auto.
Defined.
