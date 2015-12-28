(** * Soundness of LJT w.r.t. Kripke Semantics *)

Set Implicit Arguments.

Require Import decidable_IN.
Require Import associations.
Require Import sublist.
Require Import language_syntax.
Require Import renaming_substitution.
Require Import fresh_cst.
Require Import LJT_and_weakening.
Require Import kripke_semantics.

(** The soundness of [LJT] with respect to Kripke semantics
   is relatively simple.

   If we had included parameters (free variables), the soundness
   proof of [LJT] would be a simple simultaneous induction
   on the derivation, cf. with_FreeVar_soundness.v.

   However, because we use constants instead, the case
   [ProofForallR] requires more attention. *) 

(** ** Some auxiliary predicates and operations *)

(** A predicate checking that a property holds for all elements
   of a list. *)

Inductive list_forall (A:Type)(P:A -> Type) : list A -> Type :=
| ForallNil  : list_forall P nil
| ForallCons : forall a l, 
               P a -> list_forall P l -> list_forall P (cons a l).

Definition force_ctx K (w:worlds K) eta Ga :=
  list_forall (fun B : fml => w ||- B {[eta]}) Ga.

Lemma force_IN_ctx : forall K (w:worlds K) eta Ga,
  force_ctx K w eta Ga ->
  forall A,
    IN_ctx A Ga ->
    w ||- A {[eta]}.
Proof.
  induction 1 as [ | B]; simpl; intros A; [ intro Hnil; elim Hnil | intro Hcons ].
  destruct (fml_dec A B); subst; auto.
Qed.

Lemma list_force_assoc_equiv : forall Ga K (w:worlds K) eta eta0,
  wf_c Ga ->
  list_forall (fun B : fml => w ||- B {[eta]}) Ga ->
  list_forall (fun B : fml => w ||- B {[eta0]}) Ga.
Proof.
  induction Ga; constructor; intros.
  apply force_formula_assoc_indep with eta.
  inversion H; assumption. inversion X; assumption.
  apply IHGa with eta.
  inversion H; assumption.
  inversion X; apply wCons with (A:=a) in H; try assumption.
  inversion H; assumption.
Defined.

(** Forcing is monotone wrt. the world relation. *)

Lemma mono_force_ctx : forall K (w w':worlds K),
  w <= w' -> 
  forall eta (Ga:context), 
    force_ctx K w eta Ga ->
    force_ctx K w' eta Ga.
Proof.
  induction 2 as [| B]; constructor; eauto using mono_force.
Qed.

(** ** Creation of a new Kripke model *)

Section Creation_new_Kripke.

(** This section reflects the fact that fresh constants are
   as good as fresh parameters.

   - Syntactically, this fact is represented by the renaming lemma.

   - At the semantic level, this corresponds to creating a new Kripke
     model from a given one such that the semantics remains
     nearly identical.

   - The following section is not necessary when we had introduced
     parameters. *)

  Variable K : Kripke.

(** Given an arbitrary association for constants, we construct
   a new Kripke model which differs only for a specific constant. *)

  Definition Kripke_new_csts (f : name -> domain K) : Kripke
    := @Build_Kripke (worlds K) (wle K) (wle_refl K) (wle_trans K)
    (domain K) f (funs K) (atoms K) (atoms_mon K).

(** [csts_up] creates a new association for constants using a specific
   value for a specific contant. *)

  Definition csts_up (f:name -> domain K) (n:name) (d:domain K) :
    name -> domain K
    := (fun m => if eqdec m n then d else f m).

(** If [c] is a fresh constant for a class of formulae, then
   the new Kripke model has the same interpretation as before
   w.r.t. the class.

   For technical reason, we need to exclude the case [c=0],
   Note its special role in the definition of forcing. *)

  Lemma fresh_csts_psem : forall (t:trm) (c:name) (eta:assoc (domain K)),
    c # (oc_t t) ->
    sub_name (bv_t t) (dom eta) ->
    forall (d:domain K),
      psem K t eta = psem (Kripke_new_csts (csts_up (csts K) c d)) t eta.
  Proof.
    unfold csts_up; induction t; simpl; intros.
    destruct (IN_dom_sig n eta (H0 n (IN_eq eqdec n nil))) as [d' Hd'].
    rewrite Hd' in *.
    auto.
    repeat case_var; intuition.
    generalize (sub_appL _ _ H0); intro.
    generalize (sub_appR _ _ H0); intro.
    destruct_notin; f_equal; eauto.
  Defined.

  Lemma fresh_csts_forceL : forall (A:fml) (c:name) (eta:assoc (domain K)),
    c # oc A ->
    sub_name (bv A) (dom eta) ->
    forall (w:worlds K) (d:domain K),
      force K w A eta ->
      force (Kripke_new_csts (csts_up (csts K) c d)) w A eta

    with fresh_csts_forceR : forall (A:fml) (c:name) (eta:assoc (domain K)),
      c # oc A ->
      sub_name (bv A) (dom eta) ->
      forall (w:worlds K) (d:domain K),
        force (Kripke_new_csts (csts_up (csts K) c d)) w A eta ->
        force K w A eta.
  Proof.
    * destruct A as [ [p t] | | ]; simpl; intros.
      - rewrite <- fresh_csts_psem; assumption. 
      - generalize (sub_appL _ _ H0); intro.
        generalize (sub_appR _ _ H0); intro.
        destruct_notin; eauto.
      - assert (sub_name (bv A) (dom ((n,d0)::eta))).
        + apply sub_rm_2; auto.
        + apply fresh_csts_forceL; auto.
    * destruct A as [ [p t] | | ]; simpl; intros.
      - rewrite <- fresh_csts_psem in X; assumption.
      - generalize (sub_appL _ _ H0); intro.
        generalize (sub_appR _ _ H0); intro.
        destruct_notin; eauto.
      - assert (sub_name (bv A)(dom ((n,d0)::eta))).
        + apply sub_rm_2; auto.
        + apply fresh_csts_forceR with (c:=c)(d:=d0); eauto.
  Defined.

  Lemma fresh_csts_force_ctx : forall (Ga:context) (c:name),
    c # oc_c Ga ->
    wf_c Ga ->
    forall (w:worlds K) (eta:assoc (domain K)) (d:domain K),
      force_ctx K w eta Ga ->
      force_ctx (Kripke_new_csts (csts_up (csts K) c d)) w eta Ga.
  Proof.
    - induction Ga as [ | A]; simpl; intros.
      + apply ForallNil.
      + destruct_notin; apply ForallCons; inversion X; try assumption.
        apply fresh_csts_forceL; try assumption.
        inversion H0.
        rewrite wf_bv_empty; auto with datatypes.
        apply IHGa; auto with datatypes.
        inversion H0; assumption.
  Defined.

End Creation_new_Kripke.

(** ** Soundness *)

Lemma subst_t_eq_notIN : forall y u t,
    y # bv_t t -> t [[(y,u)::nil]] = t.
Proof.
  induction t; simpl; intros.
  case_var; auto; case_var; try tauto; auto.
  auto.
  destruct_notin.
  rewrite IHt1, IHt2; auto.
Defined.

Lemma subst_eq_notIN : forall B y u,
    y # bv B -> (B[(y,u)::nil]=B).
Proof.
  induction B; simpl; intros; auto.
  destruct a.
  rewrite subst_t_eq_notIN; auto.
  destruct_notin; rewrite IHB1, IHB2; auto.
  case_var; auto.
  rewrite nil_subst; auto.
  rewrite IHB; auto.  
  apply notIN_rm_2 with n; auto.
Defined.

Lemma IN_subst_wf_t : forall t y u,
    y @ bv_t t ->
    bv_t (t [[(y,u)::nil]])=nil ->
    wf_t u.
Proof.
  induction t; simpl; intros.
  repeat case_var; auto with datatypes; tauto. tauto.
  apply IN_app_or in H.
  apply app_eq_nil in H0; destruct H0.
  destruct H.
  apply IHt1 with (y:=y); auto.
  apply IHt2 with (y:=y); auto.
Defined.

Lemma notIN_rm_eq : forall n l,
    n # l -> remove eqdec n l = l.
Proof.
  induction l; simpl; intros; auto.
  case_var; simpl; intros; auto; try tauto.
  rewrite IHl; auto.
Defined. 

Lemma IN_open_0 : forall n y B u,
    n <> y -> n @ bv (B [(y, u) :: nil]) -> n # bv_t u ->
    n @ bv B.
Proof.    
  induction B.
  intros.
  destruct a.
  simpl in *.
  induction t.
  simpl in *.
  case_var; try tauto.
  case_var; try tauto.
  simpl in *.
  case_var; try tauto.
  simpl in *; try tauto.
  simpl in *.
  apply IN_or_app.
  apply IN_app_or in H0.
  destruct H0.
  left; apply IHt1; auto.
  right; apply IHt2; auto.
  simpl in *; intros.
  apply IN_or_app.
  apply IN_app_or in H0.
  destruct H0.
  left; apply IHB1 with u; auto.
  right; apply IHB2 with u; auto.
  simpl in *; intros.
  case_var.
  rewrite <- nil_subst in H0; auto.
  destruct (n==n0).
  rewrite e in *.
  apply notIN_rm_1 in H0; try tauto.
  apply IN_rm_2; auto.
  apply IHB with u; auto.
  apply IN_rm_1 with n0; auto.
Defined.

Hint Rewrite notIN_rm_eq IN_open_0. 
Hint Resolve notIN_rm_eq IN_open_0.

Lemma IN_subst_wf_tt : forall t y eta,
    y @ bv_t t ->
    y @ dom eta ->
    bv_t (t[[eta]])=nil ->
    wf_t ((BVar y) [[eta]]).
Proof.
induction t; intros; simpl in H, H1; try tauto.
case_var; try tauto; auto with datatypes.
apply IN_app_or in H; apply app_eq_nil in H1; destruct H1, H.
apply IHt1; auto. apply IHt2; auto.
Defined.

Hint Resolve IN_subst_wf_t subst_eq_notIN subst_t_eq_notIN.
Hint Rewrite subst_eq_notIN subst_t_eq_notIN.

Theorem soundness : forall Ga A,
  Ga |- A ->
    forall K (w:worlds K),
      list_forall (fun B => w ||- B {[nil]}) Ga ->
      w ||- A {[nil]}

with soundness_stoup : forall Ga A C,
  Ga ;; A |- C ->
    forall K (w:worlds K),
      list_forall (fun B => w ||- B {[nil]}) Ga ->
      w ||- A {[nil]}
      -> w ||- C {[nil]}.
Proof.

  (* soundness *)

  - destruct 1; simpl; intros.

    + apply soundness_stoup with (Ga:=Ga)(A:=A); eauto using force_IN_ctx.

    + apply soundness with (Ga:=B::Ga); auto; 
      apply ForallCons; auto; apply mono_force_ctx with (w:=w); assumption.

    + set (K' := Kripke_new_csts K (csts_up K (csts K) a d)).
      assert (K'= Kripke_new_csts K (csts_up K (csts K) a d)).
      auto.
      assert (d = psem K' (Cst a) nil).
      simpl; unfold csts_up; simpl; case_var; intuition congruence.
      rewrite H1.
      simpl in n; destruct_notin.
      apply fresh_csts_forceR with (c:=a)(d:=d); auto.
      apply wf_prove in H.
      destruct H.
      simpl.
      apply forall_wf_sub.
      apply wf_bv_empty in H4.
      apply empty_bv_wf.
      apply sub_nil with eqdec.
      rewrite <- H4.
      apply sub_q_open.
      apply subst_force with (K:=K'); simpl; auto with datatypes.
      apply soundness with (K:=K')(Ga:=Ga); auto.
      apply fresh_csts_force_ctx; auto.
      apply wf_prove in H; destruct H; assumption.
      apply mono_force_ctx with (w:=w); auto.

  (* soundness_stoup *)

  - destruct 1; simpl; intros.

    + assumption.

    + apply soundness_stoup with (Ga:=Ga)(A:=C); auto; apply X0. 
      apply wle_refl.
      apply soundness with Ga; auto.

    + apply soundness_stoup with (Ga:=Ga)(A:=B[(y,u)::nil]); auto.
      pose proof decIN eqdec y (bv B).
      destruct H0.
      apply force_assoc_equiv with (m:=nil)(eta:=(y, psem K u nil)::nil); auto.
      apply wf_prove_stoup in H; destruct H; destruct H0.
      apply wf_bv_empty in H0.
      unfold open in H0; rewrite H0; auto.
      apply force_subst with (eta:=(y, psem K u nil) :: nil).
      apply wf_prove_stoup in H; destruct H; destruct H0.
      apply wf_bv_empty in H0.
      unfold open in H0.
      assumption.
      assert (w0<=w0). apply wle_refl.
      pose proof X0 w0 X1 (psem K u ((y, psem K u nil) ::nil)).
      apply force_st_assoc_equiv 
      with (eta:=(y, psem K u ((y, psem K u nil) :: nil)) :: nil); auto.
      rewrite subst_eq_notIN; auto.
      assert (w0<=w0). apply wle_refl.
      set (d:= csts K 0).
      pose proof X0 w0 X1 d.
      apply force_assoc_equiv with (m:= bv B)(eta:=(y,d)::nil); auto.
      intro; intros; simpl.
      case_var; try tauto.
Defined.

